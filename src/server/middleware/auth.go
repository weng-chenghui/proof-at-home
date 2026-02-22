package middleware

import (
	"context"
	"crypto/rsa"
	"encoding/base64"
	"encoding/json"
	"fmt"
	"log/slog"
	"math/big"
	"net/http"
	"strings"
	"sync"
	"time"

	"github.com/golang-jwt/jwt/v5"
)

type contextKey string

const (
	UserSubKey      contextKey = "user_sub"
	UserEmailKey    contextKey = "user_email"
	UserNicknameKey contextKey = "user_nickname"
)

type AuthConfig struct {
	Issuer   string
	Audience string
}

type jwksCache struct {
	mu      sync.RWMutex
	keys    map[string]*rsa.PublicKey
	fetched time.Time
	ttl     time.Duration
	jwksURL string
}

func newJWKSCache(issuer string, ttl time.Duration) *jwksCache {
	jwksURL := strings.TrimSuffix(issuer, "/") + "/.well-known/jwks.json"
	return &jwksCache{
		keys:    make(map[string]*rsa.PublicKey),
		ttl:     ttl,
		jwksURL: jwksURL,
	}
}

type jwksResponse struct {
	Keys []jwkKey `json:"keys"`
}

type jwkKey struct {
	Kty string `json:"kty"`
	Kid string `json:"kid"`
	Use string `json:"use"`
	N   string `json:"n"`
	E   string `json:"e"`
}

func (c *jwksCache) getKey(kid string) (*rsa.PublicKey, error) {
	c.mu.RLock()
	if time.Since(c.fetched) < c.ttl {
		if key, ok := c.keys[kid]; ok {
			c.mu.RUnlock()
			return key, nil
		}
	}
	c.mu.RUnlock()

	// Fetch fresh keys
	if err := c.refresh(); err != nil {
		return nil, err
	}

	c.mu.RLock()
	defer c.mu.RUnlock()
	key, ok := c.keys[kid]
	if !ok {
		return nil, fmt.Errorf("key %s not found in JWKS", kid)
	}
	return key, nil
}

func (c *jwksCache) refresh() error {
	c.mu.Lock()
	defer c.mu.Unlock()

	// Double-check after acquiring write lock
	if time.Since(c.fetched) < c.ttl {
		return nil
	}

	client := &http.Client{Timeout: 10 * time.Second}
	resp, err := client.Get(c.jwksURL)
	if err != nil {
		return fmt.Errorf("fetching JWKS: %w", err)
	}
	defer resp.Body.Close()

	if resp.StatusCode != http.StatusOK {
		return fmt.Errorf("JWKS endpoint returned %d", resp.StatusCode)
	}

	var jwks jwksResponse
	if err := json.NewDecoder(resp.Body).Decode(&jwks); err != nil {
		return fmt.Errorf("decoding JWKS: %w", err)
	}

	newKeys := make(map[string]*rsa.PublicKey)
	for _, k := range jwks.Keys {
		if k.Kty != "RSA" || k.Use != "sig" {
			continue
		}
		key, err := parseRSAPublicKey(k)
		if err != nil {
			slog.Warn("Failed to parse JWKS key", "kid", k.Kid, "error", err)
			continue
		}
		newKeys[k.Kid] = key
	}

	c.keys = newKeys
	c.fetched = time.Now()
	slog.Debug("JWKS keys refreshed", "count", len(newKeys))
	return nil
}

func parseRSAPublicKey(k jwkKey) (*rsa.PublicKey, error) {
	nBytes, err := base64.RawURLEncoding.DecodeString(k.N)
	if err != nil {
		return nil, fmt.Errorf("decoding N: %w", err)
	}
	eBytes, err := base64.RawURLEncoding.DecodeString(k.E)
	if err != nil {
		return nil, fmt.Errorf("decoding E: %w", err)
	}

	n := new(big.Int).SetBytes(nBytes)
	e := new(big.Int).SetBytes(eBytes)

	return &rsa.PublicKey{
		N: n,
		E: int(e.Int64()),
	}, nil
}

// RequireAuth returns middleware that validates JWT Bearer tokens.
func RequireAuth(cfg AuthConfig) func(http.Handler) http.Handler {
	cache := newJWKSCache(cfg.Issuer, 15*time.Minute)

	return func(next http.Handler) http.Handler {
		return http.HandlerFunc(func(w http.ResponseWriter, r *http.Request) {
			authHeader := r.Header.Get("Authorization")
			if authHeader == "" || !strings.HasPrefix(authHeader, "Bearer ") {
				http.Error(w, `{"error":"missing or invalid authorization header"}`, http.StatusUnauthorized)
				return
			}

			tokenString := strings.TrimPrefix(authHeader, "Bearer ")

			token, err := jwt.Parse(tokenString, func(token *jwt.Token) (interface{}, error) {
				if _, ok := token.Method.(*jwt.SigningMethodRSA); !ok {
					return nil, fmt.Errorf("unexpected signing method: %v", token.Header["alg"])
				}

				kid, ok := token.Header["kid"].(string)
				if !ok {
					return nil, fmt.Errorf("missing kid in token header")
				}

				return cache.getKey(kid)
			},
				jwt.WithIssuer(cfg.Issuer),
				jwt.WithAudience(cfg.Audience),
			)

			if err != nil || !token.Valid {
				slog.Debug("JWT validation failed", "error", err)
				http.Error(w, `{"error":"invalid token"}`, http.StatusUnauthorized)
				return
			}

			claims, ok := token.Claims.(jwt.MapClaims)
			if !ok {
				http.Error(w, `{"error":"invalid claims"}`, http.StatusUnauthorized)
				return
			}

			// Extract user info into context
			ctx := r.Context()
			if sub, ok := claims["sub"].(string); ok {
				ctx = context.WithValue(ctx, UserSubKey, sub)
			}
			if email, ok := claims["email"].(string); ok {
				ctx = context.WithValue(ctx, UserEmailKey, email)
			}
			if nickname, ok := claims["nickname"].(string); ok {
				ctx = context.WithValue(ctx, UserNicknameKey, nickname)
			}

			next.ServeHTTP(w, r.WithContext(ctx))
		})
	}
}
