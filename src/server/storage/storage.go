package storage

import (
	"context"
	"io"
	"time"
)

// ObjectStorage defines the interface for file storage operations.
type ObjectStorage interface {
	Upload(ctx context.Context, key string, reader io.Reader, contentType string) error
	PresignedURL(ctx context.Context, key string, expiry time.Duration) (string, error)
	Ping(ctx context.Context) error
}
