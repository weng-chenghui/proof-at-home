package storage

import (
	"context"
	"io"
	"net/url"
	"time"

	"github.com/minio/minio-go/v7"
	"github.com/minio/minio-go/v7/pkg/credentials"
)

type S3Storage struct {
	client *minio.Client
	bucket string
}

type S3Config struct {
	Endpoint  string
	Bucket    string
	Region    string
	AccessKey string
	SecretKey string
	UseSSL    bool
}

func NewS3(cfg S3Config) (*S3Storage, error) {
	client, err := minio.New(cfg.Endpoint, &minio.Options{
		Creds:  credentials.NewStaticV4(cfg.AccessKey, cfg.SecretKey, ""),
		Secure: cfg.UseSSL,
		Region: cfg.Region,
	})
	if err != nil {
		return nil, err
	}

	return &S3Storage{
		client: client,
		bucket: cfg.Bucket,
	}, nil
}

func (s *S3Storage) Upload(ctx context.Context, key string, reader io.Reader, contentType string) error {
	_, err := s.client.PutObject(ctx, s.bucket, key, reader, -1, minio.PutObjectOptions{
		ContentType: contentType,
	})
	return err
}

func (s *S3Storage) PresignedURL(ctx context.Context, key string, expiry time.Duration) (string, error) {
	u, err := s.client.PresignedGetObject(ctx, s.bucket, key, expiry, url.Values{})
	if err != nil {
		return "", err
	}
	return u.String(), nil
}

func (s *S3Storage) Ping(ctx context.Context) error {
	_, err := s.client.BucketExists(ctx, s.bucket)
	return err
}
