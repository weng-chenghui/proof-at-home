FROM golang:1.24-alpine AS builder

RUN apk add --no-cache git

WORKDIR /app

COPY go.mod go.sum ./
RUN go mod download

COPY . .

RUN CGO_ENABLED=0 GOOS=linux go build -o /server ./src/server

FROM alpine:3.20

RUN apk add --no-cache ca-certificates git

COPY --from=builder /server /server
COPY conjectures/ /conjectures/

ENV PORT=8080
ENV CONJECTURES_DIR=/conjectures

EXPOSE 8080

ENTRYPOINT ["/server"]
