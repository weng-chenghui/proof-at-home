// Package static embeds the web frontend files.
package static

import "embed"

//go:embed *.html *.css *.js
var Files embed.FS
