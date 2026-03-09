package data

import (
	"encoding/json"
	"fmt"

	toml "github.com/pelletier/go-toml/v2"
	"gopkg.in/yaml.v3"
)

// UnmarshalConjecture decodes a Conjecture from raw bytes using the format
// indicated by ext (".json", ".toml", ".yaml", ".yml").
func UnmarshalConjecture(raw []byte, ext string) (Conjecture, error) {
	var c Conjecture
	var err error
	switch ext {
	case ".json":
		err = json.Unmarshal(raw, &c)
	case ".toml":
		err = toml.Unmarshal(raw, &c)
	case ".yaml", ".yml":
		err = yaml.Unmarshal(raw, &c)
	default:
		return c, fmt.Errorf("unsupported conjecture format: %s", ext)
	}
	return c, err
}

// MarshalConjecture encodes a Conjecture to bytes in the format indicated by ext.
func MarshalConjecture(c Conjecture, ext string) ([]byte, error) {
	switch ext {
	case ".json":
		return json.MarshalIndent(c, "", "  ")
	case ".toml":
		return toml.Marshal(c)
	case ".yaml", ".yml":
		return yaml.Marshal(c)
	default:
		return nil, fmt.Errorf("unsupported conjecture format: %s", ext)
	}
}

// IsConjectureExt returns true if the file extension is a supported conjecture format.
func IsConjectureExt(ext string) bool {
	switch ext {
	case ".json", ".toml", ".yaml", ".yml":
		return true
	}
	return false
}
