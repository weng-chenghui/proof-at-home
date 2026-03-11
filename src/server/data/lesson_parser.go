package data

import (
	"fmt"
	"strings"

	toml "github.com/pelletier/go-toml/v2"
	"gopkg.in/yaml.v3"
)

// ParseLessonFile parses a lesson.md file with YAML frontmatter (between --- delimiters).
// Returns a Lesson with Content set to the body after the frontmatter.
func ParseLessonFile(raw []byte) (Lesson, error) {
	content := string(raw)
	if !strings.HasPrefix(content, "---\n") {
		return Lesson{}, fmt.Errorf("missing --- frontmatter delimiter")
	}
	rest := content[4:] // skip opening ---\n
	endIdx := strings.Index(rest, "\n---\n")
	if endIdx < 0 {
		endIdx = strings.Index(rest, "\n---")
		if endIdx < 0 {
			return Lesson{}, fmt.Errorf("missing closing --- frontmatter delimiter")
		}
	}
	frontmatter := rest[:endIdx]
	body := strings.TrimLeft(rest[endIdx+4:], "\n\r")

	var l Lesson
	if err := yaml.Unmarshal([]byte(frontmatter), &l); err != nil {
		return Lesson{}, fmt.Errorf("parsing YAML frontmatter: %w", err)
	}
	l.Content = body
	return l, nil
}

// ParseSeriesFile parses a series.md file with YAML frontmatter.
func ParseSeriesFile(raw []byte) (Series, error) {
	content := string(raw)
	if !strings.HasPrefix(content, "---\n") {
		return Series{}, fmt.Errorf("missing --- frontmatter delimiter")
	}
	rest := content[4:]
	endIdx := strings.Index(rest, "\n---\n")
	if endIdx < 0 {
		endIdx = strings.Index(rest, "\n---")
		if endIdx < 0 {
			return Series{}, fmt.Errorf("missing closing --- frontmatter delimiter")
		}
	}
	frontmatter := rest[:endIdx]
	body := strings.TrimLeft(rest[endIdx+4:], "\n\r")

	var s Series
	if err := yaml.Unmarshal([]byte(frontmatter), &s); err != nil {
		return Series{}, fmt.Errorf("parsing YAML frontmatter: %w", err)
	}
	s.Content = body
	return s, nil
}

// RenderLessonFile renders a Lesson as a markdown file with YAML frontmatter.
func RenderLessonFile(l Lesson) ([]byte, error) {
	meta := struct {
		LessonID       string         `yaml:"lesson_id"`
		AuthorUsername string         `yaml:"author_username,omitempty"`
		Title          string         `yaml:"title"`
		Topic          string         `yaml:"topic,omitempty"`
		Difficulty     string         `yaml:"difficulty,omitempty"`
		Description    string         `yaml:"description,omitempty"`
		Prerequisites  string         `yaml:"prerequisites,omitempty"`
		ConjectureIDs  []string       `yaml:"conjecture_ids,omitempty,flow"`
		Published      bool           `yaml:"published"`
		AIAnnotations  []AIAnnotation `yaml:"ai_annotations,omitempty"`
		References     []Reference    `yaml:"references,omitempty"`
	}{
		LessonID:       l.LessonID,
		AuthorUsername: l.AuthorUsername,
		Title:          l.Title,
		Topic:          l.Topic,
		Difficulty:     l.Difficulty,
		Description:    l.Description,
		Prerequisites:  l.Prerequisites,
		ConjectureIDs:  l.ConjectureIDs,
		Published:      l.Published,
		AIAnnotations:  l.AIAnnotations,
		References:     l.References,
	}

	yamlBytes, err := yaml.Marshal(meta)
	if err != nil {
		return nil, fmt.Errorf("marshalling YAML: %w", err)
	}

	var sb strings.Builder
	sb.WriteString("---\n")
	sb.Write(yamlBytes)
	sb.WriteString("---\n")
	if l.Content != "" {
		sb.WriteString(l.Content)
		if !strings.HasSuffix(l.Content, "\n") {
			sb.WriteString("\n")
		}
	}
	return []byte(sb.String()), nil
}

// ParseCreditsFile parses a CREDITS.toml file into a Credits struct.
func ParseCreditsFile(raw []byte) (*Credits, error) {
	var c Credits
	if err := toml.Unmarshal(raw, &c); err != nil {
		return nil, fmt.Errorf("parsing CREDITS.toml: %w", err)
	}
	return &c, nil
}

// RenderCreditsFile renders a Credits struct as TOML bytes.
func RenderCreditsFile(c *Credits) ([]byte, error) {
	data, err := toml.Marshal(c)
	if err != nil {
		return nil, fmt.Errorf("marshalling CREDITS.toml: %w", err)
	}
	return data, nil
}

// RenderSeriesFile renders a Series as a markdown file with YAML frontmatter.
func RenderSeriesFile(s Series) ([]byte, error) {
	meta := struct {
		SeriesID       string   `yaml:"series_id"`
		Title          string   `yaml:"title"`
		AuthorUsername string   `yaml:"author_username,omitempty"`
		Difficulty     string   `yaml:"difficulty,omitempty"`
		Description    string   `yaml:"description,omitempty"`
		LessonIDs      []string `yaml:"lesson_ids,omitempty,flow"`
		Published      bool     `yaml:"published"`
	}{
		SeriesID:       s.SeriesID,
		Title:          s.Title,
		AuthorUsername: s.AuthorUsername,
		Difficulty:     s.Difficulty,
		Description:    s.Description,
		LessonIDs:      s.LessonIDs,
		Published:      s.Published,
	}

	yamlBytes, err := yaml.Marshal(meta)
	if err != nil {
		return nil, fmt.Errorf("marshalling YAML: %w", err)
	}

	var sb strings.Builder
	sb.WriteString("---\n")
	sb.Write(yamlBytes)
	sb.WriteString("---\n")
	if s.Content != "" {
		sb.WriteString(s.Content)
		if !strings.HasSuffix(s.Content, "\n") {
			sb.WriteString("\n")
		}
	}
	return []byte(sb.String()), nil
}
