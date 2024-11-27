package main

import (
	"bytes"
	"fmt"
	"strconv"
	"strings"
)

// Tokenizing

type tokenKind int

const (
	// Token types
	eof tokenKind = iota + 128
	word
	ge
	le
	number
)

type token struct {
	kind tokenKind
	val  string
	pos  int
}

func T(kind tokenKind, val string, pos int) token {
	return token{kind: kind, val: val, pos: pos}
}

func isSpace(c rune) bool {
	switch c {
	case ' ', '\t', '\n', '\r':
		return true
	}
	return false
}

func isWordChar(c rune) bool {
	return 'a' <= c && c <= 'z' || 'A' <= c && c <= 'Z' || '0' <= c && c <= '9'
}

func tokenize(s string) []token {
	var tokens []token
	for i := 0; i < len(s); {
		for i < len(s) && isSpace(rune(s[i])) {
			i += 1
		}
		if i >= len(s) {
			break
		}
		switch s[i] {
		case '(', ')', '{', '}', '[', ']', ',', ':', ';', '.', '?', '+', '-', '*', '/', '%', '^', '&', '|', '=', '!':
			tokens = append(tokens, T(tokenKind(s[i]), string(s[i]), i))
			i += 1
		case '>':
			if i+1 < len(s) && s[i+1] == '=' {
				tokens = append(tokens, T(ge, ">=", i))
				i += 2
			} else {
				tokens = append(tokens, T(tokenKind('>'), ">", i))
				i += 1
			}
		case '<':
			if len(s) > 1 && s[1] == '=' {
				tokens = append(tokens, T(le, "<=", i))
				i += 2
			} else {
				tokens = append(tokens, T(tokenKind('<'), "<", i))
				i += 1
			}
		case '0', '1', '2', '3', '4', '5', '6', '7', '8', '9':
			// Number
			j := i
			for j < len(s) && '0' <= s[j] && s[j] <= '9' {
				j += 1
			}
			tokens = append(tokens, T(number, s[i:j], i))
			i = j
		default:
			// Word
			j := i
			for j < len(s) && isWordChar(rune(s[j])) {
				j += 1
			}
			tokens = append(tokens, T(word, strings.ToLower(s[i:j]), i))
			i = j
		}
	}
	return tokens
}

// The good shit

type Matcher func([]token) (any, []token, error)

type Exactly struct {
	token token
}

func (e *Exactly) Match(tokens []token) (any, []token, error) {
	if len(tokens) == 0 {
		return nil, nil, NewParseError(fmt.Sprintf("expected token %v", e.token), 0, 0)
	}
	if tokens[0] != e.token {
		return nil, nil, NewParseError(fmt.Sprintf("expected token %v", e.token), tokens[0].pos, tokens[0].pos+1)
	}
	return nil, tokens[1:], nil
}

func Word(s string) Matcher {
	return func(tokens []token) (any, []token, error) {
		if len(tokens) == 0 || tokens[0].kind != word || tokens[0].val != s {
			return nil, nil, NewParseError(fmt.Sprintf("expected word %q", s), tokens[0].pos, tokens[0].pos+len(s))
		}
		return nil, tokens[1:], nil
	}
}

func Exact(kinds ...tokenKind) Matcher {
	return func(tokens []token) (any, []token, error) {
		vals := make([]string, len(tokens))
		for i, t := range kinds {
			if i >= len(tokens) {
				return nil, nil, NewParseError("unexpected EOF", 0, 0)
			}
			if tokens[i].kind != t {
				return nil, nil, NewParseError(fmt.Sprintf("expected token kind %v", t), tokens[i].pos, tokens[i].pos+1)
			}
			vals[i] = tokens[i].val
		}
		return vals, tokens[len(kinds):], nil
	}
}

func Or(ms ...Matcher) Matcher {
	return func(tokens []token) (any, []token, error) {
		var err error
		for _, matcher := range ms {
			var result any
			result, tokens, err = matcher(tokens)
			if err == nil {
				return result, tokens, nil
			}
		}
		if err != nil {
			return nil, nil, err
		}
		return nil, nil, NewParseError("no matches succeeded", 0, 0)
	}
}

func Maybe(m Matcher) Matcher {
	return func(tokens []token) (any, []token, error) {
		result, rest, err := m(tokens)
		if err != nil {
			return nil, tokens, nil
		}
		return result, rest, nil
	}
}

func Repeat(m Matcher) Matcher {
	return func(tokens []token) (any, []token, error) {
		matches := []any{}
		for {
			result, rest, err := m(tokens)
			if err != nil {
				break
			}
			matches = append(matches, result)
			tokens = rest
		}
		return matches, tokens, nil
	}
}

func Concat(ms ...Matcher) Matcher {
	return func(tokens []token) (any, []token, error) {
		var matches []any
		for _, matcher := range ms {
			result, rest, err := matcher(tokens)
			if err != nil {
				return nil, nil, err
			}
			matches = append(matches, result)
			tokens = rest
		}
		return matches, tokens, nil
	}
}

type MapMatch struct {
	matcher Matcher
	f       func(any) any
}

func (m *MapMatch) Match(tokens []token) (any, []token, error) {
	val, rest, err := m.matcher(tokens)
	if err != nil {
		return nil, nil, err
	}
	return m.f(val), rest, nil
}

func Map(m Matcher, f func(any) any) Matcher {
	return func(tokens []token) (any, []token, error) {
		val, rest, err := m(tokens)
		if err != nil {
			return nil, nil, err
		}
		return f(val), rest, nil
	}
}

// Expressions

type Expression interface {
	Eval(row map[string]int) int
	Format(buf *bytes.Buffer)
}

type Number struct {
	val int
}

func (n *Number) Eval(row map[string]int) int {
	return n.val
}

func (n *Number) Format(buf *bytes.Buffer) {
	buf.WriteString(strconv.Itoa(n.val))
}

type Variable struct {
	name string
}

func (v *Variable) Eval(row map[string]int) int {
	return row[v.name]
}

func (v *Variable) Format(buf *bytes.Buffer) {
	buf.WriteString(v.name)
}

type Op int

const (
	Add Op = iota
	Sub
	Mul
	Div
)

type BinOp struct {
	left  Expression
	right Expression
	op    Op
}

func (b *BinOp) Eval(row map[string]int) int {
	l := b.left.Eval(row)
	r := b.right.Eval(row)
	switch b.op {
	case Add:
		return l + r
	case Sub:
		return l - r
	case Mul:
		return l * r
	case Div:
		return l / r
	}
	panic("unreachable")
}

func (b *BinOp) Format(buf *bytes.Buffer) {
	buf.WriteRune('(')
	b.left.Format(buf)
	switch b.op {
	case Add:
		buf.WriteRune('+')
	case Sub:
		buf.WriteRune('-')
	case Mul:
		buf.WriteRune('*')
	case Div:
		buf.WriteRune('/')
	}
	b.right.Format(buf)
	buf.WriteRune(')')
}

func ExprInstaller() Installer {
	return func(sys *System) {
		number := Map(Exact(number), func(matches any) any {
			ms := matches.([]string)
			val, _ := strconv.Atoi(ms[0])
			return &Number{val: val}
		})
		variable := Map(Exact(word), func(matches any) any {
			ms := matches.([]string)
			return &Variable{name: ms[0]}
		})

		sys.Register("expr/Factor", number)
		sys.Register("expr/Factor", variable)
		sys.Register("expr/Factor", Map(Concat(
			Exact('('),
			sys.Match("expr/Expr"),
			Exact(')'),
		), func(matches any) any {
			ms := matches.([]any)
			return ms[1]
		}))

		sys.Register("expr/Term", Map(Concat(
			sys.Match("expr/Factor"),
			Repeat(
				Concat(
					Or(Exact('*'), Exact('/')),
					sys.Match("expr/Factor"),
				),
			),
		), func(matches any) any {
			ms := matches.([]any)
			lhs := ms[0].(Expression)
			for _, m := range ms[1].([]any) {
				ms := m.([]any)
				op := ms[0].([]string)[0]
				rhs := ms[1].(Expression)
				if op == "*" {
					lhs = &BinOp{left: lhs, right: rhs, op: Mul}
				} else {
					lhs = &BinOp{left: lhs, right: rhs, op: Div}
				}
			}
			return lhs
		}))

		expr := Map(Concat(
			sys.Match("expr/Term"),
			Repeat(
				Concat(
					Or(Exact('+'), Exact('-')),
					sys.Match("expr/Term"),
				),
			),
		), func(matches any) any {
			ms := matches.([]any)
			lhs := ms[0].(Expression)
			for _, m := range ms[1].([]any) {
				ms := m.([]any)
				op := ms[0].([]string)[0]
				rhs := ms[1].(Expression)
				if op == "+" {
					lhs = &BinOp{left: lhs, right: rhs, op: Add}
				} else {
					lhs = &BinOp{left: lhs, right: rhs, op: Sub}
				}
			}
			return lhs
		})

		sys.Register("expr/Expr", expr)
	}
}

// Top-Level Commands

type Exec interface {
	Exec(*System) string
}

type Install struct {
	extension string
}

func InstallInstaller() Installer {
	return func(sys *System) {
		sys.Register("S", Map(Concat(
			Word("install"),
			Exact(word),
		), func(matches any) any {
			ms := matches.([]any)
			return Install{extension: ms[1].([]string)[0]}
		}))
	}
}

type Eval struct {
	expr Expression
}

func (e Eval) Exec(sys *System) string {
	var buf bytes.Buffer
	e.expr.Format(&buf)
	return fmt.Sprintf("%s = %d", buf.String(), e.expr.Eval(map[string]int{"hello": 123}))
}

func (i Install) Exec(sys *System) string {
	switch i.extension {
	case "select":
		installSelect(sys)
	case "eval":
		sys.Register("S", Map(Concat(
			Word("eval"),
			sys.Match("expr/Expr"),
		), func(matches any) any {
			ms := matches.([]any)
			expr := ms[1].(Expression)
			return Eval{expr: expr}
		}))
		return "installed eval"
	}
	return fmt.Sprintf("Unknown extension: %s", i.extension)
}

// SELECT

type Select struct {
	cols   []Expression
	tables []string
}

func (s *Select) Exec(sys *System) string {
	var buf bytes.Buffer
	for i, col := range s.cols {
		if i > 0 {
			buf.WriteString(", ")
		}
		col.Format(&buf)
	}
	return fmt.Sprintf("executing SELECT %s FROM %s", buf.String(), strings.Join(s.tables, ", "))
}

func installSelect(sys *System) {
	sys.Register("select/col-list", Map(Concat(
		sys.Match("expr/Expr"),
		Repeat(
			Concat(
				Exact(','),
				sys.Match("expr/Expr"),
			),
		),
	), func(matches any) any {
		ms := matches.([]any)
		cols := []Expression{ms[0].(Expression)}
		rest := ms[1].([]any)
		for _, m := range rest {
			ms := m.([]any)
			cols = append(cols, ms[1].(Expression))
		}
		return cols
	},
	))

	sys.Register("select/table-list", Map(Concat(
		Exact(word),
		Repeat(
			Concat(
				Exact(','),
				Exact(word),
			),
		),
	), func(matches any) any {
		ms := matches.([]any)
		tabs := []string{ms[0].([]string)[0]}
		rest := ms[1].([]any)
		for _, m := range rest {
			ms := m.([]any)
			tabs = append(tabs, ms[1].([]string)[0])
		}
		return tabs
	}))

	sys.Register("select/after", Exact())

	sys.Register("S", Map(Concat(
		Word("select"),
		sys.Match("select/col-list"),
		Word("from"),
		sys.Match("select/table-list"),
		sys.Match("select/after"),
	), func(matches any) any {
		ms := matches.([]any)
		return &Select{cols: ms[1].([]Expression), tables: ms[3].([]string)}
	}))
}

// Framework

type NonterminalMatch struct {
	nonterminal string
	system      *System
}

func (n *NonterminalMatch) Match(tokens []token) (any, []token, error) {
	return n.system.parseNonterminal(n.nonterminal, tokens)
}

type Installer func(sys *System)

type System struct {
	// Each nonterminal is implicitly an Or in the order the extensions have
	// been installed.
	nonterminals map[string][]Matcher
}

func NewSystem() *System {
	return &System{
		nonterminals: make(map[string][]Matcher),
	}
}

func (sys *System) Install(installer Installer) {
	installer(sys)
}

func (sys *System) parseNonterminal(nonterminal string, tokens []token) (any, []token, error) {
	errs := []error{}
	for _, matcher := range sys.nonterminals[nonterminal] {
		result, rest, err := matcher(tokens)
		if err == nil {
			return result, rest, nil
		}
		errs = append(errs, err)
	}
	if len(errs) > 0 {
		var bestErr *ParseError
		// return the parse error that got the furthest
		for _, err := range errs {
			if pe, ok := err.(*ParseError); ok {
				if bestErr == nil {
					bestErr = pe
				} else {
					if pe.start > bestErr.start {
						bestErr = pe
					}
				}
			}
		}
		return nil, nil, bestErr
	}
	return nil, nil, fmt.Errorf("no match for nonterminal %q", nonterminal)
}

func (sys *System) Register(nonterminal string, matcher Matcher) {
	sys.nonterminals[nonterminal] = append(sys.nonterminals[nonterminal], matcher)
}

func (sys *System) Match(nonterminal string) Matcher {
	return func(tokens []token) (any, []token, error) {
		return sys.parseNonterminal(nonterminal, tokens)
	}
}

type ParseError struct {
	msg   string
	start int
	end   int
}

func NewParseError(msg string, start int, end int) *ParseError {
	return &ParseError{msg: msg, start: start, end: end}
}

func (e *ParseError) Error() string {
	return e.ErrMsg("")
}

func (e *ParseError) ErrMsg(input string) string {
	var buf bytes.Buffer
	buf.WriteString("parse error:\n")
	buf.WriteString(input)
	buf.WriteByte('\n')
	for i := 0; i < e.start; i++ {
		buf.WriteRune(' ')
	}
	buf.WriteByte('^')
	for i := e.start; i < e.end-2; i++ {
		buf.WriteByte('~')
	}
	buf.WriteByte('^')
	buf.WriteByte('\n')
	buf.WriteString(e.msg)
	return buf.String()
}

func (sys *System) Parse(s string) (any, error) {
	tokens := tokenize(s)
	val, tokens, err := sys.parseNonterminal("S", tokens)
	if err != nil {
		return nil, err
	}
	if len(tokens) > 0 {
		return nil, NewParseError("unconsumed tokens", tokens[0].pos, len(s))
	}
	return val, nil
}

func (sys *System) Execute(s string) string {
	val, err := sys.Parse(s)
	if err != nil {
		if pe, ok := err.(*ParseError); ok {
			return pe.ErrMsg(s)
		}
		return err.Error()
	}
	return val.(Exec).Exec(sys)
}

func main() {
	sys := NewSystem()

	sys.Install(InstallInstaller())
	sys.Install(ExprInstaller())

	sys.Execute("install select")
	result := sys.Execute("select a, b, c from foo")
	fmt.Println(result)

	result = sys.Execute("select a as a, b, c from foo")
	fmt.Println(result)

	result = sys.Execute("select a, b, c from foo where d = 4")
	fmt.Println(result)
}
