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

type WhereExpr struct {
	input RelExpr
	where Expression
}

func (w *WhereExpr) Format(buf *bytes.Buffer) {
	buf.WriteString("(where ")
	w.input.Format(buf)
	buf.WriteString(" ")
	w.where.Format(buf)
	buf.WriteString(")")
}

func (w *WhereExpr) Apply(expr RelExpr) RelExpr {
	return &WhereExpr{input: expr, where: w.where}
}

func (i Install) Exec(sys *System) string {
	switch i.extension {
	case "select":
		installSelect(sys)
		return "installed select"
	case "where":
		sys.Register("select/after", Map(Concat(
			Word("where"),
			sys.Match("expr/Expr"),
		), func(matches any) any {
			ms := matches.([]any)
			return &WhereExpr{where: ms[1].(Expression)}
		}))
		return "installed where"
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

type RelExpr interface {
	// Format writes the expression as an s-expression to the buffer.
	Format(buf *bytes.Buffer)
}

type SelectExpr struct {
	cols   []Expression
	tables []string
}

func (s *SelectExpr) Format(buf *bytes.Buffer) {
	buf.WriteString("(select")
	for _, col := range s.cols {
		buf.WriteRune(' ')
		col.Format(buf)
	}
	buf.WriteString(" from")
	for _, table := range s.tables {
		buf.WriteRune(' ')
		buf.WriteString(table)
	}
	buf.WriteString(")")
}

type Applier interface {
	Apply(expr RelExpr) RelExpr
}

type Select struct {
	relexpr RelExpr
}

func (s *Select) Exec(sys *System) string {
	var buf bytes.Buffer
	s.relexpr.Format(&buf)
	return fmt.Sprintf("executing %s", buf.String())
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

	sys.Denote("select/after")

	sys.Register("S", Map(Concat(
		Word("select"),
		sys.Match("select/col-list"),
		Word("from"),
		sys.Match("select/table-list"),
		sys.Match("select/after"),
	), func(matches any) any {
		ms := matches.([]any)
		var expr RelExpr = &SelectExpr{cols: ms[1].([]Expression), tables: ms[3].([]string)}
		if after, ok := ms[4].(Applier); ok {
			expr = after.Apply(expr)
		}
		return &Select{relexpr: expr}
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
	lowpri       map[string][]Matcher
}

func NewSystem() *System {
	return &System{
		nonterminals: make(map[string][]Matcher),
		lowpri:       make(map[string][]Matcher),
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
	for _, matcher := range sys.lowpri[nonterminal] {
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

// Denote installs a nonterminal that matches nothing, subsequent registers will have
// precedence over the empty installation.
func (sys *System) Denote(nonterminal string) {
	sys.lowpri[nonterminal] = append(sys.lowpri[nonterminal], Exact())
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
	fmt.Printf("> %s\n", s)
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

	for _, s := range []string{
		"install select",
		"select a, b, c from foo",
		"select a form bar",
		"select a, b, c from foo where d = 4",
		"install where",
		"select a, b, c from foo where d",
	} {
		result := sys.Execute(s)
		fmt.Println(result)
		fmt.Println()
	}
}
