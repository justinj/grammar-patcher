package main

import (
	"bytes"
	"errors"
	"fmt"
	"strconv"
	"strings"
)

const whitespace = " \t\n\r"

type Parser func(input string) (any, string, error)

func Word(s string) Parser {
	return func(input string) (any, string, error) {
		input = strings.TrimLeft(input, whitespace)
		if strings.HasPrefix(input, s) {
			return s, input[len(s):], nil
		}
		return "", "", fmt.Errorf("word %v not found", s)
	}
}

func OneOf(ps ...Parser) Parser {
	return func(input string) (any, string, error) {
		for _, p := range ps {
			if r, rest, err := p(input); err == nil {
				return r, rest, nil
			}
		}
		return nil, "", errors.New("no parser matched")
	}
}

func Sequence(ps ...Parser) Parser {
	return func(input string) (any, string, error) {
		var result []any
		for _, p := range ps {
			r, rest, err := p(input)
			if err != nil {
				return nil, "", err
			}
			result = append(result, r)
			input = rest
		}
		return result, input, nil
	}
}

func Map(p Parser, f func(any) any) Parser {
	return func(input string) (any, string, error) {
		r, rest, err := p(input)
		if err != nil {
			return nil, rest, err
		}
		return f(r), rest, nil
	}
}

func Optional(p Parser) Parser {
	return OneOf(p, func(input string) (any, string, error) {
		return nil, input, nil
	})
}

func Repeat(p Parser) Parser {
	return func(input string) (any, string, error) {
		var result []any
		for {
			r, rest, err := p(input)
			if err != nil {
				break
			}
			result = append(result, r)
			input = rest
		}
		return result, input, nil
	}
}

func Identifier(input string) (any, string, error) {
	input = strings.TrimLeft(input, whitespace)
	if len(input) == 0 {
		return "", "", errors.New("unexpected eof")
	}
	if 'a' <= input[0] && input[0] <= 'z' || 'A' <= input[0] && input[0] <= 'Z' || input[0] == '_' {
		i := 0
		for i = 1; i < len(input); i++ {
			if !('a' <= input[i] && input[i] <= 'z' || 'A' <= input[i] && input[i] <= 'Z' || '0' <= input[i] && input[i] <= '9' || input[i] == '_') {
				break
			}
		}
		return input[:i], input[i:], nil
	}
	return "", "", errors.New("identifier not found")
}

// %whitespace <- [ \t\n\r]*
// List(D) <- D (',' D)*
// Parens(D) <- '(' D ')'

type Format interface {
	Format(buf *bytes.Buffer)
}

type AstNode interface {
	Format
}

type BinOp struct {
	lhs Expr
	op  string
	rhs Expr
}

func (b *BinOp) Format(buf *bytes.Buffer) {
	buf.WriteByte('(')
	b.lhs.Format(buf)
	fmt.Fprintf(buf, " %s ", b.op)
	b.rhs.Format(buf)
	buf.WriteByte(')')
}

var OperatorsByPrecedence = [][]Parser{
	{Word("*"), Word("/")},
	{Word("+"), Word("-")},
	{Word("="), Word("<>"), Word("<="), Word("<"), Word(">="), Word(">")},
}

var errEof = errors.New("unexpected eof")

func isDigit(r byte) bool {
	return '0' <= r && r <= '9'
}

func Number(input string) (any, string, error) {
	input = strings.TrimLeft(input, whitespace)
	if len(input) == 0 {
		return nil, "", errEof
	}

	i := 0
	for i < len(input) && isDigit(input[i]) {
		i += 1
	}
	if i == 0 {
		return nil, "", errors.New("expected number")
	}
	num := input[:i]
	val, _ := strconv.Atoi(num)

	return DInt(val), input[i:], nil
}

type ColumnExpr struct {
	name string
}

func (c *ColumnExpr) Format(buf *bytes.Buffer) {
	buf.WriteString(c.name)
}

var Column = Map(Identifier, func(matches any) any {
	return &ColumnExpr{matches.(string)}
})

func PrecExpr(sys *System, precedence int) Parser {
	return func(input string) (any, string, error) {
		if precedence == 0 {
			// At this precedence, we only parse literals and open parentheses.
			return OneOf(
				sys.Parser("Literal"),
				Map(
					Sequence(
						Word("("),
						sys.Parser("ScalarExpr"),
						Word(")"),
					),
					func(matches any) any {
						return matches.([]any)[1]
					},
				),
			)(input)
		} else {
			return Map(Sequence(
				PrecExpr(sys, precedence-1),
				Repeat(
					Sequence(
						OneOf(OperatorsByPrecedence[precedence-1]...),
						PrecExpr(sys, precedence-1),
					),
				),
			),
				func(matches any) any {
					ms := matches.([]any)
					result := ms[0].(Expr)
					others := ms[1].([]any)
					for _, o := range others {
						pair := o.([]any)
						op := pair[0].(string)
						expr := pair[1].(Expr)
						result = &BinOp{
							lhs: result,
							op:  op,
							rhs: expr,
						}
					}
					return result
				},
			)(input)
		}
	}
}

// var ScalarExpr = PrecExpr(len(OperatorsByPrecedence))

func Parens(p Parser) Parser {
	return Map(Sequence(
		Word("("),
		p,
		Word(")"),
	), func(matches any) any {
		return matches.([]any)[1]
	})
}

type Expr interface {
	Format
}

type DInt int64

func (d DInt) Format(buf *bytes.Buffer) {
	fmt.Fprintf(buf, "%d", d)
}

type DString string

func (d DString) Format(buf *bytes.Buffer) {
	fmt.Fprintf(buf, "%s", d)
}

func CommaSeparated(parser Parser) Parser {
	return func(input string) (any, string, error) {
		result := []any{}
		r, input, err := parser(input)
		if err != nil {
			return nil, input, err
		}
		result = append(result, r)
		for {
			_, rest, err := Word(",")(input)
			if err != nil {
				break
			}
			r, rest, err = parser(rest)
			if err != nil {
				return nil, input, err
			}
			result = append(result, r)
			input = rest
		}
		return result, input, nil
	}
}

// SelectStmt <- SimpleSelect (SetopClause SimpleSelect)*

type SelectStmt struct {
	lhs AstNode
	op  SetopClause
	rhs AstNode
}

func (s *SelectStmt) Format(buf *bytes.Buffer) {
	s.lhs.Format(buf)
	s.op.Format(buf)
	s.rhs.Format(buf)
}

// SetopClause <-
//     ('UNION' / 'EXCEPT' / 'INTERSECT') 'ALL'?

type SetopClause struct {
	op  string
	all bool
}

func (s *SetopClause) Format(buf *bytes.Buffer) {
	fmt.Fprintf(buf, " %s ", s.op)
	if s.all {
		buf.WriteString("ALL ")
	}
}

var SetopClauseParser = Map(
	Sequence(OneOf(Word("UNION"), Word("EXCEPT"), Word("INTERSECT")), Optional(Word("ALL"))),
	func(matches any) any {
		ms := matches.([]any)
		return &SetopClause{ms[0].(string), ms[1] != nil}
	},
)

// SimpleSelect <- WithClause? SelectClause FromClause?
//     WhereClause? GroupByClause? HavingClause?
//     OrderByClause? LimitClause?

type Select struct {
	exprs   []AliasExpression
	tables  []string
	with    *WithClause
	where   *WhereClause
	groupBy *GroupByClause
	having  *HavingClause
	orderBy *OrderByClause
	limit   *LimitClause
}

func (s *Select) Format(buf *bytes.Buffer) {
	if s.with != nil {
		s.with.Format(buf)
	}
	buf.WriteString("SELECT ")
	for i, e := range s.exprs {
		if i > 0 {
			buf.WriteString(", ")
		}
		e.Format(buf)
	}
	buf.WriteString(" FROM ")
	for i, e := range s.tables {
		if i > 0 {
			buf.WriteString(", ")
		}
		buf.WriteString(e)
	}
	if s.where != nil {
		s.where.Format(buf)
	}
	if s.groupBy != nil {
		s.groupBy.Format(buf)
	}
	if s.having != nil {
		s.having.Format(buf)
	}
	if s.orderBy != nil {
		s.orderBy.Format(buf)
	}
	if s.limit != nil {
		s.limit.Format(buf)
	}
}

// WithStatement <- Identifier 'AS' SubqueryReference

type WithStatement struct {
	name     string
	subquery *Select
}

func (w *WithStatement) Format(buf *bytes.Buffer) {
	buf.WriteString(w.name)
	buf.WriteString(" AS (")
	w.subquery.Format(buf)
	buf.WriteString(") ")
}

// WithClause <- 'WITH' List(WithStatement)

type WithClause struct {
	statements []*WithStatement
}

func (w *WithClause) Format(buf *bytes.Buffer) {
	buf.WriteString("WITH ")
	for i, stmt := range w.statements {
		if i > 0 {
			buf.WriteString(", ")
		}
		stmt.Format(buf)
	}
}

// SelectClause <- 'SELECT' ('*' / List(AliasExpression))
// ColumnsAlias <- Parens(List(Identifier))
// TableReference <-
//     (SubqueryReference 'AS'? Identifier ColumnsAlias?) /
//     (Identifier ('AS'? Identifier)?)
// ExplicitJoin <- ('LEFT' / 'FULL')? 'OUTER'?
//     'JOIN' TableReference 'ON' Expression
// FromClause <- 'FROM' TableReference
//     ((',' TableReference) / ExplicitJoin)*
// WhereClause <- 'WHERE' Expression

type WhereClause struct {
	expr Expr
}

func (w *WhereClause) Format(buf *bytes.Buffer) {
	buf.WriteString(" WHERE ")
	w.expr.Format(buf)
}

// GroupByClause <- 'GROUP' 'BY' List(Expression)

type GroupByClause struct {
	exprs []Expr
}

func (g *GroupByClause) Format(buf *bytes.Buffer) {
	buf.WriteString(" GROUP BY ")
	for i, expr := range g.exprs {
		if i > 0 {
			buf.WriteString(", ")
		}
		expr.Format(buf)
	}
}

// HavingClause <- 'HAVING' Expression

type HavingClause struct {
	expr Expr
}

func (h *HavingClause) Format(buf *bytes.Buffer) {
	buf.WriteString(" HAVING ")
	h.expr.Format(buf)
}

// OrderByExpression <- Expression ('DESC' / 'ASC')?
//     ('NULLS' 'FIRST' / 'LAST')?

type OrderByExpression struct {
	expr  Expr
	desc  bool
	nulls string // "first", "last" or ""
}

func (o *OrderByExpression) Format(buf *bytes.Buffer) {
	o.expr.Format(buf)
	if o.desc {
		buf.WriteString(" DESC")
	} else {
		buf.WriteString(" ASC")
	}
	if o.nulls != "" {
		fmt.Fprintf(buf, " NULLS %s", strings.ToUpper(o.nulls))
	}
}

// OrderByClause <- 'ORDER' 'BY' List(OrderByExpression)

type OrderByClause struct {
	exprs []*OrderByExpression
}

func (o *OrderByClause) Format(buf *bytes.Buffer) {
	buf.WriteString(" ORDER BY ")
	for i, expr := range o.exprs {
		if i > 0 {
			buf.WriteString(", ")
		}
		expr.Format(buf)
	}
}

// LimitClause <- 'LIMIT' NumberLiteral

type LimitClause struct {
	limit DInt
}

func (l *LimitClause) Format(buf *bytes.Buffer) {
	fmt.Fprintf(buf, " LIMIT %d", l.limit)
}

var LimitClauseParser = Map(
	Sequence(Word("LIMIT"), Number),
	func(matches any) any {
		ms := matches.([]any)
		limit := ms[1].(DInt)
		return &LimitClause{limit: limit}
	},
)

// AliasExpression <- Expression ('AS'? Identifier)?

type AliasExpression struct {
	expr Expr
	as   string
}

func (a *AliasExpression) Format(buf *bytes.Buffer) {
	a.expr.Format(buf)
	if a.as != "" {
		fmt.Fprintf(buf, " AS %s", a.as)
	}
}

type System struct {
	nonterminals map[string][]Parser
}

func NewSystem() *System {
	return &System{nonterminals: map[string][]Parser{}}
}

func (s *System) Install(nonterminal string, parser Parser) {
	s.nonterminals[nonterminal] = append(s.nonterminals[nonterminal], parser)
}

func (s *System) InstallFront(nonterminal string, parser Parser) {
	s.nonterminals[nonterminal] = append([]Parser{parser}, s.nonterminals[nonterminal]...)
}

func (s *System) Parser(nonterminal string) Parser {
	return func(input string) (any, string, error) {
		for _, parser := range s.nonterminals[nonterminal] {
			if r, rest, err := parser(input); err == nil {
				return r, rest, nil
			}
		}
		return nil, input, fmt.Errorf("no parser matched")
	}
}

func InstallSelect(sys *System) {
	// Some of these things need to be installed like this to avoid
	// Golang initialization order issues.
	sys.Install("WithClause", Map(
		Sequence(
			Word("WITH"),
			CommaSeparated(sys.Parser("WithStatement")),
		),
		func(matches any) any {
			ms := matches.([]any)
			stmts := ms[1].([]any)
			result := make([]*WithStatement, len(stmts))
			for i, stmt := range stmts {
				result[i] = stmt.(*WithStatement)
			}
			return &WithClause{statements: result}
		},
	))

	sys.Install("WithStatement", Map(
		Sequence(
			Identifier,
			Word("AS"),
			sys.Parser("SubqueryReference"),
		),
		func(matches any) any {
			ms := matches.([]any)
			return &WithStatement{
				name:     ms[0].(string),
				subquery: ms[2].(*Select),
			}
		},
	))

	// SubqueryReference <- Parens(SelectStmt)
	sys.Install("SubqueryReference", Parens(sys.Parser("SelectStmt")))

	sys.Install("SelectStmt", Map(
		Sequence(sys.Parser("Select"), Repeat(Sequence(SetopClauseParser, sys.Parser("Select")))),
		func(matches any) any {
			ms := matches.([]any)
			lhs := ms[0].(AstNode)
			others := ms[1].([]any)
			for _, o := range others {
				pair := o.([]any)
				op := pair[0].(*SetopClause)
				expr := pair[1].(AstNode)
				lhs = &SelectStmt{lhs: lhs, op: *op, rhs: expr}
			}
			return lhs
		},
	))

	sys.Install("Select", Map(Sequence(
		Optional(sys.Parser("WithClause")),
		Word("SELECT"),
		CommaSeparated(sys.Parser("AliasExpression")),
		Word("FROM"),
		Identifier,
		Optional(sys.Parser("WhereClause")),
		Optional(sys.Parser("GroupByClause")),
		Optional(sys.Parser("HavingClause")),
		Optional(sys.Parser("OrderByClause")),
		Optional(LimitClauseParser),
	), func(matches any) any {
		ms := matches.([]any)
		var with *WithClause
		if ms[0] != nil {
			with = ms[0].(*WithClause)
		}
		exprsA := ms[2].([]any)
		exprs := make([]AliasExpression, len(exprsA))
		for i := range exprs {
			exprs[i] = exprsA[i].(AliasExpression)
		}
		tables := []string{ms[4].(string)}
		var where *WhereClause
		if ms[5] != nil {
			where = ms[5].(*WhereClause)
		}
		var groupBy *GroupByClause
		if ms[6] != nil {
			groupBy = ms[6].(*GroupByClause)
		}
		var having *HavingClause
		if ms[7] != nil {
			having = ms[7].(*HavingClause)
		}
		var orderBy *OrderByClause
		if ms[8] != nil {
			orderBy = ms[8].(*OrderByClause)
		}
		var limit *LimitClause
		if ms[9] != nil {
			limit = ms[9].(*LimitClause)
		}
		return &Select{
			with:    with,
			exprs:   exprs,
			tables:  tables,
			where:   where,
			groupBy: groupBy,
			having:  having,
			orderBy: orderBy,
			limit:   limit,
		}
	}))

	sys.Install("AliasExpression", Map(
		Sequence(sys.Parser("ScalarExpr"), Optional(Sequence(Word("AS"), Identifier))),
		func(matches any) any {
			ms := matches.([]any)
			expr := ms[0].(Expr)
			as := ""
			if ms[1] != nil {
				as = ms[1].([]any)[1].(string)
			}
			return AliasExpression{expr, as}
		},
	))

	sys.Install("WhereClause", Map(
		Sequence(
			Word("WHERE"),
			sys.Parser("ScalarExpr"),
		),
		func(matches any) any {
			ms := matches.([]any)
			expr := ms[1].(Expr)
			return &WhereClause{expr: expr}
		},
	))

	sys.Install("GroupByClause", Map(
		Sequence(Word("GROUP"), Word("BY"), CommaSeparated(sys.Parser("ScalarExpr"))),
		func(matches any) any {
			ms := matches.([]any)
			exprs := ms[2].([]any)
			result := make([]Expr, len(exprs))
			for i, expr := range exprs {
				result[i] = expr.(Expr)
			}
			return &GroupByClause{exprs: result}
		},
	))

	sys.Install("HavingClause", Map(
		Sequence(
			Word("HAVING"),
			sys.Parser("ScalarExpr"),
		),
		func(matches any) any {
			ms := matches.([]any)
			expr := ms[1].(Expr)
			return &HavingClause{expr: expr}
		},
	))

	sys.Install("OrderByExpression", Map(
		Sequence(
			sys.Parser("ScalarExpr"),
			Optional(OneOf(Word("DESC"), Word("ASC"))),
			Optional(
				Sequence(
					Word("NULLS"),
					OneOf(Word("FIRST"), Word("LAST")),
				),
			),
		),
		func(matches any) any {
			ms := matches.([]any)
			expr := ms[0].(Expr)
			desc := false
			if ms[1] != nil {
				desc = ms[1].(string) == "DESC"
			}
			nulls := ""
			if ms[2] != nil {
				nulls = strings.ToLower(ms[2].([]any)[1].(string))
			}
			return &OrderByExpression{
				expr:  expr,
				desc:  desc,
				nulls: nulls,
			}
		},
	))

	sys.Install("OrderByClause", Map(
		Sequence(
			Word("ORDER"),
			Word("BY"),
			CommaSeparated(sys.Parser("OrderByExpression")),
		),
		func(matches any) any {
			ms := matches.([]any)
			exprs := ms[2].([]any)
			result := make([]*OrderByExpression, len(exprs))
			for i, expr := range exprs {
				result[i] = expr.(*OrderByExpression)
			}
			return &OrderByClause{exprs: result}
		},
	))

	sys.Install("ScalarExpr", PrecExpr(sys, len(OperatorsByPrecedence)))

	sys.Install("Literal", OneOf(Number, Column))
}

type ArrayExpr []Expr

func (a *ArrayExpr) Format(buf *bytes.Buffer) {
	buf.WriteString("ARRAY[")
	for i, expr := range *a {
		if i > 0 {
			buf.WriteString(", ")
		}
		expr.Format(buf)
	}
	buf.WriteString("]")
}

func InstallArrayLiteral(sys *System) {
	sys.Install("ArrayLiteral", func(input string) (any, string, error) {
		return Map(
			Sequence(Word("ARRAY["), CommaSeparated(sys.Parser("ScalarExpr")), Word("]")),
			func(matches any) any {
				ms := matches.([]any)
				exprs := ms[1].([]any)
				result := make(ArrayExpr, len(exprs))
				for i, expr := range exprs {
					result[i] = expr.(Expr)
				}
				return &result
			},
		)(input)
	})

	sys.InstallFront("Literal", sys.Parser("ArrayLiteral"))
}

func (sys *System) RunCommand(command string) {
	fmt.Printf("> %s\n", command)
	result, rest, err := sys.Parser("SelectStmt")(command)
	if err != nil || len(rest) > 0 {
		fmt.Printf("error: %v\n\n", err)
		return
	}
	var out bytes.Buffer
	out.WriteString("result: ")
	result.(AstNode).Format(&out)
	fmt.Println(out.String())
	fmt.Println()
}

func main() {
	sys := NewSystem()

	sys.RunCommand("SELECT 1 FROM b")

	InstallSelect(sys)
	fmt.Println("installed select extension")
	fmt.Println()

	sys.RunCommand("SELECT 1 FROM b")
	sys.RunCommand("SELECT ARRAY[1, 2, 3] FROM b")

	InstallArrayLiteral(sys)
	fmt.Println("installed array literal extension")
	fmt.Println()

	sys.RunCommand("SELECT ARRAY[1, 2, 3] FROM b")
}
