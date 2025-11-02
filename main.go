package main

/*

NOTE(@hadydotai): Alright so the idea is pretty simple. Values will fall into an ordered series of states:

Available -> Maybe -> Consumed

Using a value will always require it to be Available, I'm not really sure how to quantify the term `Use` but I suppose
the best way to describe it is to say, for any value X, where X appears in any expression, if X is not Available then it's an error.

Expressions here is a bit of an umbrella term, that encompasses statements as defined by any language that carries a distinction
between expressions and statements. Irrespective of that, Using X, we'll shorthand it as `Use(X)` requires Available(X) to assert
to true.

Right moving on, the Consumed state is easy, any function that marks a param as `consume` will require `Available(X)`,
transitioning X to `Consumed(X)`. This will look like that:

Apply(Available(X)) -> Consumed(X)

Finally the Maybe state, absolute PITA. Maybe is my idea of capturing edge cases as a variant. I need to cover the following
edge cases:

- Field access on a container (array, map, struct)
- Flow graph merge points (read: control structures, eg. conditionals, loops, switch-cases, exceptions)
- Patterns (callbacks, function pointers, closures)

So, field access. The issue is I would have no guarantee that the rest of the container remains valid if I
`Apply(Available(field)) -> Consumed(field)` I think this will require me to add some form of container tracking,
then decide on what it means for the container. I'm thinking of a usecase where I have a struct that maintains its own
arena. At some point during an allocation op I might want to grow the arena, potentially relocate it, making the arena
an unstable reference. What does this mean for the neighboring fields, does this invalidate the struct?

Flow graph merge points, is an interesting issue. I think the best way to visualize the general problem is with conditionals:

if !(arena_len(X) - arena_cap(X) < sizeof(Obj)) {
	arena_expand(X, sizeof(Obj) * 2);
}
Obj(obj) = arena_alloc(X, sizeof(Obj)); // <-- merge point

So the issue here is, at the point we merge back the execution from branching, we have no guarantee that X is no longer consumed.
The execution could have branched, arena_expand is defined like this:

fn arena_expand(consumes arena: Arena_C, target_size: ui32);

At one branch of the flow graph we've triggered an Apply(Available(X)) -> Consumed(X)
but an adjacent branch still sees Available(X). If we calculate the new state of X at the joining point which we'll call
`Meet(X)` then we'd have Consumed(X^CondBranch) + Available(X^JoinBranch) = Maybe(X)

The obvious solution here is to actually redefine X, like this:

if !(arena_len(X) - arena_cap(X) < sizeof(Obj)) {
	X = arena_expand(X, sizeof(Obj) * 2);
}
Obj(obj) = arena_alloc(X, sizeof(Obj)); // <-- merge point

At the merge point, the `Meet(X) = Available(X^CondBranch) + Available(X^JoinBranch) = Available(X)` X got a new lease of life.

*/

import (
	"errors"
	"fmt"
	"os"
	"strings"

	"github.com/alecthomas/participle/v2"
	"github.com/alecthomas/participle/v2/lexer"
)

var (
	lex = lexer.MustSimple([]lexer.SimpleRule{
		{Name: "Comment", Pattern: `//[^\n]*`},
		{Name: "BlockComment", Pattern: `/\*([^*]|\*+[^*/])*\*+/`},
		{Name: "String", Pattern: `"(\\"|[^"])*"`},
		{Name: "Number", Pattern: `[-+]?(\d*\.)?\d+`},
		{Name: "Ident", Pattern: `[a-zA-Z_]\w*`},
		{Name: "Punct", Pattern: `->|[-+*/%.,;:=(){}<>]|==|<=|>=|\*\*`},
		{Name: "EOL", Pattern: `[\n\r]+`},
		{Name: "Whitespace", Pattern: `[ \t]+`},
	})

	parser = participle.MustBuild[Program](
		participle.Lexer(lex),
		participle.Elide("Whitespace", "Comment", "BlockComment", "EOL"),
		participle.Unquote(),
	)
)

type Program struct {
	Funcs []*Func `@@*`
}

type Func struct {
	Pos        lexer.Position
	Name       string   `"fn" @Ident`
	Params     []*Param `"(" (@@ ("," @@)* )? ")"`
	ReturnType *string  `( ":" @Ident )?`
	Body       *Block   `@@`
}

type Param struct {
	Pos      lexer.Position
	Consumes bool    `@"consumes"?`
	Name     string  `@Ident`
	Type     *string `(":" @Ident)?`
}

type Block struct {
	Pos   lexer.Position
	Stmts []*Stmt `"{" @@* "}"`
}

type Stmt struct {
	Pos        lexer.Position
	Assignment *Assignment `@@ ";"`
	If         *If         `| @@`
	While      *While      `| @@`
	Return     *Return     `| @@ ";"`
	Expr       *Expr       `| @@ ";"`
}

type Assignment struct {
	Pos         lexer.Position
	Declaration bool   `@"let"?`
	Name        string `@Ident`
	Expr        *Expr  `"=" @@`
}

type If struct {
	Pos lexer.Position
	// NOTE(@hadydotai): A handy little thing from participle, a positive lookahead group that matches further input
	// without consuming it, we only match the head of the If if we have a block following it
	Cond *Expr  `"if" @@ (?= "{")`
	Then *Block `@@`
	Else *Block `("else" @@)?`
}

type While struct {
	Pos  lexer.Position
	Cond *Expr  `"while" @@ (?= "{")`
	Body *Block `@@`
}

type Return struct {
	Pos  lexer.Position
	Expr *Expr `"return" (@@)?`
}

type Expr struct {
	Pos        lexer.Position
	Call       *Call       `@@`
	Assignment *Assignment `| @@`
	Ident      *string     `| @Ident`
	Number     *string     `| @Number`
}

type Call struct {
	Pos    lexer.Position
	Callee string  `@Ident "("`
	Args   []*Expr `(@@ ("," @@)* )? ")"`
}

type binding struct {
	id   int
	name string
	pos  lexer.Position
}

type valueState uint8

const (
	Consumed valueState = iota
	Maybe
	Available
)

func (s valueState) String() string {
	switch s {
	case Available:
		return "Available"
	case Maybe:
		return "Maybe"
	case Consumed:
		return "Consumed"
	default:
		panic(fmt.Sprintf("!!shouldn't be here!! value state unknown: %d", int(s)))
	}
}

func meet(valA, valB valueState) valueState {
	// lattice logic: Available > Maybe > Consumed => meet is the min
	if valA < valB {
		return valA
	}
	return valB
}

type env map[*binding]valueState

func newEnv() env { return make(env) }
func (e env) clone() env {
	new := newEnv()
	for k, v := range e {
		new[k] = v
	}
	return new
}
func (e env) get(b *binding) valueState {
	if v, ok := e[b]; ok {
		return v
	}
	return Consumed
}
func (e env) set(b *binding, s valueState) { e[b] = s }
func (e env) meet(other env) env {
	out := newEnv()
	seen := map[*binding]struct{}{}
	for k := range e {
		seen[k] = struct{}{}
	}
	for k := range other {
		seen[k] = struct{}{}
	}
	for k := range seen {
		out[k] = meet(e.get(k), other.get(k))
	}
	return out
}

func (e env) equal(other env) bool {
	if len(e) != len(other) {
		return false
	}
	for k, v := range e {
		if other.get(k) != v {
			return false
		}
	}
	return true
}

type scope struct {
	parent *scope
	binds  map[string]*binding
}

type scopes struct {
	top    *scope
	nextID int
}

func newScopes() *scopes {
	return &scopes{top: &scope{binds: make(map[string]*binding)}}
}

func (s *scopes) push() {
	s.top = &scope{parent: s.top, binds: make(map[string]*binding)}
}

func (s *scopes) pop() []*binding {
	out := make([]*binding, 0, len(s.top.binds))
	for _, b := range s.top.binds {
		out = append(out, b)
	}
	s.top = s.top.parent
	return out
}

func (s *scopes) declare(name string, pos lexer.Position) *binding {
	b := &binding{id: s.nextID, name: name, pos: pos}
	s.nextID++
	s.top.binds[name] = b
	return b
}

func (s *scopes) resolve(name string) (*binding, bool) {
	for sc := s.top; sc != nil; sc = sc.parent {
		if b, ok := sc.binds[name]; ok {
			return b, true
		}
	}
	return nil, false
}

type fnSig struct {
	name     string
	consumes []bool // consume mask
}

type fnTable map[string]*fnSig

func newFnTable() fnTable {
	return make(fnTable)
}

func (ft fnTable) add(name string, consumes []bool) {
	ft[name] = &fnSig{name: name, consumes: consumes}
}

func (ft fnTable) get(name string, argc int) *fnSig {
	if sig, ok := ft[name]; ok {
		return sig
	}
	// NOTE(@hadydotai): this is an edge case that I think I need to handle in a type check pass
	// but at this point we actually don't know the callee, so we're assuming that we don't have
	// any consuming params, which is where fnTable.get will be triggered for. Also, maybe the name is too generic.
	// This is afterall, a mapping for consuming functions, not really a dispatch table.
	return &fnSig{name: name, consumes: make([]bool, argc)}
}

type checker struct {
	funcs  fnTable
	errors []string
	scopes *scopes
	// NOTE(@hadydotai): for diagnostics, I really hate this. I think I will replace it at some point with the offset
	// lexer.Position already carries this, I don't need to lift this off the AST everywhere later. Offset will do fine.
	consumeSites map[*binding]lexer.Position
}

func newChecker() *checker {
	ft := newFnTable()

	// NOTE(@hadydotai): I want some intrinsic sentinel values/markers which don't do anything really but force
	// a value to be in some state. Only one for now, can't think of another, also not sure if this is useful but
	// will make testing easy for now until I go into codegen with QBE.
	ft.add("consume", []bool{true})
	return &checker{
		funcs:        ft,
		scopes:       newScopes(),
		consumeSites: make(map[*binding]lexer.Position),
	}
}

func short(longstr string) string {
	if longstr == "" {
		return "<src>"
	}
	if i := strings.LastIndexByte(longstr, '/'); i >= 0 {
		return longstr[i+1:]
	}
	return longstr
}

func (c *checker) err(pos lexer.Position, msg string) {
	c.errors = append(c.errors, fmt.Sprintf("%s:%d:%d: %s", short(pos.Filename), pos.Line, pos.Column, msg))
}

func (c *checker) checkExpr(e *Expr, in env) env {
	switch {
	case e.Ident != nil:
		b, ok := c.scopes.resolve(*e.Ident)
		if !ok {
			c.err(e.Pos, "use of undeclared identifier "+*e.Ident)
			return in
		}
		state := in.get(b)
		if state != Available {
			msg := "use of '" + b.name + "' after it may have been consumed"
			if state == Consumed {
				msg = "use of '" + b.name + "' after it was consumed"
			}
			if pos, ok := c.consumeSites[b]; ok {
				msg += fmt.Sprintf(" \n(consumed at %s:%d:%d)", short(pos.Filename), pos.Line, pos.Column)
			}
			c.err(e.Pos, msg)
		}
		return in
	case e.Call != nil:
		return c.checkCall(e.Call, in)
	default:
		// literals and other types of expressions should have no effect, right now only numbers are in question.
		return in
	}
}

func (c *checker) checkCall(call *Call, in env) env {
	env := in.clone()
	argc := len(call.Args)
	sig := c.funcs.get(call.Callee, argc)
	for i := 0; i < argc; i++ {
		arg := call.Args[i]
		consumes := i < len(sig.consumes) && sig.consumes[i]
		if consumes {
			// NOTE(@hadydotai): This is probably where I would need to handle field access and container groups
			if arg.Ident == nil {
				c.err(arg.Pos, fmt.Sprintf("argument %d to '%s' is consuming. We only support bare identifiers", i+1, call.Callee))
				// We still need to analzye the rest of expression variants
				env = c.checkExpr(arg, env)
				continue
			}

			name := *arg.Ident
			b, ok := c.scopes.resolve(name)
			if !ok {
				c.err(arg.Pos, "consuming undeclared identifier "+name)
				continue
			}
			state := env.get(b)
			if state != Available {
				msg := fmt.Sprintf("passing '%s' to consuming param of '%s' but it's %s", name, call.Callee, state)
				if pos, ok := c.consumeSites[b]; ok {
					msg += fmt.Sprintf(" \n(consumed at %s:%d:%d)", short(pos.Filename), pos.Line, pos.Column)
				}
				c.err(arg.Pos, msg)
			}
			// consume it
			env.set(b, Consumed)
			c.consumeSites[b] = arg.Pos
		} else {
			env = c.checkExpr(arg, env)
		}
	}
	// NOTE(@hadydotai): Calls are expressions that return a value, we need to handle this later, for now we'll ignore it
	return env
}

func (c *checker) checkBlock(block *Block, in env) env {
	c.scopes.push()
	defer c.scopes.pop()

	env := in.clone()
	for _, stmt := range block.Stmts {
		env = c.checkStmt(stmt, env)
	}

	// NOTE(@hadydotai): Do I need to filter out local bindings? None of them will hit on any name resolutions later
	// but maybe it's cleaner to actually just not return the env with the locals. I suspect I'll have an issue or rather
	// some annoyance when doing codegen.
	return env
}

func (c *checker) checkStmt(stmt *Stmt, in env) env {
	switch {
	case stmt.Assignment != nil:
		// NOTE(@hadydotai): we need to check if an assignment is also a declaration.
		// Here I should also be checking if we're re-declaring this.
		if stmt.Assignment.Declaration {
			b := c.scopes.declare(stmt.Assignment.Name, stmt.Assignment.Pos)
			env := c.checkExpr(stmt.Assignment.Expr, in.clone())
			env.set(b, Available)
			return env
		}
		env := c.checkExpr(stmt.Assignment.Expr, in.clone())
		b, ok := c.scopes.resolve(stmt.Assignment.Name)
		if !ok {
			c.err(stmt.Assignment.Pos, "assignment to undeclared identifier "+stmt.Assignment.Name)
			return env
		}
		env.set(b, Available)
		return env
	case stmt.If != nil:
		condOut := c.checkExpr(stmt.If.Cond, in.clone())
		thenOut := c.checkBlock(stmt.If.Then, condOut.clone())

		var elseOut env
		if stmt.If.Else != nil {
			elseOut = c.checkBlock(stmt.If.Else, condOut.clone())
		} else {
			elseOut = in.clone()
		}
		return thenOut.meet(elseOut)
	case stmt.While != nil:
		condOut := c.checkExpr(stmt.While.Cond, in.clone())
		bodyOut := c.checkBlock(stmt.While.Body, condOut.clone())
		return in.meet(bodyOut)
	case stmt.Return != nil:
		env := in.clone()
		if stmt.Return.Expr != nil {
			env = c.checkExpr(stmt.Return.Expr, env)
		}
		return env
	case stmt.Expr != nil:
		return c.checkExpr(stmt.Expr, in.clone())
	default:
		return in
	}
}

func (c *checker) checkFunc(f *Func) {
	c.scopes.push()
	defer c.scopes.pop()

	env := newEnv()

	for _, p := range f.Params {
		b := c.scopes.declare(p.Name, p.Pos)
		env.set(b, Available)
	}

	c.checkBlock(f.Body, env)
}

func (c *checker) check(prog *Program) []string {
	for _, f := range prog.Funcs {
		mask := make([]bool, len(f.Params))
		for i, p := range f.Params {
			mask[i] = p.Consumes
		}
		c.funcs.add(f.Name, mask)
	}

	for _, f := range prog.Funcs {
		c.checkFunc(f)
	}
	return c.errors
}

func readInput(args []string) (string, string, error) {
	if len(args) == 0 || (len(args) == 1 && args[0] == "-") {
		stdin, err := os.ReadFile("/dev/stdin")
		if err != nil {
			return "", "", err
		}
		return string(stdin), "<src>", nil
	}
	if len(args) != 1 {
		return "", "", errors.New("usage: litla <file> | -")
	}
	b, err := os.ReadFile(args[0])
	if err != nil {
		return "", "", err
	}
	return string(b), args[0], nil
}

func main() {
	src, filename, err := readInput(os.Args[1:])
	if err != nil {
		fmt.Fprintln(os.Stderr, "error: ", err)
		os.Exit(2)
	}
	ast, err := parser.Parse(filename, strings.NewReader(src))
	if err != nil {
		fmt.Fprintf(os.Stderr, "parse error: %s", err)
		os.Exit(2)
	}
	checker := newChecker()
	errs := checker.check(ast)
	if len(errs) > 0 {
		for _, e := range errs {
			fmt.Fprintln(os.Stderr, e)
		}
		os.Exit(1)
	}

	fmt.Println("A-OK")
}
