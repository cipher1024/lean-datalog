-- Term : Var <text> | Sym <text>
-- Vars must start with Uppercase, eg: X, Foo, Bar
-- Syms start with lowercase, eg: mary, bob, brown

-- Atom : Name <text>, args : [Term]
-- eg: ancestor(mary, bob)

-- Rule : Head : Atom, Body : [Atom]

-- safety rule(s):
-- - Every variable in a rule _must_ occur in a positive, non-negatived position in the body
-- This ensures queries/results of a program are finite

-- what are positive / negative positions? Yeah... sorry, slightly informal description. The formal one is a bit longer. Thinking...

-- in the mean time, I'm committing this file on git and moving it to
-- its own Lean project

namespace datalog

def ident := string -- start with upper case
def sym := string   -- start with lower case

inductive term
| var : ident → term
| sym : sym → term

structure atom :=
(name : string)
(args : list term)

structure rule :=
(head : atom)
(body : list atom)

-- how do you like Lean in the cloud?
-- it's not emacs, but it will do ;)
-- indubitably!

-- do you want to start with a parser or just processing rules?
-- we could write a small example which we use as a springboard to 
-- write the interpretter
-- Yeah... I tihnk we're almost done with the definitions.
-- From there whether to parse or interpret is a matter of taste