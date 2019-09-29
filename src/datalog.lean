/-
Copyright (c) 2019 Simon Hudon and James King. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author(s): Simon Hudon and James King
-/

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

-- If you would like formal definitions: http://webdam.inria.fr/Alice/pdfs/Chapter-12.pdf
-- Specifically, 12.1.1
-- thanks

-- eg of unsafe rules:
-- s(X) :- r(Y). -- X doesn't appear in the body
-- s(X) :- r(Y), !r(X) -- X is negated in the body (we haven't discussed negation yet, but it's the opposite of positive position)
-- if we had s(X) :- r(Y), !r(X), p(X), would it make it safe?
-- I think that would be unsafe.. every variable in the head of the rule must appear (only) in a non-negative in the body
-- A lemma would be that this ensures that every query terminates :)
-- ok, I'll try to write a formal definition
-- Cool, we can try to prove that
-- The book does have a proof but it's probably not formally verified ;)

-- Cool, definition wise we also need a knowledge base/database composed of facts and rules
-- then a program is a rule and a knowledge base which, when evaluated, produces a table of facts that satisfy the atom predicate
-- eg: ? ancestor(mary, X)
-- would find, given the facts and rules in the database
-- all of the ancestors of mary
-- eg: ? ancestor(X, mary)
-- with the right rules, would find all of the people for whom mary is their
-- ancestor

-- For a practical application in package manangement we can take a list
-- of input packages and compute the list of dependencies those packages depend on
-- so that we can download them all when compiling a lean project. :)

-- nice! Thanks! Could we say that every atom can be positive or negative?
-- I think so; negation can be useful in a rule body
-- can it make sense on a head?
-- not sure about the head, but we can put negation on an atom in a body to negate its meaning
-- eg: pred(X, Y) :- foo(X), bar(Y), ! baz(X)
-- eg: pred(X, Y) <- foo(X) /\ bar(Y) /\ not baz(X)
-- in other words, the body of a rule is the conjuction of all atoms of the body

-- is it an issue that Y does not appear in the head?

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
(body : list (bool × atom))

structure program :=
(facts   : list atom)
(rules   : list rule)
(queries : list rule)

def term.vars : term → set ident
| (term.var v) := {v}
| (term.sym _) := ∅

def big_union {α β γ} (S : γ) [has_mem α γ] (f : α → set β) : set β :=
λ x : β, ∃ a ∈ S, x ∈ f a

notation `⋃ ` binder `, ` r:(scoped p, big_union set.univ p) := r
notation `⋃ ` binder ` ∈ ` S `, ` r:(scoped p, big_union S p) := r

def atom.vars (a : atom) : set ident :=
⋃ x ∈ a.args, x.vars

def rule.neg_vars (r : rule) : set ident :=
⋃ x ∈ r.body, if x.1 then ∅ else x.2.vars

-- still following?
-- yes, sorry bio.
-- I will have to get going in about 15-20 mins though :)

-- no worries. Ok, good to know. We can come back here later. And in the mean time, I can take care of pushing it to a repo. Or did you do that already?
-- Have not, but a repo would be good. A
-- I can take care of that
-- an attribution would be nice. :)
-- sure. Done

def safe (r : rule) : Prop :=
(r.head.vars ⊆ ⋃ a ∈ r.body, a.2.vars) ∧
r.neg_vars ∩ r.head.vars = ∅

def fact := sym × list sym

def query := bool × atom

def fact.unify : fact → query → bool := sorry

def rule.unify : rule → query → set query := sorry

inductive run : set fact → -- result of the query
                set fact → -- input data base
                set rule → -- set of rules
                set query → -- queries
                Prop
| nil (db : set fact) (rs : set rule) : run ∅ db rs ∅
| step  (r db : set fact) (rs : set rule)
        (qs : set query) (cq : query) :
      run r db rs ((⋃ r ∈ rs, r.unify cq) ∪ qs) →
      run ({ k ∈ db | k.unify cq } ∪ r) db rs ({cq} ∪ qs)

-- two lemmas could be proved: the result set is unique for a given
-- set of input and a safe set of rules always terminates

-- super! I added a structure to encapsulate the parts of a program.
-- In the Haskell version I was going to go with a quasiquoter to enable
-- writing the program in a datalog like syntax but... it's also easy to embed in the
-- host language

-- however I must depart! groceries and kid time. :)

-- You must feed those kids! Depart at once! I'll also leave it alone for now. It will be easier for you to follow.

-- As for a quasiquoter, we can do similar things in Lean, you shall see!


-- Send me the repo link and I'll poke at it tonight. :)

-- how do you like Lean in the cloud?
-- it's not emacs, but it will do ;)
-- indubitably!

-- do you want to start with a parser or just processing rules?
-- we could write a small example which we use as a springboard to 
-- write the interpretter
-- Yeah... I tihnk we're almost done with the definitions.
-- From there whether to parse or interpret is a matter of taste


end datalog
