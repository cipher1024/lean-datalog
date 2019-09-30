/-
Copyright (c) 2019 Simon Hudon and James King. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author(s): Simon Hudon and James King
-/

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

end datalog
