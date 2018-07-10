@[reducible] meta def debruijn := nat

meta inductive folpred
| P : folpred
| T : folpred 
| eq : folpred

meta inductive folterm
| const : name → folterm
| lconst : name → name → folterm
| prf : folterm
| var : debruijn → folterm
| app : folterm → folterm → folterm

meta inductive folform 
| P : folterm → folform
| T : folterm → folterm → folform
| eq : folterm → folterm → folform
| bottom : folform
| top : folform
| neg : folform → folform
| imp : folform → folform → folform
| iff : folform → folform → folform
| conj : folform → folform → folform
| disj : folform → folform → folform
| all : name → name → folform → folform
| exist : name → name → folform → folform

meta structure introduced_constant :=
(n : name) (e : expr) -- name and type

meta structure axioma :=
(n : name) (f : folform)

meta structure hammer_state :=
(axiomas : list axioma)
(introduced_constants : list introduced_constant)

meta def hammer_tactic :=
state_t hammer_state tactic

section tptp
open format

-- axiom is a reserved word in Lean
meta inductive role
| axioma : role
| conjecture : role

meta def role.to_format : role → format
| role.axioma := to_fmt "axiom"
| role.conjecture := to_fmt "conjecture"

meta instance : has_to_format role :=
⟨role.to_format⟩

meta def folform.to_format_collect_vars : folform → list name → (list name × folform) 
| (folform.all n n1 e@(folform.all _ _ _)) xs := folform.to_format_collect_vars e (n :: xs)
| (folform.exist n n1 e@(folform.exist _ _ _)) xs := folform.to_format_collect_vars e (n :: xs)
| (folform.all n n1 e) xs := ((n :: xs).reverse, e)
| (folform.exist n n1 e) xs := ((n :: xs).reverse, e)
| e@_ xs := (xs.reverse, e)

meta def name_to_id_format : name → format
| n := "'" ++ to_fmt n ++ "'"

meta def names_to_id_format : list name → nat → list format
| (x::xs) d := ("V" ++ to_fmt (d+1) ++ " /* " ++ to_fmt x ++ " */") :: names_to_id_format xs (d+1)
| [] d := []

meta def mygroup : format → format := id

meta def folterm.to_format : folterm → nat → format
| (folterm.const n) _ := "'" ++ to_fmt n ++ "'"
| (folterm.lconst n _) _ := "'" ++ to_fmt n ++ "'"
| (folterm.prf) _ := "prf"
| (folterm.var i) depth := "V" ++ to_fmt (depth - i)
| (folterm.app t u) depth :=
  "a(" ++ t.to_format depth ++ "," ++
    (mygroup $ nest 2 $ line ++ u.to_format depth) ++ ")"

meta def folform.to_format_aux : folform → nat → format
| e@(folform.all n n1 f) depth :=
  let (ys, g) := folform.to_format_collect_vars e [] in
  let ys' := names_to_id_format ys depth in
    "! [" ++ 
    (mygroup $ nest 3 $ (join $ list.intersperse ("," ++ line) ys') ++ "] :") ++
    (mygroup $ nest 2 $ line ++ "(" ++ (mygroup $ nest 1 $ g.to_format_aux $ depth + ys.length)) ++ ")"
| e@(folform.exist n n1 f) depth :=
  let (ys, g) := folform.to_format_collect_vars e [] in
  let ys' := names_to_id_format ys depth in
    "? [" ++ 
    (mygroup $ nest 3 $ (join $ list.intersperse ("," ++ line) ys') ++ "] :") ++
    (mygroup $ nest 2 $ line ++ "(" ++ (mygroup $ nest 1 $ g.to_format_aux $ depth + ys.length)) ++ ")"
| folform.bottom _ := to_fmt "$false"
| folform.top _ := to_fmt "$true"
| (folform.P t) depth :=
  "p(" ++ (nest 2 $ t.to_format depth) ++ ")"
| (folform.T t u) depth :=
  "t(" ++ (mygroup $ nest 2 $ t.to_format depth ++ "," ++ line ++ u.to_format depth ++ ")")
| (folform.eq t u) depth :=
  "(" ++ (nest 1 $ t.to_format depth ++
    (mygroup $ line ++ "= " ++ (nest 2 $ u.to_format depth ++ ")")))
| (folform.neg f) depth := 
  match f with
  | (folform.eq t u) :=
    "(" ++ (nest 1 $ t.to_format depth ++
      (mygroup $ line ++ "!= " ++ (nest 3 $ u.to_format depth ++ ")")))
  | _ := "~(" ++ (nest 2 $ f.to_format_aux depth ++ ")")
  end
| (folform.imp f g) depth :=
  "(" ++ (nest 1 $ f.to_format_aux depth ++ ")") ++ 
    (mygroup $ line ++ (nest 4 $ "=> (" ++ g.to_format_aux depth ++ ")"))
| (folform.iff f g) depth :=
  "(" ++ (nest 1 $ f.to_format_aux depth ++ ")") ++
    (mygroup $ line ++ (nest 5 $ "<=> (" ++ g.to_format_aux depth ++ ")"))
| (folform.conj f g) depth :=
  "(" ++ (nest 1 $ f.to_format_aux depth ++ ")") ++
    (mygroup $ line ++ (nest 3 $ "& (" ++ g.to_format_aux depth ++ ")"))
| (folform.disj f g) depth :=
  "(" ++ (nest 1 $ f.to_format_aux depth ++ ")") ++
    (mygroup $ line ++ (nest 3 $ "| (" ++ g.to_format_aux depth ++ ")"))
     
meta def folform.to_format (f : folform) : format := folform.to_format_aux f 0

meta instance : has_to_format folform :=
⟨folform.to_format⟩

meta def to_fof : string → role → folform → format
| id r f :=
to_fmt "fof("
++ (mygroup $ nest 4 $ join $ list.intersperse ("," ++ line) $
  [to_fmt id, to_fmt r, "(" ++ (mygroup $ nest 1 $ to_fmt f) ++ ")"]) ++ to_fmt ")."
  
meta def to_tptp : list axioma → folform → format
| (⟨n, f⟩::as) conjecture := 
  to_fof ("'" ++ to_string n ++ "'") role.axioma f
     ++ line
     ++ line
     ++ to_tptp as conjecture
| [] conjecture := to_fof "'problem_conjecture'" role.conjecture conjecture


meta def myformat {α : Type} [has_to_format α] : list α → format
| [] := to_fmt "[]"
| xs := to_fmt "[" ++ mygroup (format.nest 1 $ format.join $ list.intersperse ("," ++ format.line) $ xs.map to_fmt) ++ to_fmt "]"

end tptp 





meta def name.repr : name → string
| name.anonymous := "name.anonymous"
| (name.mk_numeral n p) := "(name.mk_numeral " ++ repr n ++ " " ++ name.repr p ++ ")"
| (name.mk_string s p) := "(name.mk_string " ++ repr s ++ " " ++ name.repr p ++ ")"

meta instance : has_repr name :=
⟨name.repr⟩

meta def folterm.repr : folterm → string 
| (folterm.const n) := "(folterm.const " ++ repr n ++ ")"
| (folterm.lconst n n1) := "(folterm.lconst " ++ repr n ++ " " ++ repr n1 ++ ")"
| folterm.prf := "folterm.prf"
| (folterm.var n) := "(folterm.var " ++ repr n ++ ")"
| (folterm.app t1 t2) := "(folterm.app " ++ folterm.repr t1 ++ " " ++ folterm.repr t2 ++ ")"

meta instance : has_repr folterm :=
⟨folterm.repr⟩

meta def folpred.repr : folpred → string
| folpred.P := "folpred.P"
| folpred.T := "folpred.T"
| folpred.eq := "folpred.eq"

meta instance : has_repr folpred :=
⟨folpred.repr⟩

meta def folform.repr : folform → string
| (folform.P t) := "(folform.P " ++ repr t ++ ")"
| (folform.T t u) := "(folform.T " ++ repr t ++  " " ++ repr u ++ ")"
| (folform.eq t u) := "(folform.eq " ++ repr t ++  " " ++ repr u ++ ")"
| folform.bottom := "folform.bottom"
| folform.top := "folform.top"
| (folform.neg f) := "(folform.neg " ++ folform.repr f ++ ")"
| (folform.imp f g) := "(folform.imp " ++ folform.repr f ++ " " ++ folform.repr g ++ ")"
| (folform.iff f g) := "(folform.iff " ++ folform.repr f ++ " " ++ folform.repr g ++ ")"
| (folform.conj f g) := "(folform.conj " ++ folform.repr f ++ " " ++ folform.repr g ++ ")"
| (folform.disj f g) := "(folform.disj " ++ folform.repr f ++ " " ++ folform.repr g ++ ")"
| (folform.all n n1 f) := "(folform.all " ++ repr n ++ " " ++ repr n1 ++ " " ++ folform.repr f ++ ")"
| (folform.exist n n1 f) := "(folform.exist " ++ repr n ++ " " ++ repr n1 ++ " " ++ folform.repr f ++ ")"

meta instance : has_repr folform :=
⟨folform.repr⟩

meta def example_formula : folform :=
folform.all `h1 `h1 $ folform.all `h2 `h2 $
  folform.neg $
  folform.iff
    (folform.conj
      (folform.neg $ folform.eq (folterm.var 0) (folterm.var 1)) 
      (folform.eq (folterm.var 0) (folterm.var 1)) )
    (folform.imp
      (folform.conj (folform.P $ folterm.var 0) (folform.disj (folform.P $ folterm.var 0) (folform.P $ folterm.var 1)))
      (folform.T (folterm.var 0) (folterm.app (folterm.var 1) (folterm.var 0))))


--set_option pp.indent 2
--set_option pp.colors true
--set_option pp.width 1

#eval tactic.trace $ to_fof "example_formula" role.axioma example_formula   



meta instance : monad hammer_tactic :=
state_t.monad 

meta instance (α : Type) : has_coe (tactic α) (hammer_tactic α) :=
⟨state_t.lift⟩


meta def using_hammer {α} (t : hammer_tactic α) : tactic (α × hammer_state) :=
do let ss := hammer_state.mk [] [],
   state_t.run t ss -- (do a ← t, return a) 

meta def when' (c : Prop) [decidable c] (tac : hammer_tactic unit) : hammer_tactic unit :=
if c then tac else tactic.skip

meta def lives_in_prop_p (e : expr) : hammer_tactic bool :=
do tp ← tactic.infer_type e,
   return (if eq tp (expr.sort level.zero) then tt else ff)

meta def add_axiom (n : name) (axioma : folform) : hammer_tactic unit :=
do state_t.modify (fun state, {state with axiomas := ⟨n, axioma⟩ :: state.axiomas})

meta def add_constant (n : name) (e : expr) : hammer_tactic unit :=
do state_t.modify (fun state, {state with introduced_constants := ⟨n, e⟩ :: state.introduced_constants })

meta def doforget {α : Type} (t₁ : tactic α)  : tactic α :=
λ s, interaction_monad.result.cases_on (t₁ s)
  (λ r _, interaction_monad.result.success r s)
  (λ e p _, interaction_monad.result.exception e p s)

meta def doforget1 {α : Type} (t₁ : hammer_tactic α) : hammer_tactic α :=
state_t.mk (λ x, do ⟨a, b⟩ ← doforget (t₁.run x),
                    return ⟨a, b⟩) 

-- might want to do something different
meta def mk_fresh_name : tactic name := tactic.mk_fresh_name

meta def body_of : expr → hammer_tactic (expr × name)
| e@(expr.pi n bi d b) := do id ← mk_fresh_name,
                             let x := expr.local_const id n bi d,
                             return $ prod.mk (expr.instantiate_var b x) id
| e@(expr.lam n bi d b) := do id ← mk_fresh_name,
                             let x := expr.local_const id n bi d,
                             return $ prod.mk (expr.instantiate_var b x) id                           
| e := return (e, name.anonymous)
                    
meta def folterm.abstract_locals_core : folterm → ℕ → list name → folterm
| e@(folterm.lconst n n1) d ln :=
  list.foldl
    (λ e' n', if n = n' then folterm.var $ d + ln.reverse.find_index (= n) else e')
    e
    ln
| (folterm.app t1 t2) d ln := folterm.app (t1.abstract_locals_core d ln) (t2.abstract_locals_core d ln)
| e d ln := e

meta def folterm.abstract_locals : folterm → list name → folterm := λ f l, f.abstract_locals_core 0 l

meta def folform.abstract_locals_core : folform → nat → list name → folform
| e@(folform.P t) d ln := folform.P $ t.abstract_locals_core d ln
| e@(folform.T t u) d ln := folform.T (t.abstract_locals_core d ln) (u.abstract_locals_core d ln)
| e@(folform.eq t u) d ln := folform.eq (t.abstract_locals_core d ln) (u.abstract_locals_core d ln)
| e@(folform.neg f) d ln := f.abstract_locals_core d ln
| e@(folform.imp f1 f2) d ln := folform.imp (f1.abstract_locals_core d ln) (f2.abstract_locals_core d ln)
| e@(folform.iff f1 f2) d ln := folform.iff (f1.abstract_locals_core d ln) (f2.abstract_locals_core d ln)
| e@(folform.conj f1 f2) d ln := folform.conj (f1.abstract_locals_core d ln) (f2.abstract_locals_core d ln)
| e@(folform.disj f1 f2) d ln := folform.disj (f1.abstract_locals_core d ln) (f2.abstract_locals_core d ln)
| e@(folform.all n n1 f) d ln := folform.all n n1 (f.abstract_locals_core (d+1) ln)
| e@(folform.exist n n1 f) d ln := folform.exist n n1 (f.abstract_locals_core (d+1) ln)
| e d ln := e

meta def folform.abstract_locals : folform → list name → folform := λ f l, f.abstract_locals_core 0 l

meta def hammer_fc (e: expr) : list $ name × name × expr :=
expr.fold e []
  (λ (e : expr) n l, 
    match e with
    | e@(expr.local_const n n1 _ t) := let e := (n, n1, t) in if e ∉ l then e::l else l
    | _ := l
    end)

meta def hammer_ff (l : list $ name × name × expr) : hammer_tactic $ list $ name × name :=
do  exprs ← list.mfilter
      (λ x, let (⟨_, _, t⟩ : name × name × expr) := x in
        do  lip ← lives_in_prop_p t,
            return ¬lip)
      l, 
    return $ list.foldl
      (λ a (x : name × name × expr), let (⟨n, n1, t⟩ : name × name × expr) := x in
        ⟨n, n1⟩ :: a)
      [] exprs 

meta def wrap_quantifier (binder : name → name → folform → folform) (ns : list $ name × name) (f : folform) : folform :=
list.foldr
  (λ (np : name × name) f, binder np.1 np.2 f)
  (folform.abstract_locals f (list.map (λ (np : name × name), np.1) ns))
  ns      

meta def collect_lambdas_aux :
    (expr × (list $ name × name × expr)) → 
    hammer_tactic (expr × (list $ name × name × expr))
| (e@(expr.lam n _ t _), l) := do (b, xn) ← body_of e, collect_lambdas_aux (b, (xn, n, t) :: l)
| a := return a

meta def collect_lambdas (e : expr) := collect_lambdas_aux (e, [])


meta mutual def hammer_c, hammer_g, hammer_f
with hammer_c : expr → hammer_tactic folterm 
| (expr.const n _) := 
  return $ folterm.const n
| (expr.local_const n pp _ t) :=
  do  lip ← lives_in_prop_p t,
      if lip
      then
        return $ folterm.prf
      else
        return $ folterm.lconst n pp
| (expr.app t s) := 
  do  tp ← hammer_c t,
      sp ← hammer_c s,
      match tp with
      | folterm.prf := return folterm.prf
      | _ :=
        match sp with
        | folterm.prf := return tp
        | _ := return $ folterm.app tp sp
        end
      end
| e@(expr.pi n _ t _) :=
  do  lip ← lives_in_prop_p e,
      Fn ← mk_fresh_name,
      let F := folterm.const Fn,
      let An := n ++ Fn,
      ys ← hammer_ff $ hammer_fc e,
      let ce0 := list.foldl (λ t (np : name × name), folterm.app t (folterm.lconst np.1 np.2)) F ys,
      if lip
      then
        (do let ce1 := folform.P ce0, 
            ce2 ← hammer_f e,
            add_axiom An $ wrap_quantifier folform.all ys (folform.iff ce1 ce2))
      else
        (do zn ← mk_fresh_name,
            let zlc := folterm.lconst zn zn, 
            let ys := (⟨zn, zn⟩ :: ys : list $ name × name),
            let ce1 := folform.T zlc ce0,
            ce2 ← hammer_g zlc e,
            add_axiom An $ wrap_quantifier folform.all ys (folform.iff ce1 ce2)),
      return ce0
| e@(expr.lam n _ _ _) :=
  do  (t, xτs) ← collect_lambdas e, 
      α ← tactic.infer_type t,
      let yρs := hammer_fc e,
      Fn ← mk_fresh_name,
      let An := n ++ Fn,
      y₀s ← hammer_ff yρs,
      x₀s ← hammer_ff xτs,
      let Ft :=
        list.foldr
          (λ (nt : name × name × expr) a,
            expr.pi nt.2.1 binder_info.default nt.2.2 $ expr.abstract_local a nt.1)
          α
          $ yρs ++ xτs,
      -- instead of extending the environment, we use a local constant and keep track of its name
      add_constant Fn Ft,
      let F := @expr.local_const tt Fn Fn binder_info.default Ft,
      let (ce1a : expr) :=
        list.foldl 
          (λ (a : expr) (nt : name × name × expr), (a (expr.local_const nt.1 nt.2.1 binder_info.default nt.2.2)))
          F
          $ yρs ++ xτs,  
      -- TODO two approaches:
      my_eq ← tactic.mk_const `eq,
      my_iff ← tactic.mk_const `iff,
      lip ← lives_in_prop_p ce1a,
      let ce1b' := if lip then (my_iff ce1a t) else (my_eq α ce1a t),
      -- ce1b ← tactic.to_expr ``(eq %%ce1a %%t), 
      -- tactic.to_expr is going to blow up if operands are not of the same type. Exciting.
      ce1 ← hammer_f ce1b',
      add_axiom An $ wrap_quantifier folform.all (y₀s ++ x₀s) ce1,
      return $
        list.foldl
          (λ a (nt : name × name), folterm.app a $ folterm.lconst nt.1 nt.2)
          (folterm.const Fn)
          y₀s
| e@(expr.elet x τ t s) :=
  do  let yαs := hammer_fc (t τ),  
      y₀s ← hammer_ff yαs,
      Fn ← mk_fresh_name,
      let An := x ++ Fn,
      let Ft :=
        list.foldr
          (λ (nt : name × name × expr) a,
            expr.pi nt.2.1 binder_info.default nt.2.2 $ expr.abstract_local a nt.1)
          τ
          $ yαs,
      -- deviation from the specification, since I cannot imagine why a definition
      -- instead of a constant is required since the redexes F... are not going to be
      -- reduced
      -- instead of extending the environment, we use a local constant and keep track of its name
      add_constant Fn Ft,
      tactic.add_decl $ declaration.cnst Fn [] Ft tt,
      let F := expr.local_const Fn Fn binder_info.default Ft,
      let ce1 :=
        list.foldl
          (λ (e : expr) (nt : name × name × expr), (e (expr.local_const nt.1 nt.2.1 binder_info.default nt.2.2))) 
          F
          yαs,
      -- TODO deviation from the specification, we use yαs here instead of y₀s.
      -- I presume the specification is some sort of "optimization" since since
      -- Gamma-proof terms are going to be filtered by the definition of hammer_c
      -- anyway, however infer_type is not going to blow up but it will report
      -- incorrect types if the arguments to a function are in the wrong positions
      lip ← lives_in_prop_p Ft,
      if lip
      then
        do  ce2 ← hammer_c t,
            add_axiom An $ wrap_quantifier folform.all y₀s $
              folform.eq 
                (list.foldl (λ e (nt : name × name), (folterm.app e (folterm.const nt.1))) (folterm.const Fn) y₀s)
                ce2
      else
        return (),
      hammer_c $ expr.instantiate_var s ce1
| (expr.var _) := undefined
| (expr.sort _) := undefined
| (expr.mvar _ _ _) := undefined
| (expr.macro _ _) := undefined


with hammer_g : folterm → expr → hammer_tactic folform
| u w@(expr.pi n _ t _) := 
  do  lip ← lives_in_prop_p t,
      if lip
      then 
        do  ge1 ← hammer_f t,
            (s, _) ← body_of w,
            ge2 ← hammer_g u s,
            return $ folform.imp ge1 ge2
      else
        do  (s, xn) ← body_of w,
            ge1 ← hammer_g (folterm.lconst xn n) t,
            ge2 ← hammer_g (folterm.app u (folterm.lconst xn n)) s,
            return $ wrap_quantifier folform.all [(xn, n)] (folform.imp ge1 ge2)
| u w :=
  do  ge1 ← hammer_c w,
      return $ folform.T u ge1


with hammer_f : expr → hammer_tactic folform 
| e@(expr.pi n _ t _) :=
  do  lip ← lives_in_prop_p t,
      if lip 
      then
        do  fe1 ← (hammer_f t),
            (s, _) ← body_of e,
            fe2 ← hammer_f s,
            return $ folform.imp fe1 fe2
      else
        do  (s, xn) ← body_of e,
            fe1 ← hammer_g (folterm.lconst xn n) t,
            fe2 ← hammer_f s,
            return $ wrap_quantifier folform.all [(xn, n)] (folform.imp fe1 fe2)
| e@`(@Exists %%t %%ps) := -- we cannot assume that ps has the shape of a lambda
  do  xn ← mk_fresh_name,
      let lc := expr.local_const xn xn binder_info.default t,
      s ← tactic.whnf (ps lc),
      fe1 ← hammer_g (folterm.lconst xn xn) t,
      fe2 ← hammer_f s,
      return $ wrap_quantifier folform.exist [(xn, xn)] (folform.conj fe1 fe2) 
| e@`(and %%t %%s) :=
  do  fe1 ← hammer_f t,
      fe2 ← hammer_f s,
      return $ folform.conj fe1 fe2
| `(or %%t %%s) :=
  do  fe1 ← hammer_f t,
      fe2 ← hammer_f s,
      return $ folform.disj fe1 fe2
| `(iff %%t %%s) :=
  do  fe1 ← hammer_f t,
      fe2 ← hammer_f s,
      return $ folform.iff fe1 fe2                       
| `(not %%t) :=
  do  fe1 ← hammer_f t,
      return $ folform.neg $ fe1  
| `(%%t = %%s) :=
  do  fe1 ← hammer_c t,
      fe2 ← hammer_c s,
      return $ folform.eq fe1 fe2                                                    
| t  :=
  do  ge1 ← hammer_c t,
      return $ folform.P ge1

-- TODO negation, false? Map to bottom etc.
-- eprover, vampire
-- TODO third phase section 5 Translation?