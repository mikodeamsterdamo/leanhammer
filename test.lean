
section hammerplay

meta def context := list (name × expr)

@[reducible] meta def debruijn := nat

meta inductive folvar
| var : debruijn → folvar

meta inductive folfun
| const : nat → folfun

meta inductive folpred
| P : folpred
| T : folpred 
| eq : folpred
| const : nat → folpred

meta inductive folterm
| const : name → folterm
| lconst : name → name → folterm
| prf : folterm
| var : folvar → folterm
| app : folterm → folterm → folterm

meta inductive folform 
| app : folpred → list folterm → folform
| bottom : folform
| top : folform
| neg : folform → folform
| imp : folform → folform → folform
| iff : folform → folform → folform
| conj : folform → folform → folform
| disj : folform → folform → folform
| all : name → folform → folform
| exist : name → folform → folform

meta structure hammer_state :=
(nextconstidx : ℕ)

meta def hammer_tactic :=
state_t hammer_state tactic

meta instance : monad hammer_tactic :=
state_t.monad 

meta instance (α : Type) : has_coe (tactic α) (hammer_tactic α) :=
⟨state_t.lift⟩


meta def using_hammer {α} (t : hammer_tactic α) : tactic α :=
do let ss := hammer_state.mk 0,
   (a, _) ← state_t.run t ss, -- (do a ← t, return a) 
   return a

meta def when' (c : Prop) [decidable c] (tac : hammer_tactic unit) : hammer_tactic unit :=
if c then tac else tactic.skip

meta def lives_in_prop_p (e : expr) : hammer_tactic bool :=
do tp ← tactic.infer_type e,
   return (if eq tp (expr.sort level.zero) then tt else ff)

/-
meta def fresh_folvar : hammer_tactic folvar :=
do ⟨idx⟩ ← state_t.get,
   state_t.modify (fun state, {state with nextvaridx := state.nextvaridx + 1}),
   return (folvar.var2 idx)
   -/

meta def doforget {α : Type} (t₁ : tactic α)  : tactic α :=
λ s, interaction_monad.result.cases_on (t₁ s)
  (λ r _, interaction_monad.result.success r s)
  (λ e p _, interaction_monad.result.exception e p s)

meta def doforget1 {α : Type} (t₁ : hammer_tactic α) : hammer_tactic α :=
state_t.mk (λ x, do ⟨a, b⟩ ← doforget (t₁.run x),
                    return ⟨a, b⟩) 

-- might want to do something different
meta def mk_fresh_name : tactic name := tactic.mk_fresh_name

meta def body_of : expr → hammer_tactic expr
| e@(expr.pi n bi d b) := do id ← mk_fresh_name,
                             let x := expr.local_const id n bi d,
                             return (expr.instantiate_var b x)
| e@(expr.lam n bi d b) := do id ← mk_fresh_name,
                             let x := expr.local_const id n bi d,
                             return (expr.instantiate_var b x)                             
| e := return e
                    
meta def increase_indices (t : folterm) (n : ℕ) : folterm := sorry

meta def increase_indices1 := λ t, increase_indices t 1

meta def mk_fresh_constant : hammer_tactic folpred := sorry

-- run_cmd if ```(1=1) = ```(1=1) then return () else return ()
-- run_cmd if `n = `n then return () else return ()

meta mutual def hammer_c, hammer_g, hammer_f
with hammer_c : expr → hammer_tactic folterm 
| (expr.const n _) := 
  return $ folterm.const n
| (expr.local_const n n1 _ t) :=
  do  lip ← lives_in_prop_p t,
      if lip
      then
        return $ folterm.prf
      else
        return $ folterm.lconst n n1
| (expr.app t s) := 
  do  tp ← hammer_c t,
      sp ← hammer_c s,
      match tp with
      | folterm.prf := return folterm.prf
      | _ :=
        match sp with
        | folterm.prf := return tp
        | _ := return $ folterm.app tp sp
| e@(expr.pi n _ t _) :=
  do  lip ← lives_in_prop_p e,
      R ← mk_fresh_constant,
      if lip
      then
        
      else


          
| _ := sorry


with hammer_g : folterm → expr → hammer_tactic folform
| u e@(expr.pi n _ t _) := 
  do  lip ← lives_in_prop_p t,
      if lip
      then 
        do  ge1 ← hammer_f t,
            ge2 ← body_of e >>= hammer_g u,
            return $ folform.imp ge1 ge2
      else
        do  ge1 ← hammer_g (folterm.var ⟨0⟩) t,
            ge2 ← body_of e >>= hammer_g (folterm.app (increase_indices1 u) (folterm.var ⟨0⟩)),
            return $ folform.all n $ folform.imp ge1 ge2
| u w :=
  do  ge1 ← hammer_c w,
      return $ folform.app folpred.T [u, ge1]


with hammer_f : expr → hammer_tactic folform 
| e@(expr.pi n _ t _) :=
  do  lip ← lives_in_prop_p t,
      if lip 
      then
        do  fe1 ← (hammer_f t),
            fe2 ← body_of e >>= hammer_f,
            return $ folform.imp fe1 fe2
      else
        do  fe1 ← hammer_g (folterm.var ⟨0⟩) t,
            fe2 ← body_of e >>= hammer_f,
            return $ folform.all n $ folform.imp fe1 fe2
| e@`(@Exists %%t %%s) :=
  do  fe1 ← hammer_g (folterm.var ⟨0⟩) t,
      fe2 ← body_of s >>= hammer_f,
      n ← mk_fresh_name,
      return $ folform.exist n $ folform.conj fe1 fe2
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
      return $ folform.app folpred.eq [fe1, fe2]                                                     
| t  :=
  do  ge1 ← hammer_c t,
      return $ folform.app folpred.P [ge1]

end hammerplay