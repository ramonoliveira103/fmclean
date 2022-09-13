
section propositional

variables P Q R : Prop


------------------------------------------------
-- Proposições de dupla negaço:
------------------------------------------------

theorem doubleneg_intro :
  P → ¬¬P  :=
begin
  intro p,
  intro np,
  apply np,
  exact p,
end

theorem doubleneg_elim :
  ¬¬P → P  :=
begin
  intro nnp, 
  --by_cases p : P, -- other solution
  --exact p,        -- other solution
  --exfalso,        -- other solution
  --contradiction,  -- other solution
  by_contradiction nnpboom, -- RAA (Reductio Ad Absurdum)
  contradiction,
end

theorem doubleneg_law :
  ¬¬P ↔ P  :=
begin
  split,
    intro nnp,
    by_contradiction nnpboom, -- RAA (Reductio Ad Absurdum)
    contradiction,

    intro p,
    intro np,
    contradiction,
end

------------------------------------------------
-- Comutatividade dos ∨,∧:
------------------------------------------------

theorem disj_comm :
  (P ∨ Q) → (Q ∨ P)  :=
begin
  intro f1,
  cases f1 with p q,
  right,
  exact p,
  left,
  exact q,
end

theorem conj_comm :
  (P ∧ Q) → (Q ∧ P)  :=
begin
  intro f1,
  cases f1 with p q,
  split,
  exact q,
  exact p,
end


------------------------------------------------
-- Proposições de interdefinabilidade dos →,∨:
------------------------------------------------

theorem impl_as_disj_converse :
  (¬P ∨ Q) → (P → Q)  :=
begin
  intro f1,
  cases f1 with np q,
  
  intro p,
  exfalso,
  apply np,
  exact p,

  intro p,
  exact q,  
end

theorem disj_as_impl :
  (P ∨ Q) → (¬P → Q)  :=
begin
  intro f1,
  cases f1 with p q,
  
  intro np,
  exfalso,
  apply np,
  exact p,

  intro np,
  exact q,

end


------------------------------------------------
-- Proposições de contraposição:
------------------------------------------------

theorem impl_as_contrapositive :
  (P → Q) → (¬Q → ¬P)  :=
begin
  by_cases p : P; by_cases q : Q,
  
  intro f1,
  intro nq,
  exfalso,
  apply nq,
  exact q,

  intro f2,
  intro nq,
  exfalso,
  apply nq,
  apply f2,
  exact p,

  intro f3,
  intro nq,
  exact p,

  intro f4,
  intro nq,
  exact p,

end

theorem impl_as_contrapositive_converse :
  (¬Q → ¬P) → (P → Q)  :=
begin
  by_cases p : P; by_cases q : Q,

  intro f1,
  intro p,
  exact q,

  intro f2,
  intro p,
  exfalso,
  apply f2,
  exact q,
  exact p,

  intro f3,
  intro p,
  exact q,

  intro f4,
  intro p2,
  exfalso,
  apply p,
  exact p2,

end

theorem contrapositive_law :
  (P → Q) ↔ (¬Q → ¬P)  :=
begin
  split,

    intro f1,
    intro nq,
    intro p,
    apply nq,
    apply f1,
    exact p,

    by_cases p : P; by_cases q : Q,

    intro f2,
    intro p,
    exact q,
    
    intro f3,
    intro p1,
    exfalso,
    apply f3,
    exact q,
    exact p,

    intro f4,
    intro p2,
    exact q,

    intro f5,
    intro p2,
    exfalso,
    apply p,
    exact p2,
    
end


------------------------------------------------
-- A irrefutabilidade do LEM:
------------------------------------------------

theorem lem_irrefutable :
  ¬¬(P∨¬P)  :=
begin
  intro f1,
  apply f1,
  right,
  intro p,
  apply f1,
  left,
  exact p,
end


------------------------------------------------
-- A lei de Peirce
------------------------------------------------

theorem peirce_law_weak :
  ((P → Q) → P) → ¬¬P  :=
begin
  by_cases p : P; by_cases q : Q,

  intro f1,
  intro np,
  apply np,
  exact p,

  intro f2,
  intro np,
  apply np,
  exact p,

  intro f3,
  intro np,
  apply p,
  apply f3,
  intro p2,
  exact q,

  intro f4,
  intro np,
  apply p,
  apply f4,
  intro p2,
  exfalso,
  apply np,
  exact p2,

end


------------------------------------------------
-- Proposições de interdefinabilidade dos ∨,∧:
------------------------------------------------

theorem disj_as_negconj :
  P∨Q → ¬(¬P∧¬Q)  :=
begin
  intro f1,
  cases f1 with p q,
  intro f2,
  apply f2.1,
  exact p,

  intro f3,
  apply f3.2,
  exact q,  
end

theorem conj_as_negdisj :
  P∧Q → ¬(¬P∨¬Q)  :=
begin
  intro f1,
  cases f1 with f2 f3,
  intro f4,
  cases f4 with f5 f6,
  apply f5,
  exact f2,

  apply f6,
  exact f3,
end


------------------------------------------------
-- As leis de De Morgan para ∨,∧:
------------------------------------------------

theorem demorgan_disj :
  ¬(P∨Q) → (¬P ∧ ¬Q)  :=
begin
  intro f1,
  split,
  intro p,
  apply f1,
  left,
  exact p,

  intro q,
  apply f1,
  right,
  exact q,
end

theorem demorgan_disj_converse :
  (¬P ∧ ¬Q) → ¬(P∨Q)  :=
begin
  intro f1,
  intro f2,
  apply f1.1,
  cases f2 with p q,

  exact p,

  exfalso,
  apply f1.2,
  exact q,
end

theorem demorgan_conj :
  ¬(P∧Q) → (¬Q ∨ ¬P)  :=
begin
  by_cases p : P; by_cases np : ¬P,
  
  intro f1,
  right,
  exact np,

  intro f2,
  left,
  intro q,
  apply f2,
  split,
    exact p,
    exact q,

  intro f3,
  right,
  exact np,

  intro f4,
  right,
  exact p,
end

theorem demorgan_conj_converse :
  (¬Q ∨ ¬P) → ¬(P∧Q)  :=
begin
  intro f1,
  cases f1 with nq np,
  intro f2,
  cases f2 with p q,
  apply nq,
  exact q,

  intro f3,
  cases f3 with p q,
  apply np,
  exact p,
end

theorem demorgan_conj_law :
  ¬(P∧Q) ↔ (¬Q ∨ ¬P)  :=
begin
  by_cases p : P; by_cases np : ¬P,
  
  split,
    intro f1,
    right,
    exact np,

  intro f2,
  intro f3,
  apply np,
  exact p,

  split,
    intro f4,
    left,
    intro q,
    apply f4,
    split,
      exact p,
      exact q,
    
    intro f5,
    cases f5 with nq np,
    intro f6,
    apply nq,
    exact f6.2,

    intro f7,
    apply np,
    exact p,

    split,
      intro f8,
      right,
      exact np,

      intro f9,
      intro f10,
      apply np,
      exact f10.1,

    split,
      intro f11,
      right,
      exact p,

      intro f12,
      intro f13,
      apply np,
      exact p,

end

theorem demorgan_disj_law :
  ¬(P∨Q) ↔ (¬P ∧ ¬Q)  :=
begin
  split,
    intro f1,
    split,
      intro p,
      apply f1,
      left,
      exact p,

      intro q,
      apply f1,
      right,
      exact q,

    intro f2,
    cases f2 with np nq,
    intro f3,
    cases f3 with p q,
    apply np,
    exact p,
    apply nq,
    exact q,
    
end

------------------------------------------------
-- Proposições de distributividade dos ∨,∧:
------------------------------------------------

theorem distr_conj_disj :
  P∧(Q∨R) → (P∧Q)∨(P∧R)  :=
begin
  intro f1,
  cases f1 with p f2,
  cases f2 with q r,
  left,
  split,
    exact p,
    exact q,
  
  right,
  split,
    exact p,
    exact r,
end

theorem distr_conj_disj_converse :
  (P∧Q)∨(P∧R) → P∧(Q∨R)  :=
begin
  intro f1,
  cases f1 with f2 f3,
  cases f2 with p q,
  
  split,
    exact p,
    
    left,
    exact q,

  cases f3 with p r,
  split,
    exact p,

    right,
    exact r,
end

theorem distr_disj_conj :
  P∨(Q∧R) → (P∨Q)∧(P∨R)  :=
begin
  intro f1,
  cases f1 with p f2,
 
  split,
    left,
    exact p,

    left,
    exact p,
  
  cases f2 with q r,
  split,
    right,
    exact q,

    right,
    exact r,  
end

theorem distr_disj_conj_converse :
  (P∨Q)∧(P∨R) → P∨(Q∧R)  :=
begin
  by_cases p : P; by_cases q : Q, by_cases r : R,

  intro f1,
  left,
  exact p,

  intro f2,
  left,
  exact p,
  
  intro f3,
  left,
  exact p,

  intro f4,
  right,
  split,
    exact q,

    cases f4 with f5 f6,
    cases f6 with p6 r,
    exfalso,
    apply p,
    exact p6,

  exact r,

  intro f7,
  cases f7 with f8 f9,
  left,
  cases f8 with p10 q10,
  exact p10,
  
  exfalso,
  apply q,
  exact q10,

end


------------------------------------------------
-- Currificação
------------------------------------------------

theorem curry_prop :
  ((P∧Q)→R) → (P→(Q→R))  :=
begin
  intro f1,
  intro p,
  intro q,

  have p_and_q : P∧Q,
  
  split,
    exact p,
    
    exact q,

  exact f1 p_and_q, -- Usando dados on the fly


end

theorem uncurry_prop :
  (P→(Q→R)) → ((P∧Q)→R)  :=
begin
  intro f1,
  intro f2,
  cases f2 with p q,

  exact f1 p q, -- Usando dados on the fly

end


------------------------------------------------
-- Reflexividade da →:
------------------------------------------------

theorem impl_refl :
  P → P  :=
begin
  intro p,
  exact p,
end

------------------------------------------------
-- Weakening and contraction:
------------------------------------------------

theorem weaken_disj_right :
  P → (P∨Q)  :=
begin
  intro p,
  left,
  exact p,
end

theorem weaken_disj_left :
  Q → (P∨Q)  :=
begin
  intro q,
  right,
  exact q,
end

theorem weaken_conj_right :
  (P∧Q) → P  :=
begin
  intro f1,
  cases f1 with p q,
  exact p,
end

theorem weaken_conj_left :
  (P∧Q) → Q  :=
begin
  intro f1,
  cases f1 with p q,
  exact q,
end

theorem conj_idempot :
  (P∧P) ↔ P :=
begin
  split,
    intro f1,
    cases f1 with p_left p_right,
    exact p_left,

    intro p,
    split,
      exact p,

      exact p,
end

theorem disj_idempot :
  (P∨P) ↔ P  :=
begin
  split,
    intro f1,
    cases f1 with p_left p_right,
    exact p_left,
    exact p_right,

    intro p,
    left,
    exact p,
end

end propositional


----------------------------------------------------------------


section predicate

variable U : Type
variables P Q : U -> Prop


------------------------------------------------
-- As leis de De Morgan para ∃,∀:
------------------------------------------------

theorem demorgan_exists :
  ¬(∃x, P x) → (∀x, ¬P x)  :=
begin
  intro f1,
  intro f2,
  intro f3,
  apply f1,
  existsi f2,
  exact f3,
end

theorem demorgan_exists_converse :
  (∀x, ¬P x) → ¬(∃x, P x)  :=
begin
  intro f1,
  intro f2,
  cases f2 with u f3,
  apply f1,
  exact f3,
end

theorem demorgan_forall :
  ¬(∀x, P x) → (∃x, ¬P x)  :=
begin
  --intro f1,
  --split,
    --intro f2,
    --apply f1,
    --intro f3,
    sorry,
end

theorem demorgan_forall_converse :
  (∃x, ¬P x) → ¬(∀x, P x)  :=
begin
  intro f1,
  intro f2,
  cases f1 with u f3,
  apply f3,
  exact f2 u,
end

theorem demorgan_forall_law :
  ¬(∀x, P x) ↔ (∃x, ¬P x)  :=
begin
  --split,
   -- intro f1,
  --  split,
  --    intro f2,
   --   apply f1,
   --   intro f3,
      sorry,
      
      
end

theorem demorgan_exists_law :
  ¬(∃x, P x) ↔ (∀x, ¬P x)  :=
begin
  split,
    intro f1,
    intro f2,
    intro f3,
    apply f1,
    existsi f2,
    exact f3,

    intro f4, -- demorgan_exists
    intro f5,
    cases f5 with u f6,
    apply f4,
    exact f6,
    
end


------------------------------------------------
-- Proposições de interdefinabilidade dos ∃,∀:
------------------------------------------------

theorem exists_as_neg_forall :
  (∃x, P x) → ¬(∀x, ¬P x)  :=
begin
  intro f1,
  intro f2,
  cases f1 with f3 f4,
  apply f2,
  exact f4,
end

theorem forall_as_neg_exists :
  (∀x, P x) → ¬(∃x, ¬P x)  :=
begin
  intro f1,
  intro f2,
  cases f2 with f3 f4,
  apply f4,
  apply f1,  
end

theorem forall_as_neg_exists_converse :
  ¬(∃x, ¬P x) → (∀x, P x)  :=
begin
  --intro f1,
  --intro f2,
  --by_cases f3 : P f2,
  --exact f3,
  sorry,
end

theorem exists_as_neg_forall_converse :
  ¬(∀x, ¬P x) → (∃x, P x)  :=
begin





  sorry,
  

end

theorem forall_as_neg_exists_law :
  (∀x, P x) ↔ ¬(∃x, ¬P x)  :=
begin
  split,
    intro f1,
    intro f2,
    cases f2 with f3 f4,
    apply f4,
    exact f1 f3,

    intro f5,
    intro f6,
    sorry,
    
    
end

theorem exists_as_neg_forall_law :
  (∃x, P x) ↔ ¬(∀x, ¬P x)  :=
begin


sorry,
      


end


------------------------------------------------
--  Proposições de distributividade de quantificadores:
------------------------------------------------

theorem exists_conj_as_conj_exists :
  (∃x, P x ∧ Q x) → (∃x, P x) ∧ (∃x, Q x)  :=
begin
  intro f1,
  cases f1 with f2 f3,
  cases f3 with f4 f5,
  split,
    existsi f2,
    exact f4,

    existsi f2,
    exact f5,
end

theorem exists_disj_as_disj_exists :
  (∃x, P x ∨ Q x) → (∃x, P x) ∨ (∃x, Q x)  :=
begin
  --intro f1,
  --cases f1 with f2 f3,
  --left,
  --split,
    --cases f3 with f4 f5,
    sorry,
end

theorem exists_disj_as_disj_exists_converse :
  (∃x, P x) ∨ (∃x, Q x) → (∃x, P x ∨ Q x)  :=
begin
  intro f1,
  cases f1 with f2 f3,
  cases f2 with f4 f5,
  split,
    left,
    exact f5,

    cases f3 with f6 f7,
    split,
      right,
      exact f7,
end

theorem forall_conj_as_conj_forall :
  (∀x, P x ∧ Q x) → (∀x, P x) ∧ (∀x, Q x)  :=
begin

  --intro f1,
  --split,
    --intro f2,
    sorry,    
    
end

theorem forall_conj_as_conj_forall_converse :
  (∀x, P x) ∧ (∀x, Q x) → (∀x, P x ∧ Q x)  :=
begin
  intro f1,
  cases f1 with f2 f3,
  intro f4,
  split,
    exact f2 f4,

    exact f3 f4,   
end


theorem forall_disj_as_disj_forall_converse :
  (∀x, P x) ∨ (∀x, Q x) → (∀x, P x ∨ Q x)  :=
begin
  intro f1,
  cases f1 with f2 f3,
  intro f4,
  left,
  exact f2 f4,

  intro f5,
  right,
  exact f3 f5,
end


/- NOT THEOREMS --------------------------------

theorem forall_disj_as_disj_forall :
  (∀x, P x ∨ Q x) → (∀x, P x) ∨ (∀x, Q x)  :=
begin
end

theorem exists_conj_as_conj_exists_converse :
  (∃x, P x) ∧ (∃x, Q x) → (∃x, P x ∧ Q x)  :=
begin
end

---------------------------------------------- -/

end predicate
