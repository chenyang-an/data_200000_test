variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_165468117816329699936351650262 : (((False ∨ (p2 ∨ ((False → (p2 → p5)) ∨ (p4 ∧ p2)))) ∧ ((False ∨ False) ∧ (p5 ∨ p3))) ∨ (((p4 ∧ (False → p1)) ∨ True) ∨ (p2 ∨ True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_614733879444976064949370885508 : (((((((p5 → ((p1 ∧ p4) ∧ (p4 ∨ False))) → ((p2 → p1) ∨ (p1 ∧ p2))) → (p2 ∨ p2)) ∨ (((False ∨ p3) ∨ p3) ∧ p3)) ∨ True) ∨ p4) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_342664834850959881385546350318 : (p2 → ((((p3 → False) ∨ False) ∨ ((False ∧ p2) ∨ (p3 ∨ p4))) ∨ (p3 ∨ ((p3 → p2) ∨ (((False ∨ (p1 ∧ (p3 → p4))) → p1) ∨ p3))))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h2
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_301836225057475797580678763086 : (False ∨ ((p4 ∨ False) ∨ ((p3 ∨ (((False → p2) → p2) → ((p2 ∨ p3) ∧ (p4 ∨ True)))) ∨ (((p5 ∧ p5) ∧ (p3 ∨ (p4 ∧ p1))) → p4)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h2 : (False → p2) := by
    -- Implications on the right can always be decomposed.
    intro h3
    -- False on the left can always be used.
    apply False.elim h3
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h4 := h1 h2
  -- One of the premise coincides with the conclusion.
  exact h4
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_42229387035263383733812266131 : (((False ∧ ((False → ((((p4 ∨ (True ∨ p1)) ∨ p4) ∨ p3) ∧ (p5 ∧ p4))) → ((p1 ∧ p5) ∧ ((p3 ∨ (p3 → p5)) ∧ p5)))) ∨ True) ∨ p3) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_148460492535626434933749745618 : (((((False → (p2 → True)) ∨ p1) ∨ (((False → p2) → True) ∧ p2)) ∧ ((p2 ∧ p3) ∨ (p3 ∨ (p5 ∨ p2)))) ∨ (((p3 ∨ False) ∨ True) ∨ p5)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_193203185845990244976818534671 : (((p4 ∧ (p2 ∧ (p5 → p2))) → (False → (True → False))) → (True ∧ ((((((p2 ∨ p4) ∨ (True ∨ False)) → False) ∧ (p2 ∨ p5)) ∨ False) → False))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- Implications on the right can always be decomposed.
  intro h2
  -- Disjunctions on the left can always be decomposed.
  cases h2
  case inl h3 =>
    -- Conjunctions on the left can always be decomposed.
    let h4 := h3.left
    let h5 := h3.right
    -- Disjunctions on the left can always be decomposed.
    cases h5
    case inl h6 =>
      -- We want to use the implication h4 based on <expert-advice>. So we show its premise.
      have h7 : ((p2 ∨ p4) ∨ (True ∨ False)) := by
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- One of the premise coincides with the conclusion.
        exact h6
      -- We have shown the premise of h4, we can now drive its conclusion.
      let h8 := h4 h7
      -- False on the left can always be used.
      apply False.elim h8
    case inr h9 =>
      -- We want to use the implication h4 based on <expert-advice>. So we show its premise.
      have h10 : ((p2 ∨ p4) ∨ (True ∨ False)) := by
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- True on the right can always be proven directly.
        apply True.intro
      -- We have shown the premise of h4, we can now drive its conclusion.
      let h11 := h4 h10
      -- False on the left can always be used.
      apply False.elim h11
  case inr h12 =>
    -- False on the left can always be used.
    apply False.elim h12



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_637956274492066226606727571992 : (((((p5 → (((p4 ∧ p4) ∧ p2) → (False ∨ p1))) ∧ (p2 ∧ ((p3 ∨ ((True ∨ ((p1 ∧ p2) → p3)) → p2)) → (True ∨ p2)))) → False) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_147848745210402162038070098982 : (((p5 ∨ (((p3 ∧ ((p3 → p2) ∧ p5)) → p5) → ((p2 ∨ p3) ∧ ((p1 ∨ p2) ∨ (p2 → p3))))) → False) ∨ (False → (p4 → (False → p1)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Implications on the right can always be decomposed.
  intro h3
  -- False on the left can always be used.
  apply False.elim h3



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_65143066359766100830623433209 : ((p2 ∨ (p3 → ((False ∧ p1) ∨ ((((p1 ∨ ((p5 ∨ (p1 → (p1 → True))) ∧ False)) ∧ False) ∧ (False → (p3 ∧ (p5 ∨ p4)))) ∨ True)))) ∨ p1) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_357323905694705372408243185416 : (p5 → ((True → False) ∨ ((((((p1 ∧ True) → True) ∨ (((p4 ∨ p1) → True) ∨ (p5 ∧ p2))) → (p4 → p1)) ∧ (p1 ∨ p1)) ∨ (p5 → p5)))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h2
  -- One of the premise coincides with the conclusion.
  exact h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_263680403263655057101303783111 : (True ∧ (((True → ((((p4 → p3) ∧ p1) → (((p1 → True) → p3) ∨ p2)) → (p1 ∧ p3))) ∧ True) ∨ ((p1 ∨ (p5 ∧ True)) ∨ (True ∧ True)))) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_662259518915381176648045152434 : (((((True → ((p3 ∨ False) → ((p2 ∧ (p3 ∧ True)) ∨ p2))) ∨ ((((True → p1) ∨ True) → p4) → (True → (False → p5)))) → (p3 ∧ True)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_355883390859838011690822594084 : (p5 → ((False ∨ (((p4 ∧ p5) ∨ p4) → ((p4 → (p3 → ((False → (p1 ∧ p1)) → p2))) ∨ (p2 → (p3 ∨ p4))))) ∨ ((p5 → p3) → p1))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h2
  -- Disjunctions on the left can always be decomposed.
  cases h2
  case inl h3 =>
    -- Conjunctions on the left can always be decomposed.
    let h4 := h3.left
    let h5 := h3.right
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h6
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h4
  case inr h7 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h8
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h7



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_225282583323989591307760342014 : (((True ∨ p5) ∧ p2) ∨ ((p5 → ((((((p5 ∨ (p2 ∨ (p5 ∨ p4))) → p2) ∨ p1) → p4) ∧ (False ∨ (p5 ∧ p2))) ∨ p5)) ∧ (p3 ∨ True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_194079829254016653007030916477 : ((True → (((p4 ∨ False) ∧ p2) → ((p4 ∧ True) → p4))) → ((True ∧ ((((p3 ∨ True) ∨ False) ∧ (p5 ∨ p2)) ∧ (p5 → (p2 → p1)))) ∨ True)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_305769331849089910763348423775 : (p1 ∨ ((((p1 ∨ (p1 ∨ False)) ∨ False) ∨ (p5 → True)) ∨ ((p1 ∨ (((False ∨ p3) → p2) ∨ False)) ∨ (p4 → (((p3 ∧ False) → p4) ∧ p3))))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_726251745316624046134912532606 : (((((False ∨ p4) ∨ p5) ∨ ((p5 → ((((p2 ∨ (p1 → ((False ∨ p3) → p1))) → p1) ∧ (p5 ∧ (False ∧ (p4 ∨ True)))) ∧ False)) → p5)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_225475883622745134167687392412 : (((p4 ∨ p4) ∧ p4) ∨ (p1 → ((((p3 → p3) → (p1 ∨ p2)) ∨ (p4 ∧ (((True ∨ p5) → ((False ∧ p1) ∨ p1)) ∨ p3))) → (p3 ∨ p1)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Disjunctions on the left can always be decomposed.
  cases h2
  case inl h3 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h1
  case inr h4 =>
    -- Conjunctions on the left can always be decomposed.
    let h5 := h4.left
    let h6 := h4.right
    -- Disjunctions on the left can always be decomposed.
    cases h6
    case inl h7 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- One of the premise coincides with the conclusion.
      exact h1
    case inr h8 =>
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- One of the premise coincides with the conclusion.
      exact h8



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_341002387578404031637548508761 : (p2 → ((False ∧ (((((((False ∧ (p2 ∧ p5)) ∧ False) → (p3 ∧ (p4 ∧ p2))) → (p5 ∨ p3)) ∨ (p3 ∨ p3)) ∧ (False ∨ p3)) → p1)) ∨ True)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_178950448231802345253869121009 : (((p5 ∧ False) ∨ (((True ∨ ((p3 ∨ False) ∧ (p4 → False))) → False) ∧ p2)) ∨ (True ∧ ((p3 → (False → p1)) ∧ ((p4 ∨ (True → True)) → True)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- False on the left can always be used.
  apply False.elim h2
  -- Implications on the right can always be decomposed.
  intro h3
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_323495203331551025794630154777 : (p5 ∨ ((((True ∨ ((False ∨ (p1 → False)) → p4)) → (p5 ∧ ((True ∧ p3) → p2))) ∨ (p5 → ((p1 ∨ p4) → p5))) ∨ (p2 ∧ (p5 → p1)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Disjunctions on the left can always be decomposed.
  cases h2
  case inl h3 =>
    -- One of the premise coincides with the conclusion.
    exact h1
  case inr h4 =>
    -- One of the premise coincides with the conclusion.
    exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_354592093258198393290338338167 : (p5 → (((p3 ∨ ((((p4 ∧ True) ∧ False) ∨ p3) ∨ ((p1 ∧ (p1 ∧ (((False → (p3 ∨ p1)) ∧ p4) ∨ True))) → (p5 ∨ p1)))) ∧ p1) ∨ p5)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_210376093387535396726920541264 : (((True ∨ (p1 → p2)) ∨ p4) ∧ ((((p2 → p3) ∧ p1) ∧ (((p3 ∨ p5) ∧ (((p1 ∨ p1) → p3) ∨ ((p3 ∨ True) ∨ p2))) → p4)) ∨ True)) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_780739863015299623614207140538 : (((p2 ∨ (((p1 → False) → (True ∧ (p4 ∨ p4))) ∨ (False ∨ (p4 → ((p1 → ((p4 ∨ p3) ∨ p4)) ∨ ((p2 ∧ (p2 ∨ p5)) ∨ True)))))) ∨ False) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_802595359988939176330443560627 : (((p2 → (p5 ∨ (((p1 → p3) → (p5 ∧ p5)) → (((False ∨ ((p3 → True) → p3)) ∨ p2) ∨ (((p3 ∧ p2) ∧ p2) ∧ (p4 → p5)))))) ∨ p2) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h2
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_117759950925627249282638654606 : ((p4 ∧ (((p1 → ((p1 ∨ p5) ∨ (p3 ∨ ((p3 ∧ p3) ∧ (p5 ∧ (True ∨ (p5 ∧ True))))))) ∧ ((p5 → p2) ∨ p3)) → p3)) ∨ (False → False)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_158977297594134610206227572559 : ((p3 ∨ ((((p3 ∧ (p3 → True)) ∧ False) ∧ (p2 ∧ (((p1 ∨ True) → p2) → p3))) ∨ (p3 ∧ False))) ∨ (((p4 → p5) → p4) → (p3 → p3))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- One of the premise coincides with the conclusion.
  exact h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_169114384519203444858656426519 : ((p4 → (True → (((p1 → ((True ∨ ((p1 → p2) ∧ (True → p1))) ∨ False)) ∨ p3) ∧ p1))) → (p5 ∨ ((p4 ∧ (p2 ∧ p2)) → (p5 → p1)))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h2
  -- Implications on the right can always be decomposed.
  intro h3
  -- Conjunctions on the left can always be decomposed.
  let h4 := h2.left
  let h5 := h2.right
  -- Conjunctions on the left can always be decomposed.
  let h6 := h5.left
  let h7 := h5.right
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h8 : p4 := by
    -- One of the premise coincides with the conclusion.
    exact h4
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h9 := h1 h8
  -- We want to use the implication h9 based on <expert-advice>. So we show its premise.
  have h10 : True := by
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h9, we can now drive its conclusion.
  let h11 := h9 h10
  -- We need to get the right conjuct of h11 based on <expert-advice>.
  let h12 := h11.right
  -- One of the premise coincides with the conclusion.
  exact h12



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_225872452381295969087949317910 : (((False ∧ p5) ∨ p1) ∨ (((False ∧ p2) ∧ True) ∨ (((False ∧ p2) ∧ ((p5 ∨ p3) → (((True ∨ p5) ∨ p5) ∧ (p3 → True)))) → (p4 ∧ p2)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- Conjunctions on the left can always be decomposed.
  let h4 := h2.left
  let h5 := h2.right
  -- False on the left can always be used.
  apply False.elim h4
  -- Conjunctions on the left can always be decomposed.
  let h6 := h1.left
  let h7 := h1.right
  -- Conjunctions on the left can always be decomposed.
  let h8 := h6.left
  let h9 := h6.right
  -- False on the left can always be used.
  apply False.elim h8



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_157996027550104542315709966195 : ((((p5 → p5) ∨ (True → (False → (p5 ∧ p5)))) → (p2 ∧ (((True ∧ (p3 ∧ p2)) → p5) → p1))) ∨ (p5 ∨ ((False → p5) ∧ (p1 → p1)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h1
  -- False on the left can always be used.
  apply False.elim h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- One of the premise coincides with the conclusion.
  exact h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_60471159601734807239530715163 : (((p5 → p4) → ((((p4 → (((False ∧ p2) ∧ False) → p3)) → ((p2 ∧ p1) ∧ True)) ∨ (True ∨ p5)) → (p4 ∧ (p3 ∨ (p2 → p2))))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_125034981694621361428998754074 : ((((True ∨ p1) → False) ∧ (((p2 → ((p4 → ((p4 ∧ (False ∧ p3)) ∧ p3)) ∧ p5)) → p2) ∧ ((p3 ∧ p5) ∨ (p4 → p2)))) → (p2 ∨ False)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- Conjunctions on the left can always be decomposed.
  let h4 := h3.left
  let h5 := h3.right
  -- Disjunctions on the left can always be decomposed.
  cases h5
  case inl h6 =>
    -- Conjunctions on the left can always be decomposed.
    let h7 := h6.left
    let h8 := h6.right
    -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
    have h9 : (True ∨ p1) := by
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- True on the right can always be proven directly.
      apply True.intro
    -- We have shown the premise of h2, we can now drive its conclusion.
    let h10 := h2 h9
    -- False on the left can always be used.
    apply False.elim h10
  case inr h11 =>
    -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
    have h12 : (True ∨ p1) := by
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- True on the right can always be proven directly.
      apply True.intro
    -- We have shown the premise of h2, we can now drive its conclusion.
    let h13 := h2 h12
    -- False on the left can always be used.
    apply False.elim h13



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_165989394685710002571960909013 : (((p1 ∧ p5) ∨ ((p4 ∨ p3) ∨ ((((p2 ∧ p1) → (p2 ∧ (p1 → p2))) → p1) → p1))) ∨ ((False ∧ ((p5 → False) ∧ (True → p4))) ∨ p4)) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h2 : ((p2 ∧ p1) → (p2 ∧ (p1 → p2))) := by
    -- Implications on the right can always be decomposed.
    intro h3
    -- Conjunctions on the right can always be decomposed.
    apply And.intro
    -- Conjunctions on the left can always be decomposed.
    let h4 := h3.left
    let h5 := h3.right
    -- One of the premise coincides with the conclusion.
    exact h4
    -- Implications on the right can always be decomposed.
    intro h6
    -- Conjunctions on the left can always be decomposed.
    let h7 := h3.left
    let h8 := h3.right
    -- One of the premise coincides with the conclusion.
    exact h7
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h9 := h1 h2
  -- One of the premise coincides with the conclusion.
  exact h9



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_66230529146827000088640931998 : ((p5 ∨ ((p1 ∨ ((((p2 ∨ p4) → False) → False) ∨ p2)) ∧ ((p5 → ((p4 ∨ (p4 ∧ p3)) ∨ (((p4 → p3) ∧ True) ∧ True))) ∧ p2))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_259557327354706401175734802762 : ((p1 → True) → ((p5 → (p4 ∨ (((((p4 ∧ True) → p5) → (False ∧ p2)) ∨ (p4 ∧ (p1 ∨ p2))) ∨ ((False ∨ p3) ∧ (p2 ∧ p5))))) ∨ True)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_1819851354951183024459015458 : ((p2 → (((False → ((p5 → (p3 → p1)) ∧ (((p5 ∧ False) ∨ p4) ∨ (p3 ∧ p2)))) → (p1 ∧ p5)) ∧ p2)) ∨ (p4 ∨ (False → p3))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_855633325415949120621728450170 : (((((((p1 → (((((p1 ∧ (False ∧ True)) ∨ (p3 → (True ∧ (p3 → (p5 ∨ p3))))) ∨ p3) ∨ p2) → p5)) → p1) ∨ False) ∨ True) → False) → p1) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h1
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h2 : ((((p1 → (((((p1 ∧ (False ∧ True)) ∨ (p3 → (True ∧ (p3 → (p5 ∨ p3))))) ∨ p3) ∨ p2) → p5)) → p1) ∨ False) ∨ True) := by
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h3 := h1 h2
  -- False on the left can always be used.
  apply False.elim h3
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_157058190777919257746713722066 : (((p4 ∧ ((p3 ∨ (p2 ∨ ((((p3 → p1) ∨ False) → (p4 → p5)) → p3))) ∧ (p2 ∧ False))) ∨ False) ∨ (((p4 ∨ (p5 ∧ p2)) ∨ True) ∨ p4)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_160203446290590013110081040065 : ((((((p5 → p4) → p1) ∧ ((True → p3) ∨ ((p4 ∨ True) ∧ (False → p5)))) ∧ p5) ∨ (p2 → p5)) → (p2 → (p5 ∨ ((p4 → False) ∧ p5)))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h3 =>
    -- Conjunctions on the left can always be decomposed.
    let h4 := h3.left
    let h5 := h3.right
    -- Conjunctions on the left can always be decomposed.
    let h6 := h4.left
    let h7 := h4.right
    -- Disjunctions on the left can always be decomposed.
    cases h7
    case inl h8 =>
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- One of the premise coincides with the conclusion.
      exact h5
    case inr h9 =>
      -- Conjunctions on the left can always be decomposed.
      let h10 := h9.left
      let h11 := h9.right
      -- Disjunctions on the left can always be decomposed.
      cases h10
      case inl h12 =>
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- One of the premise coincides with the conclusion.
        exact h5
      case inr h13 =>
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- One of the premise coincides with the conclusion.
        exact h5
  case inr h14 =>
    -- We want to use the implication h14 based on <expert-advice>. So we show its premise.
    have h15 : p2 := by
      -- One of the premise coincides with the conclusion.
      exact h2
    -- We have shown the premise of h14, we can now drive its conclusion.
    let h16 := h14 h15
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- One of the premise coincides with the conclusion.
    exact h16



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_164907911562169122903872808086 : (((((p3 ∧ (p2 ∨ p1)) ∨ ((p5 ∧ (False ∧ (False → (p1 ∨ p1)))) → False)) ∧ p3) → p4) ∨ ((p2 ∨ ((p1 → (False ∨ False)) ∧ False)) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_762917124196324856412927926492 : (((p3 ∧ ((True → (True ∧ ((True ∨ p5) ∧ p1))) → ((((p3 → (p2 → False)) ∨ p5) ∨ p1) → (((p2 ∧ p5) ∨ p4) ∧ (p1 → True))))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_326099329029723623439404454341 : (p5 ∨ (p1 → (((p5 → (True → ((p1 ∨ p5) ∨ True))) ∧ (True → (((p2 ∨ (p3 → (p5 ∧ ((False ∨ p1) ∧ False)))) ∨ p5) → p2))) ∨ p1))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_599291843409658987272288135308 : (((((False ∧ p3) ∨ ((p3 ∨ p3) ∨ (p1 ∨ (p1 ∧ ((True ∨ p3) ∧ ((p2 ∧ (False ∧ (p5 → (p3 ∨ (p4 ∧ p2))))) ∧ p4)))))) ∧ p2) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_47519429863967139547224765408 : (((p3 ∨ ((((False ∨ (((p3 → True) ∧ p5) ∨ p4)) → p4) → (((False ∨ (p5 ∧ p3)) ∨ False) ∨ p5)) ∧ (p3 ∨ p2))) ∨ (p1 ∨ p1)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_305763584917885415033447906401 : (p1 ∨ (((p3 ∨ (p2 → ((p5 ∨ p3) → p1))) ∨ False) ∨ ((p1 ∧ (((p4 ∨ (p5 ∨ (False ∧ p5))) ∨ p2) ∧ ((False ∨ False) ∧ p2))) → p5))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- Conjunctions on the left can always be decomposed.
  let h4 := h3.left
  let h5 := h3.right
  -- Disjunctions on the left can always be decomposed.
  cases h4
  case inl h6 =>
    -- Disjunctions on the left can always be decomposed.
    cases h6
    case inl h7 =>
      -- Conjunctions on the left can always be decomposed.
      let h8 := h5.left
      let h9 := h5.right
      -- Disjunctions on the left can always be decomposed.
      cases h8
      case inl h10 =>
        -- False on the left can always be used.
        apply False.elim h10
      case inr h11 =>
        -- False on the left can always be used.
        apply False.elim h11
    case inr h12 =>
      -- Disjunctions on the left can always be decomposed.
      cases h12
      case inl h13 =>
        -- Conjunctions on the left can always be decomposed.
        let h14 := h5.left
        let h15 := h5.right
        -- Disjunctions on the left can always be decomposed.
        cases h14
        case inl h16 =>
          -- False on the left can always be used.
          apply False.elim h16
        case inr h17 =>
          -- False on the left can always be used.
          apply False.elim h17
      case inr h18 =>
        -- Conjunctions on the left can always be decomposed.
        let h19 := h18.left
        let h20 := h18.right
        -- False on the left can always be used.
        apply False.elim h19
  case inr h21 =>
    -- Conjunctions on the left can always be decomposed.
    let h22 := h5.left
    let h23 := h5.right
    -- Disjunctions on the left can always be decomposed.
    cases h22
    case inl h24 =>
      -- False on the left can always be used.
      apply False.elim h24
    case inr h25 =>
      -- False on the left can always be used.
      apply False.elim h25



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_215068259948415926861434146100 : (((p5 ∨ p2) → (p5 ∨ p5)) ∨ ((((True → False) ∧ ((p5 ∨ (p4 → ((((True ∨ False) → p2) ∧ p3) ∧ p2))) ∨ (p3 ∨ False))) ∧ p2) → p5)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- Conjunctions on the left can always be decomposed.
  let h4 := h2.left
  let h5 := h2.right
  -- Disjunctions on the left can always be decomposed.
  cases h5
  case inl h6 =>
    -- Disjunctions on the left can always be decomposed.
    cases h6
    case inl h7 =>
      -- One of the premise coincides with the conclusion.
      exact h7
    case inr h8 =>
      -- We want to use the implication h4 based on <expert-advice>. So we show its premise.
      have h9 : True := by
        -- True on the right can always be proven directly.
        apply True.intro
      -- We have shown the premise of h4, we can now drive its conclusion.
      let h10 := h4 h9
      -- False on the left can always be used.
      apply False.elim h10
  case inr h11 =>
    -- Disjunctions on the left can always be decomposed.
    cases h11
    case inl h12 =>
      -- We want to use the implication h4 based on <expert-advice>. So we show its premise.
      have h13 : True := by
        -- True on the right can always be proven directly.
        apply True.intro
      -- We have shown the premise of h4, we can now drive its conclusion.
      let h14 := h4 h13
      -- False on the left can always be used.
      apply False.elim h14
    case inr h15 =>
      -- False on the left can always be used.
      apply False.elim h15



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_223992655330221754013664320351 : ((p4 ∨ (False → True)) ∧ ((False ∧ (((False → (True ∧ True)) → p1) ∨ p1)) ∨ ((((p4 ∧ (False ∨ ((p2 ∨ p4) ∧ p3))) ∧ True) ∨ p5) ∨ True))) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_165240445088811047713722867448 : (((p3 ∧ (p3 ∨ (p2 → (p5 ∨ (p4 ∧ (False → ((False ∨ p1) ∨ p3))))))) ∨ (p5 ∨ p4)) ∨ ((p1 → False) ∨ ((False → (True → False)) → True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_316915881294075036000281708408 : (p3 ∨ (p2 → ((p4 ∨ (((p4 ∧ p3) ∧ (p4 → (p3 ∨ ((((p1 → p5) ∧ True) ∧ p5) ∧ p5)))) → ((True ∧ (p5 ∧ True)) ∨ False))) ∨ p2))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_701608991260284447056943829512 : (((((p3 ∧ p1) ∨ ((p3 ∧ p3) ∨ ((p1 → p1) ∨ p3))) ∧ (p4 ∧ ((p5 ∨ ((p5 ∨ p3) ∨ True)) ∧ (True ∧ ((p4 ∨ True) ∨ p1))))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_58998357104100307217543284942 : (((p3 ∧ p1) ∨ ((p4 ∨ ((p1 → (p2 ∧ (False → (p1 ∨ p3)))) → p3)) → (((True → (p3 ∨ False)) ∧ (False ∨ p5)) ∨ (p4 → True)))) ∨ p1) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h2 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h3
    -- True on the right can always be proven directly.
    apply True.intro
  case inr h4 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h5
    -- True on the right can always be proven directly.
    apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_589105277599359946470708081244 : (((((p4 → (((p2 ∨ (p5 ∧ p5)) ∧ p5) ∧ ((False → (True → (p3 → (((p2 ∨ True) → p4) ∧ True)))) ∨ (p4 ∧ p5)))) ∨ False) ∧ p2) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_190959089011344486104640809340 : (((p3 ∨ (p3 ∨ (p4 ∨ p3))) ∧ ((p5 ∧ p1) ∧ p4)) ∨ ((p4 ∧ (p4 → p3)) ∨ ((p1 → p1) ∨ ((p2 → (p5 ∨ False)) ∧ (p3 ∧ p3))))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_635851227944788050710579589679 : ((((((p2 → False) ∨ ((p5 ∨ False) ∧ (p2 ∧ ((p2 ∨ (((p3 ∨ True) → True) → p2)) ∨ True)))) → ((False → (p3 ∧ False)) ∨ True)) → p3) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_720440785182104970900796372542 : (((((p2 ∧ (p3 → p2)) ∨ p1) → (p2 → ((True → (p4 ∧ p5)) ∨ ((p1 ∧ (p5 ∨ ((False ∨ p1) ∧ p4))) ∨ (True → (p1 ∨ True)))))) ∨ p4) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h3 =>
    -- Conjunctions on the left can always be decomposed.
    let h4 := h3.left
    let h5 := h3.right
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h6
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro
  case inr h7 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h8
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- One of the premise coincides with the conclusion.
    exact h7
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_321304727184926819399642207581 : (p4 ∨ (p5 ∨ (((((True ∨ p5) → p4) ∨ True) ∧ (((((p1 → p1) → (((p1 ∧ p1) ∨ True) ∨ p2)) ∨ p2) → p4) ∧ p3)) ∨ (False → p5)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_54424009776234136773733762724 : ((((((p3 ∨ p2) → (p2 ∧ p1)) → p2) ∨ False) ∨ (((p5 ∨ p4) → (p3 → p1)) → ((p4 → ((p4 ∨ p2) ∧ p4)) ∨ (p1 ∧ True)))) ∨ p1) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h2
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- One of the premise coincides with the conclusion.
  exact h2
  -- One of the premise coincides with the conclusion.
  exact h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_167823390008997024599882571810 : (((p1 ∨ (p5 → (p5 ∨ (p5 ∧ ((True ∨ p3) → True))))) ∧ (p2 → (p3 ∧ (p1 ∧ True)))) → ((p1 ∧ ((p2 ∧ p1) ∨ p1)) ∨ (False → p4))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- Disjunctions on the left can always be decomposed.
  cases h2
  case inl h4 =>
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Conjunctions on the right can always be decomposed.
    apply And.intro
    -- One of the premise coincides with the conclusion.
    exact h4
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h4
  case inr h5 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h6
    -- False on the left can always be used.
    apply False.elim h6



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_350581507385019201967100254864 : (p4 → (((((True ∧ True) → (p1 ∧ (False ∧ p5))) ∧ True) ∧ ((p5 ∧ p2) ∧ ((True → ((p5 ∨ ((True → p4) ∨ p1)) ∧ p2)) → True))) → p5)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Conjunctions on the left can always be decomposed.
  let h3 := h2.left
  let h4 := h2.right
  -- Conjunctions on the left can always be decomposed.
  let h5 := h3.left
  let h6 := h3.right
  -- Conjunctions on the left can always be decomposed.
  let h7 := h4.left
  let h8 := h4.right
  -- Conjunctions on the left can always be decomposed.
  let h9 := h7.left
  let h10 := h7.right
  -- One of the premise coincides with the conclusion.
  exact h9



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_175345663347463479646694237555 : ((p5 ∨ ((p2 → (True → ((((True ∨ p3) ∨ p2) ∨ (p3 ∧ p5)) ∧ p4))) → p1)) → (((((p5 ∨ False) ∨ (p4 ∧ True)) ∧ False) ∨ p4) → p4)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Disjunctions on the left can always be decomposed.
  cases h2
  case inl h3 =>
    -- Conjunctions on the left can always be decomposed.
    let h4 := h3.left
    let h5 := h3.right
    -- Disjunctions on the left can always be decomposed.
    cases h4
    case inl h6 =>
      -- Disjunctions on the left can always be decomposed.
      cases h6
      case inl h7 =>
        -- False on the left can always be used.
        apply False.elim h5
      case inr h8 =>
        -- False on the left can always be used.
        apply False.elim h8
    case inr h9 =>
      -- Conjunctions on the left can always be decomposed.
      let h10 := h9.left
      let h11 := h9.right
      -- False on the left can always be used.
      apply False.elim h5
  case inr h12 =>
    -- Disjunctions on the left can always be decomposed.
    cases h1
    case inl h13 =>
      -- One of the premise coincides with the conclusion.
      exact h12
    case inr h14 =>
      -- One of the premise coincides with the conclusion.
      exact h12



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_613173923277457957186727117477 : ((((((p1 ∧ (((p2 ∨ ((((True ∧ (True ∨ p4)) ∨ p3) ∧ p3) ∧ False)) → (False ∨ False)) ∧ True)) → (p3 → False)) → (p5 ∧ p2)) ∨ True) ∨ False) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_790725265962154195813432084611 : (((p5 ∨ (True → ((((p5 → (((True → (p5 ∨ (p1 ∨ p4))) ∧ p3) → p5)) ∧ (p1 ∨ p4)) ∨ p4) → (p4 ∨ ((p3 ∨ p4) ∨ False))))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_118222728179469068033291011520 : ((p1 ∨ ((((((p5 ∧ (p1 ∧ p4)) → p5) → p1) ∨ True) ∨ ((((((False ∨ p2) ∧ p2) → p4) ∨ False) ∨ False) ∧ True)) ∨ p4)) ∨ (True → p4)) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_652210699196544663388891204604 : ((((p2 ∧ (((True → ((p4 ∨ p3) ∨ ((p1 ∨ p3) ∨ p1))) → p1) ∨ (((p2 → (p3 → (p5 ∧ p4))) ∨ p3) ∧ False))) ∧ (True → p4)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_725850421637043349789275225533 : (((((True → False) ∧ p3) ∨ ((p4 ∧ (p2 ∧ p2)) ∧ (p4 ∨ ((p3 ∧ (p3 ∧ True)) → (False ∨ ((((p3 ∧ p3) ∧ p5) ∨ p4) ∧ True)))))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_253953818147721624646389875572 : ((p1 ∧ p4) → (True → (((p5 → p3) ∨ p1) ∧ ((((p1 ∧ p3) → p3) ∧ ((p5 ∨ (((p1 ∧ p5) → (p3 ∨ p4)) ∨ p5)) → p5)) ∨ p1)))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Conjunctions on the left can always be decomposed.
  let h3 := h1.left
  let h4 := h1.right
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h3
  -- Conjunctions on the left can always be decomposed.
  let h5 := h1.left
  let h6 := h1.right
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h5



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_299486700826613842142026066907 : (False ∨ ((p2 → ((((p4 ∨ p5) ∧ ((p5 ∧ p1) → p1)) ∧ p5) → (((((p5 → False) ∨ p1) ∨ False) → (p4 ∧ (p2 ∧ p3))) ∧ p2))) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_111589334483675423779811582940 : ((((p3 ∨ (((((p2 → p5) → (((p1 → True) ∧ p1) → p3)) → (p3 ∧ (False → (p4 ∨ p3)))) → p4) ∨ p3)) ∧ p1) ∨ True) ∨ (p1 ∨ p1)) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_187108118359153719966363287477 : (((p1 ∧ p3) ∨ ((True ∧ p4) → (p2 ∧ (p2 ∨ (p1 ∨ p2))))) → (((p3 ∨ (((p2 → p4) ∨ p1) ∨ p3)) ∨ p4) ∨ ((p5 → p1) → True))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h2 =>
    -- Conjunctions on the left can always be decomposed.
    let h3 := h2.left
    let h4 := h2.right
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- One of the premise coincides with the conclusion.
    exact h4
  case inr h5 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h6
    -- True on the right can always be proven directly.
    apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_304701686029553957884319697744 : (p1 ∨ ((((p3 ∨ p3) ∧ ((p3 ∧ (False ∨ (((False ∧ p4) ∧ ((p2 ∨ (p2 ∧ True)) ∧ p1)) → (False ∧ False)))) → p3)) → p1) ∨ (True ∨ p3))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_55618501231000346649617845140 : (((p3 → (((p5 → True) → False) → p1)) → (((((p2 ∨ ((True → (False ∨ (True ∧ (p1 ∧ p5)))) ∧ p2)) ∨ p2) ∧ p3) ∧ p2) ∧ p4)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_60606371644837613789334623854 : ((True ∧ ((p1 ∧ ((p1 ∧ p1) ∧ ((p4 → (p2 ∨ (False ∨ ((True → (p5 ∧ True)) → p4)))) ∧ (p2 ∨ (p4 ∨ True))))) ∧ (False → True))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_32994797781495972278758828038 : ((p3 ∨ ((p3 ∨ (p1 ∨ (p1 ∨ (p3 ∧ (((p3 ∨ p4) → p1) → (True ∨ p4)))))) ∨ ((False → (p5 ∧ (False → p5))) ∨ (False → p4)))) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- False on the left can always be used.
  apply False.elim h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_117170014923772728413835463562 : ((True ∧ ((((p5 ∨ (True ∧ ((((p3 ∨ p5) → p1) ∧ p3) → (True → p3)))) ∧ p3) ∨ ((p3 → (p2 ∧ p2)) ∨ p1)) → p3)) ∨ (False → p3)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_214109088459385511473230811452 : ((((p2 ∨ p2) ∨ p1) → p3) ∨ ((p2 ∧ ((p2 ∧ p2) ∨ True)) ∨ ((p5 → (True ∧ ((p1 ∨ False) ∨ (((False ∧ p5) ∨ p5) → p3)))) ∨ True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_218463223137840528709299294766 : (((p5 ∧ p2) → (p4 → False)) → ((((((True → p5) ∨ (True → False)) → ((p5 → False) → p5)) → p1) ∨ p4) ∨ ((p5 ∧ (p3 ∧ p1)) ∨ True))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_643058690840661126587062170979 : ((((p2 ∧ (p4 ∨ (((p4 → ((((p3 → (p1 ∧ ((False ∨ p4) ∨ True))) → (p1 → (True ∨ False))) → p3) ∧ p3)) ∧ p5) ∧ True))) → p1) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_62360718748416179408861727470 : ((p3 ∧ (((((False → True) → ((((p2 ∨ p5) ∧ True) → (p5 ∧ p3)) ∨ p3)) ∨ p3) → (p5 → p1)) → (((False ∨ p1) ∨ p2) ∨ p5))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_149218439004486019535082675551 : (((p2 ∧ True) ∨ (p1 ∨ ((True ∧ (p2 ∧ p2)) → (((p5 ∨ (p3 ∨ p5)) ∨ ((p4 → p2) ∧ p1)) ∧ False)))) ∨ (False → (p3 → (p4 ∨ p3)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_258822876817072123839005821287 : ((True → p1) → ((p4 → (p1 → ((p5 ∧ (p4 → ((p2 ∧ (False ∨ (p2 → ((p1 ∨ p5) ∧ True)))) ∧ (p2 → (p3 → p1))))) ∨ True))) ∧ True)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h2
  -- Implications on the right can always be decomposed.
  intro h3
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_44401887215097904757633883893 : (((((p1 ∨ (p1 ∨ (((True → ((False ∨ False) ∨ p1)) → False) ∧ p1))) ∧ p5) → ((False ∨ p5) ∧ ((True → p5) → (False ∧ p2)))) → p5) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_779448036222294594800174971658 : (((p2 ∨ (((p4 → ((True → p1) ∨ ((((False → p1) ∨ False) ∧ (p1 → (p2 → (p2 → p4)))) ∧ (p2 → False)))) ∨ (p2 → p4)) ∨ True)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_301268318686262371044607863286 : (False ∨ ((p4 ∨ (False ∨ (p5 ∨ (p4 ∨ True)))) ∨ ((p3 → ((((p3 → ((p1 → p1) ∨ p5)) → True) ∧ ((p2 → p3) ∧ False)) → p1)) ∧ p2))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_261073507991061451971114179560 : ((p4 → p3) → ((((False ∨ p3) → p2) → ((p4 → p4) ∧ ((p2 → ((p2 ∧ p2) ∧ False)) ∧ ((p2 → (False ∧ (p2 ∨ True))) ∧ p1)))) ∨ True)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_54654533410671457588152650939 : (((((True ∨ (p3 ∨ p5)) ∨ (p1 ∧ p5)) ∨ p4) → (((p3 → ((True → False) ∨ (((False ∨ (False → p4)) → p5) ∨ p5))) ∨ True) ∨ p3)) ∨ p3) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h2 =>
    -- Disjunctions on the left can always be decomposed.
    cases h2
    case inl h3 =>
      -- Disjunctions on the left can always be decomposed.
      cases h3
      case inl h4 =>
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- True on the right can always be proven directly.
        apply True.intro
      case inr h5 =>
        -- Disjunctions on the left can always be decomposed.
        cases h5
        case inl h6 =>
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- One of the premise coincides with the conclusion.
          exact h6
        case inr h7 =>
          -- Show the left disjunct based on <expert-advice>.
          apply Or.inl
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- True on the right can always be proven directly.
          apply True.intro
    case inr h8 =>
      -- Conjunctions on the left can always be decomposed.
      let h9 := h8.left
      let h10 := h8.right
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- True on the right can always be proven directly.
      apply True.intro
  case inr h11 =>
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_47302214942639139826761850035 : ((((p4 ∨ (p4 → p3)) ∧ (((p2 ∨ p1) ∧ ((p5 ∨ ((False → (p3 ∧ ((p1 → p4) → p3))) ∧ True)) ∧ p4)) ∨ p3)) ∨ (True ∨ p1)) ∨ p1) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_118839424288859508670427845161 : ((True → (((p1 → (((True → p1) ∧ ((p3 → False) ∧ p1)) ∨ (p5 ∨ (p5 ∨ (p4 → p5))))) → p2) ∧ (False → (p5 ∧ p4)))) ∨ (False ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_55843779135575267030984460321 : (((p1 ∧ (p2 ∨ (p2 → p2))) ∧ (((p4 ∧ (p2 ∧ (p1 → p3))) ∧ True) → (False ∨ ((((p1 ∨ (p1 ∨ True)) ∧ p3) ∧ p5) ∨ p3)))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_746198541599295050004522986993 : ((((p1 ∨ p3) → (((p1 ∨ p1) ∧ p5) ∨ ((p4 → (p2 ∧ p4)) ∨ (p1 ∨ ((p3 ∧ (p5 → p5)) → (True ∧ ((False ∧ False) ∨ p3))))))) ∨ p3) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h2 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- One of the premise coincides with the conclusion.
    exact h2
  case inr h3 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h4
    -- Conjunctions on the right can always be decomposed.
    apply And.intro
    -- True on the right can always be proven directly.
    apply True.intro
    -- Conjunctions on the left can always be decomposed.
    let h5 := h4.left
    let h6 := h4.right
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h5
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_700385178250656738847224583758 : ((((p5 ∧ (((p2 → ((p2 ∧ (p2 ∧ p4)) ∧ p5)) ∨ p3) ∧ p2)) → (p3 ∧ ((True ∧ ((p5 ∨ ((p5 → p1) ∨ p4)) ∧ p2)) ∧ p4))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_260241543046449258402798344035 : ((p2 → p3) → (((((((True ∧ p5) ∨ p3) ∧ p5) → p3) → p2) ∧ ((p1 ∧ (p5 ∧ p4)) ∧ p4)) → (p3 ∨ (p3 → (False ∨ (p3 → p2)))))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Conjunctions on the left can always be decomposed.
  let h3 := h2.left
  let h4 := h2.right
  -- Conjunctions on the left can always be decomposed.
  let h5 := h4.left
  let h6 := h4.right
  -- Conjunctions on the left can always be decomposed.
  let h7 := h5.left
  let h8 := h5.right
  -- Conjunctions on the left can always be decomposed.
  let h9 := h8.left
  let h10 := h8.right
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h11
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h12
  -- We want to use the implication h3 based on <expert-advice>. So we show its premise.
  have h13 : ((((True ∧ p5) ∨ p3) ∧ p5) → p3) := by
    -- Implications on the right can always be decomposed.
    intro h14
    -- Conjunctions on the left can always be decomposed.
    let h15 := h14.left
    let h16 := h14.right
    -- Disjunctions on the left can always be decomposed.
    cases h15
    case inl h17 =>
      -- Conjunctions on the left can always be decomposed.
      let h18 := h17.left
      let h19 := h17.right
      -- One of the premise coincides with the conclusion.
      exact h12
    case inr h20 =>
      -- One of the premise coincides with the conclusion.
      exact h20
  -- We have shown the premise of h3, we can now drive its conclusion.
  let h21 := h3 h13
  -- One of the premise coincides with the conclusion.
  exact h21



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_792303364870290869476808576327 : (((True → (((((False → (p2 → (True ∧ p2))) → p2) → p4) → ((p5 → p5) → (p3 ∧ False))) ∨ ((p3 → True) ∨ ((False ∨ p2) ∧ p3)))) ∨ p3) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h2
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_231144529619571845730721298810 : (((p1 ∨ p4) ∨ p5) → (((p2 → p5) ∧ True) ∨ ((True ∨ (p3 ∧ (p5 ∧ p1))) → (p4 → ((True → (False ∨ ((True ∨ p4) ∨ p3))) ∨ p2))))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h2 =>
    -- Disjunctions on the left can always be decomposed.
    cases h2
    case inl h3 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Implications on the right can always be decomposed.
      intro h4
      -- Implications on the right can always be decomposed.
      intro h5
      -- Disjunctions on the left can always be decomposed.
      cases h4
      case inl h6 =>
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- Implications on the right can always be decomposed.
        intro h7
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- True on the right can always be proven directly.
        apply True.intro
      case inr h8 =>
        -- Conjunctions on the left can always be decomposed.
        let h9 := h8.left
        let h10 := h8.right
        -- Conjunctions on the left can always be decomposed.
        let h11 := h10.left
        let h12 := h10.right
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- Implications on the right can always be decomposed.
        intro h13
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- One of the premise coincides with the conclusion.
        exact h9
    case inr h14 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Implications on the right can always be decomposed.
      intro h15
      -- Implications on the right can always be decomposed.
      intro h16
      -- Disjunctions on the left can always be decomposed.
      cases h15
      case inl h17 =>
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- Implications on the right can always be decomposed.
        intro h18
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- True on the right can always be proven directly.
        apply True.intro
      case inr h19 =>
        -- Conjunctions on the left can always be decomposed.
        let h20 := h19.left
        let h21 := h19.right
        -- Conjunctions on the left can always be decomposed.
        let h22 := h21.left
        let h23 := h21.right
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- Implications on the right can always be decomposed.
        intro h24
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- One of the premise coincides with the conclusion.
        exact h20
  case inr h25 =>
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Conjunctions on the right can always be decomposed.
    apply And.intro
    -- Implications on the right can always be decomposed.
    intro h26
    -- One of the premise coincides with the conclusion.
    exact h25
    -- True on the right can always be proven directly.
    apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_606674540961879543179936157927 : ((((((((False ∨ True) ∨ ((False ∨ ((True → p1) ∨ (p4 ∧ p1))) ∨ (p4 ∧ p3))) ∧ ((p4 ∨ p1) ∧ p2)) ∧ (p2 ∨ False)) ∧ True) ∨ True) ∨ p2) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_654948275975327619951581300945 : ((((((((p2 ∧ False) ∧ p1) ∧ p5) ∨ ((((True → p1) → p2) ∧ (p3 ∨ False)) → ((p3 ∨ (p5 ∧ p4)) → p4))) → p1) ∨ (True ∨ p3)) ∨ p4) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_299261736063571495856622902586 : (False ∨ ((((p4 ∨ (((p4 → p2) ∨ (p3 ∨ p1)) ∨ (True → (p3 → p2)))) → (p5 → (True ∧ False))) → ((True ∧ p2) ∨ (p1 ∧ True))) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_622836633336713501993027669873 : ((((p5 ∧ ((p1 → ((((p3 ∨ ((p4 ∨ ((p5 → True) → True)) ∨ p5)) ∧ True) → (True ∨ False)) → (p3 ∧ (p1 ∨ p4)))) ∧ p4)) ∨ True) ∨ p2) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_134536745801779419962308569389 : ((((((p5 → (p3 ∧ ((((p2 ∧ ((True ∧ False) ∨ False)) ∨ True) ∨ p3) ∧ p5))) ∧ p1) ∨ (True ∨ p2)) → False) → False) ∨ ((False ∧ p5) ∧ p5)) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h2 : (((p5 → (p3 ∧ ((((p2 ∧ ((True ∧ False) ∨ False)) ∨ True) ∨ p3) ∧ p5))) ∧ p1) ∨ (True ∨ p2)) := by
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h3 := h1 h2
  -- False on the left can always be used.
  apply False.elim h3



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_314558470746708482178298171575 : (p3 ∨ ((p1 ∧ ((((((True → p1) ∧ p5) → p3) ∧ p3) ∧ p3) ∨ (p4 ∨ ((False ∨ p1) ∧ True)))) ∨ (False → (((p5 ∨ p1) ∧ p4) ∧ p5)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- False on the left can always be used.
  apply False.elim h1
  -- False on the left can always be used.
  apply False.elim h1
  -- False on the left can always be used.
  apply False.elim h1



