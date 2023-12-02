variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_189143768003330677274487177928 : (((p5 ∨ True) ∧ ((((False → p1) ∨ p1) ∨ p5) ∨ False)) ∧ ((p3 ∨ ((False ∨ p1) → ((p4 ∧ p3) ∨ (((p4 ∨ p1) ∨ p1) ∨ p1)))) ∨ p2)) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- False on the left can always be used.
  apply False.elim h1
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h2
  -- Disjunctions on the left can always be decomposed.
  cases h2
  case inl h3 =>
    -- False on the left can always be used.
    apply False.elim h3
  case inr h4 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h4



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_665339552173845190335800993208 : ((((((p1 ∨ p5) ∨ (p1 → ((p1 ∧ (p1 → (p3 ∨ (p1 → ((p5 ∨ (p2 ∨ p5)) → p5))))) ∧ p5))) ∧ p2) ∧ (p5 ∨ (p1 ∨ p4))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_703076681707050114347045717408 : (((((p2 ∧ p1) ∨ ((True ∧ False) ∧ ((p3 ∧ p2) ∨ p3))) ∨ (((((False ∨ p2) ∨ (True ∨ p2)) ∨ (True ∧ p2)) ∨ p2) ∧ (p4 ∧ p1))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_184326323950619488681722736248 : ((((True ∨ p2) → ((p1 ∨ ((p4 → p1) ∧ p1)) ∧ False)) → p4) ∨ ((((True → True) → p4) ∨ (True → p4)) → (True ∨ ((p3 → p5) ∨ p1)))) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h2 : (True ∨ p2) := by
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h3 := h1 h2
  -- We need to get the right conjuct of h3 based on <expert-advice>.
  let h4 := h3.right
  -- False on the left can always be used.
  apply False.elim h4



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_94391007011805844124316430238 : ((p2 ∧ ((True ∧ p4) ∧ (((((p3 ∨ (p3 ∧ p5)) ∨ True) ∧ (p5 → ((p2 → p3) ∨ p5))) → p3) ∧ (((True ∧ p5) ∨ p2) → p2)))) → p3) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- Conjunctions on the left can always be decomposed.
  let h4 := h3.left
  let h5 := h3.right
  -- Conjunctions on the left can always be decomposed.
  let h6 := h4.left
  let h7 := h4.right
  -- Conjunctions on the left can always be decomposed.
  let h8 := h5.left
  let h9 := h5.right
  -- We want to use the implication h8 based on <expert-advice>. So we show its premise.
  have h10 : (((p3 ∨ (p3 ∧ p5)) ∨ True) ∧ (p5 → ((p2 → p3) ∨ p5))) := by
    -- Conjunctions on the right can always be decomposed.
    apply And.intro
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro
    -- Implications on the right can always be decomposed.
    intro h11
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h11
  -- We have shown the premise of h8, we can now drive its conclusion.
  let h12 := h8 h10
  -- One of the premise coincides with the conclusion.
  exact h12



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_337650750395836914405505072344 : (p1 → ((((p2 ∨ (True ∧ (p3 ∧ (((p3 → (False → p4)) → p5) ∨ False)))) ∨ (p3 → p4)) ∨ False) ∨ (True ∨ (False → ((False → True) → p1))))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_159206107335220464433757492415 : ((p2 → (((((p1 → (p5 ∧ p3)) ∨ p2) ∨ (True ∨ True)) ∨ p4) → (False ∧ (p1 ∧ (p3 ∧ p4))))) ∨ (p2 → (((True ∨ p4) ∨ p4) → p2))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Disjunctions on the left can always be decomposed.
  cases h2
  case inl h3 =>
    -- Disjunctions on the left can always be decomposed.
    cases h3
    case inl h4 =>
      -- One of the premise coincides with the conclusion.
      exact h1
    case inr h5 =>
      -- One of the premise coincides with the conclusion.
      exact h1
  case inr h6 =>
    -- One of the premise coincides with the conclusion.
    exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_319056801599141680550688451425 : (p4 ∨ ((True ∧ (p3 ∨ ((p5 → ((p5 ∧ ((p1 → p5) → p3)) ∨ (True ∨ ((p1 ∨ p4) → False)))) ∨ p1))) ∨ (p3 ∨ ((False ∧ p5) → p3)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- False on the left can always be used.
  apply False.elim h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_172838011300107113674834228528 : ((False ∧ (((p1 ∧ ((((False ∨ p5) ∧ p2) ∧ p2) ∨ (p3 ∧ p1))) ∨ p3) ∨ True)) ∨ (p3 ∨ ((p4 ∧ (p2 ∧ (p5 → (True ∨ p4)))) → True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_205212121913863808873278394507 : (((p5 → (p3 ∨ p3)) ∧ (p4 ∧ p3)) ∨ ((((p1 ∨ (p4 ∧ p5)) → p5) → (p1 → (p2 ∨ p4))) ∨ (False → ((p5 ∧ (True ∨ p2)) ∨ p2)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_174525884589152644158075391140 : ((((p3 ∧ (p5 ∨ (p3 ∧ p5))) ∨ p5) → (p4 ∧ ((True → p2) → (p1 → False)))) → ((p4 ∨ ((True ∨ False) ∧ p4)) ∨ ((p3 ∧ p5) → p3))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h2
  -- Conjunctions on the left can always be decomposed.
  let h3 := h2.left
  let h4 := h2.right
  -- One of the premise coincides with the conclusion.
  exact h3



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_60523634920658594987111802804 : ((True ∧ ((((p2 ∧ ((False ∨ False) ∨ (((True → (True ∨ p2)) → ((p1 ∨ p1) ∨ True)) ∨ (p1 ∧ (False ∨ p3))))) ∨ p5) ∨ p4) ∨ p5)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_165449196263512106585145198791 : ((((False → ((p5 ∧ (True ∧ (False ∧ p3))) ∧ p5)) ∨ True) ∧ ((p3 ∨ p2) → (p4 ∨ False))) ∨ (True → (p1 → ((p3 → (p1 ∧ p4)) ∨ True)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_152311458313018150007624043155 : ((((p3 → (p3 ∧ p5)) ∨ p4) ∧ ((((((p4 ∧ (p1 ∧ (p2 ∨ True))) → True) → False) ∨ p5) → p1) ∨ False)) → ((p2 ∧ p4) ∨ (p5 ∨ True))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- Disjunctions on the left can always be decomposed.
  cases h2
  case inl h4 =>
    -- Disjunctions on the left can always be decomposed.
    cases h3
    case inl h5 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- True on the right can always be proven directly.
      apply True.intro
    case inr h6 =>
      -- False on the left can always be used.
      apply False.elim h6
  case inr h7 =>
    -- Disjunctions on the left can always be decomposed.
    cases h3
    case inl h8 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- True on the right can always be proven directly.
      apply True.intro
    case inr h9 =>
      -- False on the left can always be used.
      apply False.elim h9



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_712258089811963923777936822120 : ((((((p2 ∨ False) ∨ (p3 → p3)) → False) ∨ (p2 → (p3 ∨ (p1 ∧ (p3 ∧ ((p5 ∧ (p1 → p2)) ∨ ((p3 ∧ True) ∧ (p5 ∧ p4)))))))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_723264633522783438971001298202 : (((((p3 → p3) ∨ p4) ∧ ((p2 ∧ p3) ∧ ((((p3 ∨ ((False ∧ (p1 ∨ p4)) ∧ (p4 ∧ p1))) ∧ (p4 ∧ p1)) → False) → (p5 → p4)))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_729959886348188176353961534883 : (((((p5 ∧ True) → False) → (p2 ∧ (p5 ∨ (p1 → ((((p1 → p5) ∧ p4) ∨ p3) ∨ (((p5 ∧ p4) ∨ p5) ∧ (True ∧ (False → p3)))))))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_316369844337323946574285288992 : (p3 ∨ (False ∨ ((p4 → (((p5 → (((False → p1) → p1) ∨ False)) → p5) ∨ (p3 → (True → ((True ∧ (p2 ∨ p2)) ∨ (p3 ∨ p2)))))) ∨ p2))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h2
  -- Implications on the right can always be decomposed.
  intro h3
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- One of the premise coincides with the conclusion.
  exact h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_143366086436015902160026438659 : ((p5 → (((p3 ∧ (p5 ∨ (p3 → (p4 ∧ (p4 ∨ False))))) ∧ ((p1 ∨ True) ∨ ((p2 → (p2 ∨ p4)) ∨ p1))) ∧ True)) → ((p3 ∨ True) ∧ True)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_57913612104203511972243609185 : (((p5 ∨ (p2 ∧ True)) → ((((((False ∧ ((p1 ∨ p3) → p4)) → (p3 ∨ (p2 ∧ ((p2 ∨ False) ∧ p1)))) ∨ True) ∧ p4) ∨ p1) → p1)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_701501930645498797419679209940 : (((((p4 ∨ (p4 → True)) ∨ ((p2 ∧ (p1 → p2)) → True)) ∧ (p3 ∨ ((((True → p3) ∨ (p1 ∧ (p1 ∨ p3))) ∨ p1) ∧ (p3 → True)))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_47016169133766336557896159457 : ((((p5 ∧ ((p3 ∧ (p5 → (p3 ∧ ((p4 ∧ False) ∧ p3)))) ∧ ((p3 ∧ p5) ∧ ((p1 ∧ (p3 ∨ False)) → True)))) → False) ∨ (p5 ∨ p5)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_177749804032177564339314438334 : ((((p2 ∨ p5) ∧ (True → (p3 → (((False → p2) → False) ∧ p5)))) ∧ p5) ∨ ((True ∧ (p4 → (p1 → True))) → (False ∨ (True → (p1 → p1))))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h4
  -- Implications on the right can always be decomposed.
  intro h5
  -- One of the premise coincides with the conclusion.
  exact h5



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_648230576690936973356182313411 : (((((p1 ∨ ((p1 ∨ ((True ∨ (p1 ∨ (True ∨ (((p2 ∨ (True ∨ (p3 ∨ False))) ∨ p5) ∨ False)))) ∨ True)) → p5)) ∧ p2) ∧ (p2 → p4)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_60323144679719945269563204475 : (((p2 → True) → (((((False ∧ p4) ∨ False) ∧ ((((p3 → ((True → (p1 ∧ True)) ∧ p4)) ∧ False) ∨ p1) ∨ (p5 ∧ True))) ∨ p3) ∨ p4)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_756612474922939774175733963882 : (((p1 ∧ (((False → (p2 ∧ ((((p5 → (False ∨ p1)) ∧ True) ∧ True) ∧ (p5 ∧ p4)))) ∨ p2) → ((p1 → (True ∨ (True ∧ p1))) ∧ p5))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_60342270715388432887328477890 : (((p2 → p2) → (((True → False) ∧ (p1 → ((p5 ∧ (False → p2)) ∨ p3))) → (p1 ∧ ((p1 → (p2 → False)) ∨ ((False → False) ∨ p2))))) ∨ p1) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Conjunctions on the left can always be decomposed.
  let h3 := h2.left
  let h4 := h2.right
  -- We want to use the implication h3 based on <expert-advice>. So we show its premise.
  have h5 : True := by
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h3, we can now drive its conclusion.
  let h6 := h3 h5
  -- False on the left can always be used.
  apply False.elim h6
  -- Conjunctions on the left can always be decomposed.
  let h7 := h2.left
  let h8 := h2.right
  -- We want to use the implication h7 based on <expert-advice>. So we show its premise.
  have h9 : True := by
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h7, we can now drive its conclusion.
  let h10 := h7 h9
  -- False on the left can always be used.
  apply False.elim h10



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_311270527286561595818296420696 : (p2 ∨ (True ∧ (((((((True ∨ p3) ∨ (p1 → (False ∨ p1))) → (p3 ∨ p3)) → False) ∨ True) → (p2 ∨ (p1 ∧ (p2 ∧ p4)))) → (p1 ∨ p2)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- Implications on the right can always be decomposed.
  intro h1
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h2 : (((((True ∨ p3) ∨ (p1 → (False ∨ p1))) → (p3 ∨ p3)) → False) ∨ True) := by
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h3 := h1 h2
  -- Disjunctions on the left can always be decomposed.
  cases h3
  case inl h4 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h4
  case inr h5 =>
    -- Conjunctions on the left can always be decomposed.
    let h6 := h5.left
    let h7 := h5.right
    -- Conjunctions on the left can always be decomposed.
    let h8 := h7.left
    let h9 := h7.right
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- One of the premise coincides with the conclusion.
    exact h6



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_198598572271829451650520554907 : ((p2 ∨ (((p4 → (p2 ∨ p4)) ∨ p2) → p2)) ∨ (((((((False ∧ p4) ∨ p4) → ((p4 ∨ p3) → p5)) ∨ (p1 → True)) ∧ p3) ∨ True) ∧ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_352304387291875537071325829784 : (p4 → ((p5 → (p2 ∨ (p2 ∨ p1))) → (((p5 ∧ ((p1 ∧ p1) ∧ ((p1 ∧ (((True ∨ (p5 ∨ p1)) ∨ False) ∨ p1)) ∧ p1))) ∨ p5) ∨ True))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_158994604192836728169301848377 : ((p3 ∨ (p5 ∧ (((p4 → (p2 → ((p4 → True) ∨ (p4 → (p5 ∨ False))))) → (p1 ∨ p3)) ∨ False))) ∨ (True ∨ (p1 ∨ (p5 → (False ∨ p4))))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_63172770372978442991202756060 : ((p5 ∧ (((p1 → (((p4 ∨ False) ∧ (p3 ∧ (p1 ∨ (p1 ∧ ((p5 ∧ ((p5 ∨ p5) ∧ p1)) ∧ p1))))) ∧ True)) ∨ p1) → (p4 ∧ p2))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_793158433788606465810644106749 : (((True → (True ∧ ((False ∧ p3) ∧ (p2 ∨ ((p1 ∨ (((p3 → ((p1 ∧ (p2 ∨ p4)) ∨ False)) ∧ (False → p1)) ∨ (p1 → p2))) ∧ p2))))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_40971867015577767655029712662 : (((((p3 ∨ (p4 ∨ p1)) ∧ (True ∨ ((p4 ∧ (((p3 → ((p2 → p3) ∨ (p5 ∧ p3))) ∨ p2) ∨ p3)) ∧ True))) ∨ (p3 ∧ False)) ∨ True) ∨ p5) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_149232380799006470003924249343 : (((p5 ∧ False) ∨ (p3 ∧ (p1 ∧ ((((p2 ∨ (p5 ∨ p4)) ∨ p4) → True) ∧ ((True → False) → (p2 ∧ p4)))))) ∨ ((False → (True ∧ p4)) ∧ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- False on the left can always be used.
  apply False.elim h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_347313969292260718392965311387 : (p3 → ((((p4 ∧ (p4 ∧ True)) ∧ (p3 ∧ p2)) → (p1 ∧ p2)) → (p1 → ((p1 ∧ (p5 → (p4 ∧ (p5 → p5)))) ∨ (p1 ∨ (p4 ∧ p3)))))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Implications on the right can always be decomposed.
  intro h3
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- One of the premise coincides with the conclusion.
  exact h3



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_299168084552965296458206439659 : (False ∨ ((((((p1 → (p5 ∨ p4)) ∧ (((False ∧ p3) ∧ ((p3 → p3) ∧ ((p1 ∨ p4) ∨ p3))) → (p5 → p1))) → p5) → False) → False) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_1495414679299676998065907383 : ((((((((p4 → (p3 ∨ True)) → p4) → p3) → p5) ∨ ((p3 ∨ p4) → p3)) ∧ (p1 → (False ∨ p1))) → (p3 ∨ p2)) ∨ (True ∨ False)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_382592728863309015404769995845 : (((((((p3 ∧ p5) ∨ (p4 → (p1 ∧ True))) → (p5 ∨ (p5 ∨ (p5 ∨ (((p1 ∨ ((p1 ∧ True) ∨ False)) ∨ p3) ∧ p4))))) ∨ True) ∨ p5) ∧ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
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
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_224289716532247353931164148345 : ((False → (p3 ∧ p5)) ∧ (((p4 → p5) → ((((p4 ∨ (p3 ∨ p3)) ∨ p1) → ((p1 → p2) ∧ ((p3 ∧ p1) → False))) ∧ p3)) ∨ (True ∨ p4))) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- False on the left can always be used.
  apply False.elim h1
  -- False on the left can always be used.
  apply False.elim h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_765679749450205489224684874774 : (((p4 ∧ (((p4 → (p5 → (p1 → p2))) ∨ (p3 ∧ ((p1 → p2) ∧ p3))) → (((p2 ∨ p2) ∨ (p5 → (p4 ∨ p3))) ∨ (p4 ∧ p3)))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_227681780334383304146438002403 : ((False ∧ (p5 → True)) ∨ (p3 → (True → (p1 ∨ (((p2 ∨ p4) ∨ (p2 ∨ False)) ∨ (True ∧ (False ∨ ((False → (p3 ∨ (False ∧ True))) ∨ p5)))))))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h3
  -- False on the left can always be used.
  apply False.elim h3



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_147172268168807916289379424674 : (((False ∨ (((p2 → p1) → ((p4 ∧ True) ∨ (p2 ∧ True))) → ((p5 ∧ (p3 ∨ (p5 ∧ p5))) ∨ True))) ∧ True) ∨ (p3 → ((p2 ∧ False) ∧ p2))) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_116564583697078466998576808963 : (((p2 ∨ p2) ∧ (((p2 ∨ p5) ∧ ((p3 ∨ ((p2 ∧ p3) ∨ (p1 ∨ (p5 ∨ p2)))) → p4)) ∨ (((p2 ∨ p2) ∨ p2) ∧ p3))) ∨ (False → p3)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_180434025300242323703922852171 : (((((p5 ∨ False) ∨ (True ∨ (p5 → False))) ∧ (p2 → p2)) → (False ∧ p3)) → ((((p5 ∧ p2) ∧ p1) → p1) ∧ ((p1 → False) ∧ (p1 → False)))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h2
  -- Conjunctions on the left can always be decomposed.
  let h3 := h2.left
  let h4 := h2.right
  -- Conjunctions on the left can always be decomposed.
  let h5 := h3.left
  let h6 := h3.right
  -- One of the premise coincides with the conclusion.
  exact h4
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h7
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h8 : (((p5 ∨ False) ∨ (True ∨ (p5 → False))) ∧ (p2 → p2)) := by
    -- Conjunctions on the right can always be decomposed.
    apply And.intro
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- True on the right can always be proven directly.
    apply True.intro
    -- Implications on the right can always be decomposed.
    intro h9
    -- One of the premise coincides with the conclusion.
    exact h9
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h10 := h1 h8
  -- We need to get the left conjuct of h10 based on <expert-advice>.
  let h11 := h10.left
  -- False on the left can always be used.
  apply False.elim h11
  -- Implications on the right can always be decomposed.
  intro h12
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h13 : (((p5 ∨ False) ∨ (True ∨ (p5 → False))) ∧ (p2 → p2)) := by
    -- Conjunctions on the right can always be decomposed.
    apply And.intro
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- True on the right can always be proven directly.
    apply True.intro
    -- Implications on the right can always be decomposed.
    intro h14
    -- One of the premise coincides with the conclusion.
    exact h14
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h15 := h1 h13
  -- We need to get the left conjuct of h15 based on <expert-advice>.
  let h16 := h15.left
  -- False on the left can always be used.
  apply False.elim h16



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_148303575221132998509048888563 : ((((p4 ∧ (p1 → True)) → (p5 → ((p1 ∧ (p3 ∧ True)) ∧ ((p2 ∧ p5) → p4)))) → (p3 ∧ (p5 ∨ True))) ∨ (p3 → (p5 → (True ∨ True)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_123907619235972847943592370680 : ((((((p5 ∨ False) ∨ False) ∨ ((False ∧ (p5 → p3)) → True)) ∨ p3) ∧ (p4 ∧ (p1 ∧ (p3 ∨ ((p3 ∨ False) ∧ (False → p2)))))) → (p2 → p2)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Conjunctions on the left can always be decomposed.
  let h3 := h1.left
  let h4 := h1.right
  -- Disjunctions on the left can always be decomposed.
  cases h3
  case inl h5 =>
    -- Disjunctions on the left can always be decomposed.
    cases h5
    case inl h6 =>
      -- Disjunctions on the left can always be decomposed.
      cases h6
      case inl h7 =>
        -- Disjunctions on the left can always be decomposed.
        cases h7
        case inl h8 =>
          -- Conjunctions on the left can always be decomposed.
          let h9 := h4.left
          let h10 := h4.right
          -- Conjunctions on the left can always be decomposed.
          let h11 := h10.left
          let h12 := h10.right
          -- Disjunctions on the left can always be decomposed.
          cases h12
          case inl h13 =>
            -- One of the premise coincides with the conclusion.
            exact h2
          case inr h14 =>
            -- Conjunctions on the left can always be decomposed.
            let h15 := h14.left
            let h16 := h14.right
            -- Disjunctions on the left can always be decomposed.
            cases h15
            case inl h17 =>
              -- One of the premise coincides with the conclusion.
              exact h2
            case inr h18 =>
              -- False on the left can always be used.
              apply False.elim h18
        case inr h19 =>
          -- False on the left can always be used.
          apply False.elim h19
      case inr h20 =>
        -- False on the left can always be used.
        apply False.elim h20
    case inr h21 =>
      -- Conjunctions on the left can always be decomposed.
      let h22 := h4.left
      let h23 := h4.right
      -- Conjunctions on the left can always be decomposed.
      let h24 := h23.left
      let h25 := h23.right
      -- Disjunctions on the left can always be decomposed.
      cases h25
      case inl h26 =>
        -- One of the premise coincides with the conclusion.
        exact h2
      case inr h27 =>
        -- Conjunctions on the left can always be decomposed.
        let h28 := h27.left
        let h29 := h27.right
        -- Disjunctions on the left can always be decomposed.
        cases h28
        case inl h30 =>
          -- One of the premise coincides with the conclusion.
          exact h2
        case inr h31 =>
          -- False on the left can always be used.
          apply False.elim h31
  case inr h32 =>
    -- Conjunctions on the left can always be decomposed.
    let h33 := h4.left
    let h34 := h4.right
    -- Conjunctions on the left can always be decomposed.
    let h35 := h34.left
    let h36 := h34.right
    -- Disjunctions on the left can always be decomposed.
    cases h36
    case inl h37 =>
      -- One of the premise coincides with the conclusion.
      exact h2
    case inr h38 =>
      -- Conjunctions on the left can always be decomposed.
      let h39 := h38.left
      let h40 := h38.right
      -- Disjunctions on the left can always be decomposed.
      cases h39
      case inl h41 =>
        -- One of the premise coincides with the conclusion.
        exact h2
      case inr h42 =>
        -- False on the left can always be used.
        apply False.elim h42



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_113076863463525134168186867697 : (((p4 ∨ (((False ∨ (((False ∨ (p3 ∧ (p1 ∧ True))) → ((p2 → False) → p4)) → False)) ∨ (True → (p1 ∧ p4))) ∧ p5)) → False) ∨ (True → True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_631771282411957869956730655525 : ((((((p4 ∧ ((p3 → (((p2 ∨ False) ∨ False) → p5)) → p5)) ∨ (((p1 → ((True ∨ True) → (p5 ∨ p5))) → p3) → False)) → p4) → p3) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_116166002056594578983614716835 : (((True → (p2 ∧ False)) ∧ (((p3 ∧ (p3 → (p4 ∧ p5))) → (((False ∧ p5) ∨ True) ∧ (((p1 ∧ p2) ∨ p4) ∨ p2))) ∨ True)) ∨ (False → p5)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_180737049531637935388026552918 : ((((p5 ∧ (p2 → p5)) ∨ p3) ∨ (False ∧ (((p5 → p5) → True) ∨ p1))) → ((p4 → ((p4 → (p5 ∧ p3)) ∨ (p5 ∨ (True ∨ p2)))) ∨ p3)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h2 =>
    -- Disjunctions on the left can always be decomposed.
    cases h2
    case inl h3 =>
      -- Conjunctions on the left can always be decomposed.
      let h4 := h3.left
      let h5 := h3.right
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- Implications on the right can always be decomposed.
      intro h6
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- One of the premise coincides with the conclusion.
      exact h4
    case inr h7 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- One of the premise coincides with the conclusion.
      exact h7
  case inr h8 =>
    -- Conjunctions on the left can always be decomposed.
    let h9 := h8.left
    let h10 := h8.right
    -- False on the left can always be used.
    apply False.elim h9



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_355623857421964093853385191860 : (p5 → ((False ∨ ((False ∧ (True ∧ (((p2 → ((p5 ∧ p4) ∧ False)) ∨ (False ∧ (True ∧ p2))) ∨ ((p1 ∧ p5) → p1)))) ∨ False)) ∨ (p1 → p1))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h2
  -- One of the premise coincides with the conclusion.
  exact h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_39445662057783806855099792142 : (((p5 ∧ ((((p5 ∧ (p3 ∨ (True → (p2 → p5)))) ∨ True) ∧ (p3 ∧ (p1 ∧ ((p4 ∨ False) → p1)))) ∧ ((p5 ∨ True) ∧ p1))) ∧ p4) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_118881519322016238834311942782 : ((True → ((p5 → p5) → ((p4 ∧ (((p5 ∧ (p4 ∧ ((False ∧ p2) ∧ p5))) ∨ False) ∨ (True ∨ (p3 ∧ True)))) ∨ (False ∨ p1)))) ∨ (p1 ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_658101787863306830910655981549 : ((((p3 ∧ (p1 ∨ (((p5 ∨ ((p5 ∨ p4) → ((p1 ∧ p4) ∨ p3))) → p1) ∧ ((p1 ∧ p5) → (True ∨ (p1 ∧ p4)))))) ∨ (True ∨ p3)) ∨ False) ∧ True) := by
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
theorem thm_5_vars_303802731919883905834572899095 : (p1 ∨ ((((((p5 ∧ (p5 ∧ (False ∧ p5))) ∧ (True ∧ p4)) ∧ p4) → ((p4 → (p1 → (p1 → ((True ∨ p4) → p2)))) → True)) → p2) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_348883227534781973224683679993 : (p3 → (p2 ∨ ((p5 ∨ p2) ∨ (p5 ∨ (((p1 → (True → True)) ∧ p1) ∨ ((((p2 ∧ p1) ∧ (p1 → (p5 → p5))) ∨ (p3 ∧ p3)) ∨ False)))))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- One of the premise coincides with the conclusion.
  exact h1
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_181602343336886356670791760307 : ((p1 → (p4 → (((False → ((p1 → p2) ∨ False)) ∨ (p3 → p1)) → p2))) → (((((p1 ∨ (p2 → False)) → p4) ∨ (p5 ∧ p2)) ∨ p1) ∨ True)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_115998621231117946258035588577 : ((((True → (p2 → p1)) → p2) → (((((p2 ∧ (True ∨ p1)) ∧ (p4 → (False ∧ p4))) → (p5 ∧ p3)) ∧ (p1 ∨ p5)) ∨ True)) ∨ (p3 → p2)) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_651294913162159946727756564037 : (((((p5 ∨ (p4 → p5)) ∧ (p3 ∨ ((p2 ∨ True) ∨ (((p5 → p1) ∧ p1) ∨ ((((False → p3) ∧ p5) → p1) ∧ p1))))) ∧ (p5 ∧ p2)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_443643379041109875164093160492 : (((((p2 → (((p5 ∨ p5) ∧ p3) → p5)) → (p1 ∨ ((((p5 ∧ p2) ∧ ((p2 ∧ True) ∧ p2)) ∨ p2) ∨ p4))) ∨ ((True ∨ p3) → True)) ∧ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_679035405290684859512727230634 : ((((False ∨ (((p4 ∧ ((p5 ∨ (((p4 → p2) → p5) → True)) → (p2 ∨ (True ∧ p2)))) ∨ p3) → p5)) ∨ (((p1 → p2) ∧ p1) ∨ True)) ∨ p4) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_342288236258877112138319867598 : (p2 → (((((p5 ∧ True) ∧ True) ∨ (p4 ∧ p3)) ∨ (((p3 ∧ (False → True)) ∧ (True → False)) ∨ False)) ∨ ((True ∨ (p1 ∧ (p2 ∨ p5))) ∨ p3))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_54494077162923480129188605023 : (((((p3 ∧ p1) ∧ p3) ∧ ((p1 ∨ False) ∨ False)) ∨ ((((False → ((p5 ∧ ((True ∧ p5) ∧ False)) ∧ p3)) ∨ (p5 → p5)) → p5) ∨ p5)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_596885197537701173991964135901 : ((((((p5 ∧ p5) ∨ (p5 ∧ (p3 ∧ True))) ∨ ((p4 → ((p4 ∧ (p1 ∧ ((p3 ∧ (p2 ∨ False)) → (False → p2)))) → p3)) ∨ p2)) ∧ p2) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_54951764430222602933542745088 : (((((p3 ∧ True) ∧ p2) ∨ (False ∧ p4)) ∧ ((((False ∨ (p5 ∧ (True → p5))) → (p1 → False)) ∨ p3) ∧ (p4 ∨ (p5 ∨ (True ∧ p4))))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_247521195622342898592060070478 : ((False ∨ p3) ∨ (p5 → (((((True → p3) ∨ (p1 ∧ p2)) ∨ (p4 ∨ (p5 ∧ p3))) ∨ p2) → ((p1 ∨ (((p5 ∧ p4) ∧ p4) → True)) ∨ p5)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Disjunctions on the left can always be decomposed.
  cases h2
  case inl h3 =>
    -- Disjunctions on the left can always be decomposed.
    cases h3
    case inl h4 =>
      -- Disjunctions on the left can always be decomposed.
      cases h4
      case inl h5 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- One of the premise coincides with the conclusion.
        exact h1
      case inr h6 =>
        -- Conjunctions on the left can always be decomposed.
        let h7 := h6.left
        let h8 := h6.right
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- One of the premise coincides with the conclusion.
        exact h1
    case inr h9 =>
      -- Disjunctions on the left can always be decomposed.
      cases h9
      case inl h10 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- One of the premise coincides with the conclusion.
        exact h1
      case inr h11 =>
        -- Conjunctions on the left can always be decomposed.
        let h12 := h11.left
        let h13 := h11.right
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- One of the premise coincides with the conclusion.
        exact h1
  case inr h14 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_207781237119001782438159570600 : (((p5 ∨ ((p2 ∧ False) ∨ True)) → p1) → (p5 → ((True → ((p1 ∧ p2) ∨ ((p4 ∨ (((False ∧ p2) → p4) → p3)) ∨ (p5 ∨ p2)))) ∨ False))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h3
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- One of the premise coincides with the conclusion.
  exact h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_588955944586975803140081661673 : (((((p5 ∨ (p1 ∧ (((((p2 ∧ (p3 → ((p2 ∧ p5) → (False → p4)))) ∨ p4) ∨ p5) → p2) → ((False ∧ p3) ∧ False)))) ∨ p2) ∧ p5) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_78923950529621811345001534763 : ((((False → p2) → ((((p1 → True) ∧ p1) ∧ ((p4 → (p5 → p3)) ∨ p2)) ∧ (p1 ∨ (False ∧ (p5 → (False ∨ p3)))))) ∧ (p3 ∨ True)) → p1) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- Disjunctions on the left can always be decomposed.
  cases h3
  case inl h4 =>
    -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
    have h5 : (False → p2) := by
      -- Implications on the right can always be decomposed.
      intro h6
      -- False on the left can always be used.
      apply False.elim h6
    -- We have shown the premise of h2, we can now drive its conclusion.
    let h7 := h2 h5
    -- We need to get the left conjuct of h7 based on <expert-advice>.
    let h8 := h7.left
    -- We need to get the left conjuct of h8 based on <expert-advice>.
    let h9 := h8.left
    -- We need to get the right conjuct of h9 based on <expert-advice>.
    let h10 := h9.right
    -- One of the premise coincides with the conclusion.
    exact h10
  case inr h11 =>
    -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
    have h12 : (False → p2) := by
      -- Implications on the right can always be decomposed.
      intro h13
      -- False on the left can always be used.
      apply False.elim h13
    -- We have shown the premise of h2, we can now drive its conclusion.
    let h14 := h2 h12
    -- We need to get the left conjuct of h14 based on <expert-advice>.
    let h15 := h14.left
    -- We need to get the left conjuct of h15 based on <expert-advice>.
    let h16 := h15.left
    -- We need to get the right conjuct of h16 based on <expert-advice>.
    let h17 := h16.right
    -- One of the premise coincides with the conclusion.
    exact h17



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_47822581061614698414219947643 : (((((p2 ∧ (p2 → (False ∧ (p3 ∨ p3)))) ∨ (True ∨ ((((p3 → p1) → p3) ∧ ((True ∨ True) → True)) → p5))) → p1) → (p3 ∨ p1)) ∨ False) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h2 : ((p2 ∧ (p2 → (False ∧ (p3 ∨ p3)))) ∨ (True ∨ ((((p3 → p1) → p3) ∧ ((True ∨ True) → True)) → p5))) := by
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h3 := h1 h2
  -- One of the premise coincides with the conclusion.
  exact h3



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_145356050220660432483429978834 : (((p2 → (p4 → ((p3 ∧ p1) → p5))) → (((True ∧ p3) → p1) ∨ (((p3 → p4) ∧ False) → (p4 → p1)))) ∧ ((p1 ∨ p1) → (True ∨ p3))) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
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
  -- False on the left can always be used.
  apply False.elim h5
  -- Implications on the right can always be decomposed.
  intro h6
  -- Disjunctions on the left can always be decomposed.
  cases h6
  case inl h7 =>
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- True on the right can always be proven directly.
    apply True.intro
  case inr h8 =>
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- True on the right can always be proven directly.
    apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_616752969456694961024904064813 : ((((((p1 ∧ (p3 ∨ p5)) ∧ (p3 ∨ ((True ∧ False) → False))) ∨ (p2 ∨ (((p4 ∧ p5) → ((p3 ∨ p5) ∧ p3)) → (False → True)))) ∨ p4) ∨ False) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_312314940011888083289997562329 : (p2 ∨ (p2 → (((p4 → (p1 ∨ (p3 ∧ (p4 ∨ p4)))) → p5) → (((p1 → p4) ∨ (p1 ∧ (p2 → ((p3 → p1) ∨ (True ∨ False))))) ∨ p2)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_115152514608683494441721745007 : (((p5 ∨ ((((p3 → True) ∧ True) → p1) ∨ (p4 → (True ∨ True)))) → (((p5 ∨ p4) ∨ ((True → p1) ∨ (p1 ∨ p5))) ∧ p2)) ∨ (p1 → p1)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_681139136766234109533745972503 : ((((p1 ∧ ((((True ∧ False) → p2) → ((p5 ∨ (((p5 ∧ p5) ∨ True) ∧ (p4 → p4))) → False)) → p3)) → (((p3 ∨ True) ∨ p1) ∧ True)) ∨ False) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h2
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_204430338512853648495481993686 : (((((p4 ∧ True) ∧ True) ∧ p1) ∨ p3) ∨ (((p4 → (((False ∨ (p2 ∧ ((p2 ∧ False) ∧ p5))) ∨ p3) ∨ (p5 ∨ False))) ∨ (p1 ∧ True)) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_178777359421731509331428206288 : (((p1 ∨ (True ∧ False)) ∧ (p3 ∨ (((False → p1) ∧ p4) ∨ (False ∨ p5)))) ∨ (p3 ∨ ((((p5 ∧ p4) ∨ p1) ∨ (True ∧ p5)) → (p1 → p1)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h3 =>
    -- Disjunctions on the left can always be decomposed.
    cases h3
    case inl h4 =>
      -- Conjunctions on the left can always be decomposed.
      let h5 := h4.left
      let h6 := h4.right
      -- One of the premise coincides with the conclusion.
      exact h2
    case inr h7 =>
      -- One of the premise coincides with the conclusion.
      exact h7
  case inr h8 =>
    -- Conjunctions on the left can always be decomposed.
    let h9 := h8.left
    let h10 := h8.right
    -- One of the premise coincides with the conclusion.
    exact h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_52971860651107063606285196194 : (((((True → ((p3 → p2) ∧ p5)) → (False ∨ (False → False))) → p4) ∧ (((True ∧ p3) → True) → (((False ∧ False) ∨ p4) → (p1 ∨ p2)))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_115888941214675861360593472329 : ((((p1 ∧ (False ∧ p4)) ∨ p2) ∨ ((p4 → (((p5 ∧ p1) → (True ∧ p1)) ∧ (p3 → ((p1 ∨ p2) → p2)))) ∨ (True ∧ True))) ∨ (p2 → True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_115204819468706596215459753628 : (((p1 ∧ (((p3 → p1) ∨ True) ∨ (False ∨ (p3 → p5)))) ∧ ((False ∧ p3) ∨ ((((p1 ∧ (False ∨ p5)) ∨ False) ∨ p2) ∧ True))) ∨ (False → p5)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_345512862120360788481408656980 : (p3 → ((((p2 ∨ ((p3 ∨ (p5 ∨ (((p4 → p4) ∧ True) → False))) → p3)) → False) → ((p2 ∨ p2) ∧ (False ∧ ((p5 ∧ p5) ∨ True)))) ∨ p5)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h2
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
  have h3 : (p2 ∨ ((p3 ∨ (p5 ∨ (((p4 → p4) ∧ True) → False))) → p3)) := by
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h4
    -- Disjunctions on the left can always be decomposed.
    cases h4
    case inl h5 =>
      -- One of the premise coincides with the conclusion.
      exact h5
    case inr h6 =>
      -- Disjunctions on the left can always be decomposed.
      cases h6
      case inl h7 =>
        -- One of the premise coincides with the conclusion.
        exact h1
      case inr h8 =>
        -- One of the premise coincides with the conclusion.
        exact h1
  -- We have shown the premise of h2, we can now drive its conclusion.
  let h9 := h2 h3
  -- False on the left can always be used.
  apply False.elim h9
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
  have h10 : (p2 ∨ ((p3 ∨ (p5 ∨ (((p4 → p4) ∧ True) → False))) → p3)) := by
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h11
    -- Disjunctions on the left can always be decomposed.
    cases h11
    case inl h12 =>
      -- One of the premise coincides with the conclusion.
      exact h12
    case inr h13 =>
      -- Disjunctions on the left can always be decomposed.
      cases h13
      case inl h14 =>
        -- One of the premise coincides with the conclusion.
        exact h1
      case inr h15 =>
        -- One of the premise coincides with the conclusion.
        exact h1
  -- We have shown the premise of h2, we can now drive its conclusion.
  let h16 := h2 h10
  -- False on the left can always be used.
  apply False.elim h16
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_140290492276459229742863359971 : ((((True ∨ (p4 ∧ (p3 ∨ (True → p2)))) → (((p4 ∨ p5) ∧ False) ∧ (p4 ∨ (p5 → p2)))) ∧ (p3 ∨ (True → p3))) → ((False ∨ p5) ∧ p2)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- Disjunctions on the left can always be decomposed.
  cases h3
  case inl h4 =>
    -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
    have h5 : (True ∨ (p4 ∧ (p3 ∨ (True → p2)))) := by
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- True on the right can always be proven directly.
      apply True.intro
    -- We have shown the premise of h2, we can now drive its conclusion.
    let h6 := h2 h5
    -- We need to get the left conjuct of h6 based on <expert-advice>.
    let h7 := h6.left
    -- We need to get the right conjuct of h7 based on <expert-advice>.
    let h8 := h7.right
    -- False on the left can always be used.
    apply False.elim h8
  case inr h9 =>
    -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
    have h10 : (True ∨ (p4 ∧ (p3 ∨ (True → p2)))) := by
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- True on the right can always be proven directly.
      apply True.intro
    -- We have shown the premise of h2, we can now drive its conclusion.
    let h11 := h2 h10
    -- We need to get the left conjuct of h11 based on <expert-advice>.
    let h12 := h11.left
    -- We need to get the right conjuct of h12 based on <expert-advice>.
    let h13 := h12.right
    -- False on the left can always be used.
    apply False.elim h13
  -- Conjunctions on the left can always be decomposed.
  let h14 := h1.left
  let h15 := h1.right
  -- Disjunctions on the left can always be decomposed.
  cases h15
  case inl h16 =>
    -- We want to use the implication h14 based on <expert-advice>. So we show its premise.
    have h17 : (True ∨ (p4 ∧ (p3 ∨ (True → p2)))) := by
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- True on the right can always be proven directly.
      apply True.intro
    -- We have shown the premise of h14, we can now drive its conclusion.
    let h18 := h14 h17
    -- We need to get the left conjuct of h18 based on <expert-advice>.
    let h19 := h18.left
    -- We need to get the right conjuct of h19 based on <expert-advice>.
    let h20 := h19.right
    -- False on the left can always be used.
    apply False.elim h20
  case inr h21 =>
    -- We want to use the implication h14 based on <expert-advice>. So we show its premise.
    have h22 : (True ∨ (p4 ∧ (p3 ∨ (True → p2)))) := by
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- True on the right can always be proven directly.
      apply True.intro
    -- We have shown the premise of h14, we can now drive its conclusion.
    let h23 := h14 h22
    -- We need to get the left conjuct of h23 based on <expert-advice>.
    let h24 := h23.left
    -- We need to get the right conjuct of h24 based on <expert-advice>.
    let h25 := h24.right
    -- False on the left can always be used.
    apply False.elim h25



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_173196117080143827338048763693 : ((p5 ∨ ((((p2 ∧ False) ∧ True) ∧ ((False ∧ (p4 ∨ True)) ∧ (p2 ∨ p4))) ∧ True)) ∨ (True ∨ (p1 → ((((True ∧ p1) ∨ p3) ∧ p5) ∧ p1)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_115660279785997061890552312540 : (((((p2 ∧ p1) → p3) → (p4 ∧ p1)) ∨ ((p3 ∨ ((p2 ∨ (((False ∧ p2) ∨ (p2 ∧ p2)) ∨ (False → True))) → p2)) ∧ p3)) ∨ (p4 → p4)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_305578444520680800309242639681 : (p1 ∨ (((p1 ∨ (p4 ∨ ((p2 ∨ (False ∨ (p4 → p4))) ∧ p2))) ∧ p1) ∨ (True ∨ (((((p1 → (p2 ∧ True)) → p4) ∧ p4) ∨ p5) → p2)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_301821633113759683992973390677 : (False ∨ ((p1 ∨ p3) ∨ ((((((p4 → p5) ∧ (p1 ∧ ((p1 ∧ True) ∧ (p4 ∨ True)))) → p4) ∧ (p1 ∧ p5)) ∧ (p4 ∨ True)) ∨ (p2 → p2)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_148743096137241242752731806725 : (((((p3 ∧ p4) ∨ p1) ∨ (p3 ∨ p1)) ∧ ((p2 ∨ p3) → (p2 → ((p3 → True) → (p5 → (p5 → p5)))))) ∨ (True ∨ ((p1 ∧ False) ∨ p2))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_752697578052152981120918485601 : (((False ∧ (((p5 → (((False ∧ p5) → p3) ∧ (p1 ∨ ((p5 → True) ∨ (p5 ∨ False))))) ∧ (((True → (p4 ∧ p1)) → p2) ∨ p5)) ∨ p5)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_606616782864959572391376820059 : ((((((p4 ∧ ((((p3 ∧ (((p3 ∧ p3) → ((True ∨ False) → p4)) ∧ (p5 ∨ p3))) ∧ (p1 ∧ p3)) → True) ∨ p5)) → False) ∧ False) ∨ p2) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_174035295407490657751875567583 : (((p3 ∨ ((((p3 ∨ (False ∨ (p5 ∨ p3))) ∨ (p1 → p5)) ∨ p3) → p3)) → p4) → (((p1 → p3) ∨ True) → (p3 ∨ ((p2 ∧ p2) ∨ True)))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Disjunctions on the left can always be decomposed.
  cases h2
  case inl h3 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro
  case inr h4 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_780028758602433412699070227861 : (((p2 ∨ ((((False ∨ (p3 ∨ True)) → False) ∨ (((p5 ∧ p4) ∨ p2) ∨ (((True ∧ True) → False) → ((p3 ∨ p5) ∧ p2)))) ∨ (p5 → p2))) ∨ False) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h2 : (True ∧ True) := by
    -- Conjunctions on the right can always be decomposed.
    apply And.intro
    -- True on the right can always be proven directly.
    apply True.intro
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h3 := h1 h2
  -- False on the left can always be used.
  apply False.elim h3
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h4 : (True ∧ True) := by
    -- Conjunctions on the right can always be decomposed.
    apply And.intro
    -- True on the right can always be proven directly.
    apply True.intro
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h5 := h1 h4
  -- False on the left can always be used.
  apply False.elim h5
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_654729793489472154322957001984 : ((((((True ∧ (p2 ∧ ((((p4 ∧ (((p1 → p1) ∨ ((p3 ∧ p2) ∨ p4)) ∨ p5)) ∧ p5) → p4) → p4))) ∨ p5) → False) ∨ (p4 ∧ p1)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_315130343790660741774146341512 : (p3 ∨ ((False ∧ ((p4 ∨ p1) → (p1 ∧ False))) ∨ (((((p1 → False) ∧ (False ∨ p3)) ∨ p2) ∨ (p4 → p4)) → (p2 → ((False → p2) ∨ p4))))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h3 =>
    -- Disjunctions on the left can always be decomposed.
    cases h3
    case inl h4 =>
      -- Conjunctions on the left can always be decomposed.
      let h5 := h4.left
      let h6 := h4.right
      -- Disjunctions on the left can always be decomposed.
      cases h6
      case inl h7 =>
        -- False on the left can always be used.
        apply False.elim h7
      case inr h8 =>
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- Implications on the right can always be decomposed.
        intro h9
        -- False on the left can always be used.
        apply False.elim h9
    case inr h10 =>
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- Implications on the right can always be decomposed.
      intro h11
      -- False on the left can always be used.
      apply False.elim h11
  case inr h12 =>
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Implications on the right can always be decomposed.
    intro h13
    -- False on the left can always be used.
    apply False.elim h13



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_196671687917182308308205087582 : ((((p5 ∨ (p3 ∧ (p1 → False))) ∧ p3) ∧ p2) ∨ (p4 → (((p1 ∨ ((p3 ∧ (False ∨ ((False → p4) ∨ (True ∧ p2)))) ∨ p3)) → p4) → p4))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_233498783621017959899427595407 : ((p1 ∨ (p3 ∧ p3)) → ((p1 → (p3 ∧ (False ∧ ((p1 → False) → ((True → ((p4 ∨ ((False → p3) ∧ p3)) ∧ False)) ∧ True))))) ∨ (p2 → True))) := by
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
    -- Conjunctions on the left can always be decomposed.
    let h5 := h4.left
    let h6 := h4.right
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h7
    -- True on the right can always be proven directly.
    apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_205365623288044589581997377531 : ((((p5 → p2) ∧ p2) → (p1 → p5)) ∨ ((p5 ∧ p1) ∨ (((p3 → (p1 ∨ (p2 ∨ (True ∧ (p3 ∨ (p1 ∧ False)))))) ∨ (p4 ∧ p1)) ∨ p1))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_885889839703014499510412939 : ((p1 → (((True → p2) ∨ ((((True ∧ True) → p2) ∧ ((True ∧ True) → (p2 → (p3 → p5)))) ∨ p2)) → (p4 → (p3 ∨ p2)))) ∨ p4) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Implications on the right can always be decomposed.
  intro h3
  -- Disjunctions on the left can always be decomposed.
  cases h2
  case inl h4 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- We want to use the implication h4 based on <expert-advice>. So we show its premise.
    have h5 : True := by
      -- True on the right can always be proven directly.
      apply True.intro
    -- We have shown the premise of h4, we can now drive its conclusion.
    let h6 := h4 h5
    -- One of the premise coincides with the conclusion.
    exact h6
  case inr h7 =>
    -- Disjunctions on the left can always be decomposed.
    cases h7
    case inl h8 =>
      -- Conjunctions on the left can always be decomposed.
      let h9 := h8.left
      let h10 := h8.right
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- We want to use the implication h9 based on <expert-advice>. So we show its premise.
      have h11 : (True ∧ True) := by
        -- Conjunctions on the right can always be decomposed.
        apply And.intro
        -- True on the right can always be proven directly.
        apply True.intro
        -- True on the right can always be proven directly.
        apply True.intro
      -- We have shown the premise of h9, we can now drive its conclusion.
      let h12 := h9 h11
      -- One of the premise coincides with the conclusion.
      exact h12
    case inr h13 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- One of the premise coincides with the conclusion.
      exact h13



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_338453165860096531600483257634 : (p1 → (((p4 ∨ p4) ∨ True) ∧ ((True ∧ (((((False → (p3 ∧ p1)) → p4) ∨ p5) ∨ ((p4 → (True ∧ p4)) ∧ p5)) → p4)) ∨ (p4 ∨ True)))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_983097901926596072489638070200 : (((p1 ∧ (((p2 → (False ∧ ((False → (p4 ∧ p5)) ∧ p1))) ∧ (p1 ∧ (False → (True ∨ p3)))) ∧ ((((p3 → True) → True) ∧ p3) ∧ p2))) → p4) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- Conjunctions on the left can always be decomposed.
  let h4 := h3.left
  let h5 := h3.right
  -- Conjunctions on the left can always be decomposed.
  let h6 := h4.left
  let h7 := h4.right
  -- Conjunctions on the left can always be decomposed.
  let h8 := h7.left
  let h9 := h7.right
  -- Conjunctions on the left can always be decomposed.
  let h10 := h5.left
  let h11 := h5.right
  -- Conjunctions on the left can always be decomposed.
  let h12 := h10.left
  let h13 := h10.right
  -- We want to use the implication h6 based on <expert-advice>. So we show its premise.
  have h14 : p2 := by
    -- One of the premise coincides with the conclusion.
    exact h11
  -- We have shown the premise of h6, we can now drive its conclusion.
  let h15 := h6 h14
  -- We need to get the left conjuct of h15 based on <expert-advice>.
  let h16 := h15.left
  -- False on the left can always be used.
  apply False.elim h16
  -- True on the right can always be proven directly.
  apply True.intro



