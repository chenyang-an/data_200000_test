variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_197432427463692295157461611193 : (((((p4 ∧ False) ∨ p4) ∧ False) ∧ (True ∧ p3)) ∨ ((p1 ∧ (p5 ∧ (p1 ∨ False))) ∨ (True ∨ ((False ∨ p5) ∧ ((p3 ∧ (p2 → p4)) ∧ p4))))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_310019352225433091544822787415 : (p2 ∨ ((((p1 ∧ (((p3 → (p4 ∨ True)) → p2) → p1)) ∨ (p5 ∧ (True ∧ p3))) ∨ False) ∨ (p5 → (((p1 ∨ p5) ∧ False) ∨ (p2 ∨ True))))) := by
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



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_310057037224537976981819346048 : (p2 ∨ (((((p4 → (p3 → ((p5 ∨ (p1 → p4)) ∨ False))) ∨ p2) → p1) ∧ (p1 → False)) → (((p4 → p2) → (True ∨ p2)) ∧ (p2 ∨ p3)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h2
  -- Conjunctions on the left can always be decomposed.
  let h3 := h1.left
  let h4 := h1.right
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro
  -- Conjunctions on the left can always be decomposed.
  let h5 := h1.left
  let h6 := h1.right
  -- We want to use the implication h5 based on <expert-advice>. So we show its premise.
  have h7 : ((p4 → (p3 → ((p5 ∨ (p1 → p4)) ∨ False))) ∨ p2) := by
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Implications on the right can always be decomposed.
    intro h8
    -- Implications on the right can always be decomposed.
    intro h9
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h10
    -- One of the premise coincides with the conclusion.
    exact h8
  -- We have shown the premise of h5, we can now drive its conclusion.
  let h11 := h5 h7
  -- We want to use the implication h6 based on <expert-advice>. So we show its premise.
  have h12 : p1 := by
    -- One of the premise coincides with the conclusion.
    exact h11
  -- We have shown the premise of h6, we can now drive its conclusion.
  let h13 := h6 h12
  -- False on the left can always be used.
  apply False.elim h13



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_90872043539161654571424180965 : (((p4 ∨ p5) ∧ (p4 ∧ (((p3 ∧ (False ∨ ((p1 ∧ ((p3 ∨ True) → (p1 ∨ False))) ∨ (p2 → (p5 ∨ (p1 → False)))))) ∨ True) → False))) → False) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- Disjunctions on the left can always be decomposed.
  cases h2
  case inl h4 =>
    -- Conjunctions on the left can always be decomposed.
    let h5 := h3.left
    let h6 := h3.right
    -- We want to use the implication h6 based on <expert-advice>. So we show its premise.
    have h7 : ((p3 ∧ (False ∨ ((p1 ∧ ((p3 ∨ True) → (p1 ∨ False))) ∨ (p2 → (p5 ∨ (p1 → False)))))) ∨ True) := by
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- True on the right can always be proven directly.
      apply True.intro
    -- We have shown the premise of h6, we can now drive its conclusion.
    let h8 := h6 h7
    -- False on the left can always be used.
    apply False.elim h8
  case inr h9 =>
    -- Conjunctions on the left can always be decomposed.
    let h10 := h3.left
    let h11 := h3.right
    -- We want to use the implication h11 based on <expert-advice>. So we show its premise.
    have h12 : ((p3 ∧ (False ∨ ((p1 ∧ ((p3 ∨ True) → (p1 ∨ False))) ∨ (p2 → (p5 ∨ (p1 → False)))))) ∨ True) := by
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- True on the right can always be proven directly.
      apply True.intro
    -- We have shown the premise of h11, we can now drive its conclusion.
    let h13 := h11 h12
    -- False on the left can always be used.
    apply False.elim h13



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_207756996626911117500681989709 : (((p1 ∨ ((p1 → p4) ∨ p5)) → p3) → ((p2 → (p5 ∨ p3)) ∨ ((True ∧ True) ∨ ((p3 ∧ (p5 → True)) ∧ (p3 → ((p1 → p3) ∧ True)))))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_40499576436623699362864918900 : ((((False ∧ ((p5 ∨ ((((((p3 ∧ p1) ∨ ((p2 ∧ p3) ∨ True)) ∧ (p3 → True)) ∨ False) ∧ False) ∨ (True → True))) ∧ p5)) ∨ p2) ∨ True) ∨ p3) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_245790404803041062245607846572 : ((p3 ∧ p3) ∨ (((((p3 ∧ (p4 → (p5 ∧ p1))) ∧ p4) → (p1 ∨ p5)) ∧ p2) → (((((p5 ∧ p2) ∧ True) ∧ (False ∧ p2)) ∧ p4) ∨ p2))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h3



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_809353418836681580896862306612 : (((p5 → ((p3 ∨ ((True ∧ ((p1 → (p2 ∧ (p1 → (True → ((p4 ∧ False) ∧ False))))) ∨ ((p5 ∧ (p1 ∧ p3)) ∧ False))) ∨ p3)) ∨ True)) ∨ p1) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_112805282224940289644417018707 : ((((True ∨ (p1 → ((p5 ∨ p4) → p5))) ∨ (True → (p1 ∨ (p3 ∨ ((((p1 ∨ False) ∧ p4) → False) → (p5 ∨ p2)))))) → p4) ∨ (True ∨ p4)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_309337515974125748360177987833 : (p2 ∨ (((p3 ∨ ((p5 → (((p2 ∨ p3) ∨ p2) → False)) ∧ ((p1 → (p4 ∧ (p4 ∧ True))) ∧ (p1 → p1)))) → (p5 ∨ p1)) ∨ (False → p2))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_714075447735116200987376499348 : ((((((p2 ∨ p5) ∧ (p5 ∧ p4)) → False) → (p1 ∧ (((p4 ∧ (p1 → (False → p2))) ∨ ((p4 → p3) → p5)) ∨ ((p2 ∧ True) ∨ p1)))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_54023819743965534479650095665 : (((((True ∧ (p2 → True)) ∨ (True → p1)) ∧ (p1 ∨ p1)) → ((((p5 → ((False ∨ p4) ∧ ((p2 ∧ False) ∧ p4))) ∨ p3) ∨ False) → p4)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_185539915229390074771041877570 : ((p3 ∨ (False ∨ (((False ∨ True) ∧ True) → ((p4 ∨ p4) ∨ False)))) ∨ (((p4 ∧ (False ∨ (True ∧ (p1 ∨ (False → (p2 → p1)))))) ∨ True) ∨ p1)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_51053803966033497685763386533 : (((p4 ∨ ((p1 → ((p5 → (p5 ∨ p3)) ∧ p4)) ∨ (((p1 ∨ False) ∧ True) → (True → p4)))) ∧ (p2 ∨ ((p3 ∧ (True ∧ p3)) → False))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_52241080492200826275757076474 : (((p4 ∧ (p1 ∨ (((p5 ∧ ((p2 ∧ (p4 → False)) ∧ p2)) ∨ True) ∨ (False → False)))) → ((p2 ∧ ((p4 ∧ (False ∨ p1)) → True)) ∨ p5)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_46126812012886414550540060079 : ((((p5 → ((((((p2 → True) ∧ (False ∨ p4)) → True) → True) ∧ ((p1 ∧ (p1 ∧ False)) → p1)) → (True → False))) ∨ p4) ∧ (True ∨ False)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_358242472381466132702982657617 : (p5 → (p4 ∨ ((False ∨ ((p1 ∧ (p3 ∨ True)) → p1)) ∧ (p2 ∨ (((p3 → (p2 ∧ (p1 → False))) ∧ ((p2 ∧ p3) → (p2 ∨ p5))) ∨ True))))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h2
  -- Conjunctions on the left can always be decomposed.
  let h3 := h2.left
  let h4 := h2.right
  -- Disjunctions on the left can always be decomposed.
  cases h4
  case inl h5 =>
    -- One of the premise coincides with the conclusion.
    exact h3
  case inr h6 =>
    -- One of the premise coincides with the conclusion.
    exact h3
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_151916909036182832447085437530 : (((((((p4 ∧ False) ∨ (p3 → p4)) → p1) ∨ (True ∧ p1)) ∧ p5) ∧ ((p1 ∧ p1) → ((p4 → True) ∧ p1))) → ((p3 → p4) ∨ (p3 → True))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- Conjunctions on the left can always be decomposed.
  let h4 := h2.left
  let h5 := h2.right
  -- Disjunctions on the left can always be decomposed.
  cases h4
  case inl h6 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h7
    -- True on the right can always be proven directly.
    apply True.intro
  case inr h8 =>
    -- Conjunctions on the left can always be decomposed.
    let h9 := h8.left
    let h10 := h8.right
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h11
    -- True on the right can always be proven directly.
    apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_47882978378565857228087636005 : (((((((p5 → p1) ∧ True) → (p1 → (((p3 → (p5 ∨ p4)) → ((False → p1) ∨ p3)) ∨ True))) ∨ True) ∨ (p2 ∧ p3)) → (True ∧ p5)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_823296061288333593938439099967 : (((((True → (p5 ∧ ((True ∧ False) ∧ p4))) ∧ (True ∨ ((((p4 ∧ ((p3 ∨ (p1 ∧ p4)) ∧ p4)) ∧ (True ∨ p1)) → p1) → p3))) ∧ p3) → p4) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
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
    -- We want to use the implication h4 based on <expert-advice>. So we show its premise.
    have h7 : True := by
      -- True on the right can always be proven directly.
      apply True.intro
    -- We have shown the premise of h4, we can now drive its conclusion.
    let h8 := h4 h7
    -- We need to get the right conjuct of h8 based on <expert-advice>.
    let h9 := h8.right
    -- We need to get the right conjuct of h9 based on <expert-advice>.
    let h10 := h9.right
    -- One of the premise coincides with the conclusion.
    exact h10
  case inr h11 =>
    -- We want to use the implication h4 based on <expert-advice>. So we show its premise.
    have h12 : True := by
      -- True on the right can always be proven directly.
      apply True.intro
    -- We have shown the premise of h4, we can now drive its conclusion.
    let h13 := h4 h12
    -- We need to get the right conjuct of h13 based on <expert-advice>.
    let h14 := h13.right
    -- We need to get the right conjuct of h14 based on <expert-advice>.
    let h15 := h14.right
    -- One of the premise coincides with the conclusion.
    exact h15
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_382181022584560781684568575200 : (((((((p3 ∨ (False ∧ (p5 ∨ ((p4 → (p4 ∧ True)) ∨ True)))) → ((((p1 ∨ False) ∨ p5) ∧ p4) → True)) → (p4 → p3)) ∨ True) ∨ False) ∧ True) ∧ True) := by
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
theorem thm_5_vars_354720215234290226734098394636 : (p5 → (((False ∨ (((((p3 ∧ (p2 ∨ (p1 ∨ False))) → (p4 ∧ (p4 → p1))) ∨ p5) → p3) ∨ (p5 ∧ p5))) ∨ (p4 → (False ∨ True))) ∨ p3)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- One of the premise coincides with the conclusion.
  exact h1
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_212231587012392127225346413435 : ((False ∨ ((p1 ∧ p5) → p5)) ∧ ((((p1 ∧ False) ∧ p3) ∧ (False ∨ ((p2 ∧ p5) → p1))) ∨ (((p4 ∨ True) ∧ ((False → p4) ∨ p5)) ∨ False))) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- One of the premise coincides with the conclusion.
  exact h3
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h4
  -- False on the left can always be used.
  apply False.elim h4



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_46270692252015387344131942180 : (((((((p3 ∨ p4) ∧ (p4 → True)) ∨ (p2 ∨ ((True ∨ (True ∧ p2)) ∧ (False ∨ p5)))) ∧ p3) ∧ (p1 ∧ (p2 → False))) ∧ (False ∧ p1)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_802943138064011454117383712615 : (((p3 → ((((p2 → ((p2 ∧ (p1 ∧ (((p5 ∨ p3) → (p5 ∨ True)) ∨ ((False ∧ (p3 → p4)) → False)))) ∨ p5)) ∨ p4) → False) ∧ p1)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_85911143500841191444135208618 : ((((p2 ∧ (((False → p3) → True) ∨ (p3 → p5))) ∧ p3) ∧ (((p2 ∨ ((p3 → (p1 ∨ ((p3 → p3) → p5))) → False)) → p3) → p2)) → p3) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- Conjunctions on the left can always be decomposed.
  let h4 := h2.left
  let h5 := h2.right
  -- Conjunctions on the left can always be decomposed.
  let h6 := h4.left
  let h7 := h4.right
  -- Disjunctions on the left can always be decomposed.
  cases h7
  case inl h8 =>
    -- One of the premise coincides with the conclusion.
    exact h5
  case inr h9 =>
    -- One of the premise coincides with the conclusion.
    exact h5



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_214295702019334480480929917110 : (((p5 ∧ (False ∨ p5)) → p3) ∨ ((p1 ∧ p1) ∨ ((p1 ∨ p5) ∨ (((False ∨ (p2 → p3)) ∨ p1) ∨ ((p3 ∨ (False → (p1 → True))) ∨ p4))))) := by
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
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_649854922915276953497728975758 : ((((((((p4 ∨ (((p1 ∨ p1) ∧ p5) ∨ (p3 ∨ (p4 → p2)))) → (p2 ∧ True)) ∨ p4) ∧ p3) ∧ ((p2 ∨ p2) ∧ True)) ∧ (False ∧ p3)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_193576366465102294774683154544 : (((p4 ∨ True) → ((p2 ∧ False) ∧ (False ∧ (p4 ∧ p4)))) → ((p1 ∨ (p1 → (p2 → (p3 ∧ (((p2 → p2) → p4) ∨ (True ∨ p5)))))) ∧ True)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h2 : (p4 ∨ True) := by
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h3 := h1 h2
  -- We need to get the left conjuct of h3 based on <expert-advice>.
  let h4 := h3.left
  -- We need to get the right conjuct of h4 based on <expert-advice>.
  let h5 := h4.right
  -- False on the left can always be used.
  apply False.elim h5
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_231140901217986383776196655940 : (((p1 ∨ p4) ∨ p1) → (((((False → p1) ∨ ((p3 ∧ True) ∨ (((p2 → p5) → (p2 ∨ p3)) ∨ (p2 ∧ p2)))) ∧ (False ∨ False)) ∧ p2) ∨ True)) := by
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
      -- True on the right can always be proven directly.
      apply True.intro
    case inr h4 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- True on the right can always be proven directly.
      apply True.intro
  case inr h5 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_148207726696355316578479419847 : (((p1 ∨ ((p2 ∧ (p4 ∨ (True → p3))) ∨ ((p2 ∧ p4) ∨ (True ∧ (p3 ∨ False))))) ∧ (p1 ∨ (p4 → p2))) ∨ (p3 → ((True → p5) → p3))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_165504123088870921563231796884 : (((p4 → (p5 ∨ (((p3 → p3) ∨ p5) ∧ (p2 ∧ p4)))) ∨ (p1 ∨ (True → (False ∨ True)))) ∨ ((False → p1) → ((p2 ∧ (p3 ∧ p3)) ∧ p5))) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_264428069432827596610049997554 : (True ∧ ((((p1 → p1) ∨ p3) ∨ p5) → (((p2 ∧ (p1 → (p3 ∨ p5))) → (((p4 ∧ (p2 ∧ p5)) → (False ∨ (False ∨ p2))) ∨ p1)) ∨ p5))) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- Implications on the right can always be decomposed.
  intro h1
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h2 =>
    -- Disjunctions on the left can always be decomposed.
    cases h2
    case inl h3 =>
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- Implications on the right can always be decomposed.
      intro h4
      -- Conjunctions on the left can always be decomposed.
      let h5 := h4.left
      let h6 := h4.right
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- Implications on the right can always be decomposed.
      intro h7
      -- Conjunctions on the left can always be decomposed.
      let h8 := h7.left
      let h9 := h7.right
      -- Conjunctions on the left can always be decomposed.
      let h10 := h9.left
      let h11 := h9.right
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- One of the premise coincides with the conclusion.
      exact h10
    case inr h12 =>
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- Implications on the right can always be decomposed.
      intro h13
      -- Conjunctions on the left can always be decomposed.
      let h14 := h13.left
      let h15 := h13.right
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- Implications on the right can always be decomposed.
      intro h16
      -- Conjunctions on the left can always be decomposed.
      let h17 := h16.left
      let h18 := h16.right
      -- Conjunctions on the left can always be decomposed.
      let h19 := h18.left
      let h20 := h18.right
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- One of the premise coincides with the conclusion.
      exact h19
  case inr h21 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h21



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_330784983922748268097470185791 : (True → (p2 → ((p3 ∨ (True → (p3 → ((((p1 → True) ∧ p5) → ((p4 ∧ p2) ∧ ((p5 ∧ (p5 ∧ False)) ∨ False))) ∨ (False ∨ p3))))) ∨ p2))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_590095801709995255894000579777 : ((((((p5 ∧ (((True ∨ ((p4 ∨ False) ∧ p5)) → p1) ∧ p2)) ∧ (((p3 → (False ∨ p1)) ∧ (p4 ∨ p1)) ∨ (p1 ∨ p5))) → False) ∧ p4) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_53564400314247214252483653940 : ((((((p1 ∧ (False ∧ p1)) ∧ False) ∨ (p3 ∧ p3)) ∨ p2) ∧ ((True ∧ (False ∧ p5)) ∨ ((p5 ∨ ((False ∨ p5) ∨ (p5 ∧ p2))) ∨ True))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_712720234593476004250008176432 : (((((True ∧ p5) ∨ (p3 → (p1 → False))) ∨ (p3 → (((((True → (p5 ∨ p5)) → p3) ∨ (((False → True) → p4) → p1)) → False) ∨ p4))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_114767849001162287802770603558 : (((p3 → (p5 → (False ∧ (p4 ∨ (p1 ∨ (True ∨ (False → ((p2 ∨ p4) ∧ p1)))))))) → (((True → (p4 ∧ True)) ∧ p1) ∨ p5)) ∨ (True ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_809310081971491981772259477760 : (((p5 → (((True → False) → (p3 ∨ ((p4 ∧ p1) ∧ (p4 ∧ (p2 ∧ (True → (p4 → ((p5 → ((p1 → p4) ∨ p4)) ∧ p4)))))))) ∨ p2)) ∨ p1) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h2
  -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
  have h3 : True := by
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h2, we can now drive its conclusion.
  let h4 := h2 h3
  -- False on the left can always be used.
  apply False.elim h4
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_246266088483600843566024418180 : ((p4 ∧ p4) ∨ ((p2 ∨ ((p1 → False) ∨ ((True ∧ ((False ∧ (True ∨ ((False ∧ p5) → p5))) ∧ ((p2 ∧ True) ∧ p5))) ∨ p4))) ∨ (True ∨ p3))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_713222840567944640651092971421 : ((((p2 ∨ (p2 ∧ (p3 ∧ (True → p5)))) ∨ ((True → p5) ∨ (((p2 ∨ (True ∨ (False ∨ True))) ∨ p3) → (False ∨ (False → (p3 ∨ p3)))))) ∨ p2) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
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
      -- False on the left can always be used.
      apply False.elim h4
    case inr h5 =>
      -- Disjunctions on the left can always be decomposed.
      cases h5
      case inl h6 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- Implications on the right can always be decomposed.
        intro h7
        -- False on the left can always be used.
        apply False.elim h7
      case inr h8 =>
        -- Disjunctions on the left can always be decomposed.
        cases h8
        case inl h9 =>
          -- False on the left can always be used.
          apply False.elim h9
        case inr h10 =>
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- Implications on the right can always be decomposed.
          intro h11
          -- False on the left can always be used.
          apply False.elim h11
  case inr h12 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h13
    -- False on the left can always be used.
    apply False.elim h13
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_337053721291618425524993702696 : (p1 → (((p5 ∧ (p1 ∧ (((((p4 ∧ p4) ∨ p3) ∧ ((True ∧ True) ∧ p2)) ∧ (p1 ∧ ((p4 → False) ∨ p1))) ∧ p4))) ∨ p1) ∨ (p4 ∨ p3))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_158650319253466725735239739909 : ((p1 ∧ ((p1 ∧ (p4 ∨ p5)) ∧ ((True ∧ ((p2 ∧ True) ∧ True)) → ((p2 ∨ p3) ∧ (p3 ∨ p5))))) ∨ ((p5 ∨ (p2 ∨ (p4 ∨ True))) ∨ p1)) := by
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
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_824220079410615753802823774965 : ((((((p5 → True) ∨ (True ∨ p5)) → (((p4 ∨ (((p1 ∨ p5) ∧ ((p1 ∨ p3) ∧ False)) ∨ ((p4 → p3) → p4))) ∧ True) ∧ p3)) ∧ p2) → p3) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
  have h4 : ((p5 → True) ∨ (True ∨ p5)) := by
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h2, we can now drive its conclusion.
  let h5 := h2 h4
  -- We need to get the right conjuct of h5 based on <expert-advice>.
  let h6 := h5.right
  -- One of the premise coincides with the conclusion.
  exact h6
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_66347536276107477736629206699 : ((p5 ∨ (p5 ∧ ((False ∧ ((((p1 ∧ ((p1 ∧ (p2 ∨ p3)) → (p3 ∨ p2))) ∧ (p5 → True)) → (p2 ∨ (p3 ∧ False))) → p1)) ∧ p5))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_303006438542064633567021809589 : (False ∨ (p1 → ((((True ∧ p4) → p2) → (p4 ∨ ((p1 ∧ True) → p5))) ∨ (p4 ∨ ((((False ∨ p1) ∨ ((p2 → True) ∧ p3)) ∧ True) → p1))))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h2
  -- Conjunctions on the left can always be decomposed.
  let h3 := h2.left
  let h4 := h2.right
  -- Disjunctions on the left can always be decomposed.
  cases h3
  case inl h5 =>
    -- Disjunctions on the left can always be decomposed.
    cases h5
    case inl h6 =>
      -- False on the left can always be used.
      apply False.elim h6
    case inr h7 =>
      -- One of the premise coincides with the conclusion.
      exact h7
  case inr h8 =>
    -- Conjunctions on the left can always be decomposed.
    let h9 := h8.left
    let h10 := h8.right
    -- One of the premise coincides with the conclusion.
    exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_649226778384742352039685175813 : ((((((p3 → True) ∨ (p5 → ((p4 ∧ ((p1 ∧ (((p2 ∧ (True ∨ p2)) ∧ True) → p4)) → (p3 ∨ True))) ∧ p4))) → False) ∧ (False ∨ False)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_117026080582517193856180127034 : (((p2 ∨ p1) → (((p5 → (True ∧ p1)) ∨ (p4 ∧ False)) ∨ ((p2 ∧ (False ∧ p1)) ∨ (p2 ∨ ((p3 ∧ (p1 → p1)) ∨ p5))))) ∨ (False ∧ p3)) := by
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
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Implications on the right can always be decomposed.
    intro h4
    -- Conjunctions on the right can always be decomposed.
    apply And.intro
    -- True on the right can always be proven directly.
    apply True.intro
    -- One of the premise coincides with the conclusion.
    exact h3



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_137025471039968694357031167988 : (((p4 ∨ True) → (p1 ∧ ((((((False ∨ False) → False) ∧ p3) → p5) ∧ p3) ∨ ((p5 → p4) → ((p5 ∨ p5) ∧ False))))) ∨ (p2 ∨ (False → p5))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_55567931239045994737735659516 : (((p5 ∧ (p4 → ((True → False) ∨ p4))) → (((((p3 ∧ p1) → (True ∨ p5)) → p5) → p3) ∨ (p3 → ((p2 → (p4 ∨ p2)) ∧ p3)))) ∨ False) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h4
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h5
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h5
  -- One of the premise coincides with the conclusion.
  exact h4



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_165089206118932422305831350145 : (((p2 ∨ ((p2 → p5) ∧ ((False ∨ p1) → (p5 ∧ (True → ((p2 ∧ False) → p4)))))) → p2) ∨ (((p4 → (p4 → (p5 ∧ p2))) ∨ True) ∨ p3)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_180587454515971057228935569789 : (((True ∨ ((p5 → p3) ∨ ((True ∧ p5) ∨ p2))) → ((p4 ∧ p1) ∧ p4)) → (((p1 ∨ (p1 → ((p1 → p3) → (False ∨ p1)))) ∧ p3) ∨ p4)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h2 : (True ∨ ((p5 → p3) ∨ ((True ∧ p5) ∨ p2))) := by
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h3 := h1 h2
  -- We need to get the right conjuct of h3 based on <expert-advice>.
  let h4 := h3.right
  -- One of the premise coincides with the conclusion.
  exact h4



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_691623122292345618917549228501 : ((((p3 ∧ ((p2 ∧ (p1 ∨ p4)) ∨ (p5 ∧ (p2 → (p2 ∧ (False → (p4 → p1))))))) → (((True ∨ (True ∧ p2)) ∧ (p4 ∧ p1)) ∧ p5)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_740023965463892041194159167529 : ((((False ∨ False) ∨ (False ∧ (p2 ∨ ((p4 ∨ ((p3 ∨ p3) ∧ (p2 → (p1 → ((False ∧ p4) → (p3 ∨ p1)))))) ∧ (p4 → (p1 ∧ True)))))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_214173184802285313021030426952 : ((((p5 ∧ p5) → p2) → p2) ∨ (p5 ∨ ((False → p2) ∧ (((p3 ∨ p1) ∧ p1) ∨ (((((False ∨ p1) ∨ (p5 → False)) ∨ True) ∨ True) ∨ p5))))) := by
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
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_668696624489373290094841042906 : ((((((((p3 → False) ∧ p3) ∧ (((False ∨ (False ∨ ((p1 ∧ True) → (False ∨ p5)))) ∧ p1) ∧ False)) ∧ p4) ∨ False) ∨ ((False ∧ False) → p3)) ∨ p5) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- False on the left can always be used.
  apply False.elim h2
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_622803346756995344782383404149 : ((((p4 ∧ (p3 → ((p4 ∧ ((False ∨ p3) ∧ ((p1 ∨ False) ∧ p1))) ∧ (False ∧ ((True ∨ ((p1 → p4) ∧ (False → p3))) ∨ p4))))) ∨ True) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_147514658939711748653568559243 : (((p3 ∨ (p1 → (p5 → (((p3 ∧ p2) ∧ (((p3 ∨ True) → (p3 ∨ p3)) ∨ (True ∨ p4))) → False)))) ∨ p5) ∨ ((False → (p5 ∧ p1)) ∨ p3)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- False on the left can always be used.
  apply False.elim h1
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_172431101226382545220779235701 : (((p2 ∨ ((p3 ∧ False) ∨ p1)) ∧ (p5 ∧ (p4 ∧ ((p5 → p3) → (p3 ∨ False))))) ∨ ((p4 → (True ∧ ((p5 → p2) ∨ (p3 → p3)))) ∨ p3)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h2
  -- One of the premise coincides with the conclusion.
  exact h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_339625290270586301782538552329 : (p1 → (p2 ∨ ((p4 ∨ (p3 ∨ (((True ∧ (p4 → (p5 ∧ p4))) → p4) ∨ p1))) ∨ ((((False ∧ False) ∨ p2) → ((p1 ∧ p2) → p5)) → p3)))) := by
  -- Implications on the right can always be decomposed.
  intro h1
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
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_349283738779287535913926738901 : (p3 → (p2 → (((p2 ∧ (p5 ∧ (((p5 ∧ (((False ∨ (p4 → p4)) → p2) → p3)) ∧ (p5 → (False ∨ p1))) ∨ False))) ∨ p3) ∧ (True ∨ True)))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h1
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_59368990228727212649962546093 : (((p5 ∨ p4) ∨ ((True ∧ (p4 ∧ (False ∧ ((p1 ∧ ((False → ((p5 ∧ p5) ∨ p2)) → p2)) → p4)))) ∨ ((False → True) → (p2 ∨ True)))) ∨ p4) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_737646561469670217323724648253 : ((((p5 → p3) ∧ (((False → ((((p2 ∨ p3) ∨ True) → p1) ∨ p2)) ∨ (p1 ∧ (p3 ∨ ((p3 ∧ p4) → (p1 ∧ False))))) → (p1 ∨ True))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_51282982940356512606112241884 : (((p2 ∧ ((p2 → (False ∧ (p1 ∧ (p2 → p1)))) ∨ (p3 ∧ (((False ∨ p5) → p5) → False)))) ∨ (p3 → (p3 ∨ ((True ∧ False) ∧ False)))) ∨ p3) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_258799296682007493859732951860 : ((True → False) → ((p4 ∧ p1) → (p5 → (False ∧ (((p4 ∨ True) → ((p2 ∨ (p3 → (((p3 → True) ∨ True) ∨ (p5 → p5)))) → p3)) ∨ p4))))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Implications on the right can always be decomposed.
  intro h3
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Conjunctions on the left can always be decomposed.
  let h4 := h2.left
  let h5 := h2.right
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h6 : True := by
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h7 := h1 h6
  -- False on the left can always be used.
  apply False.elim h7
  -- Conjunctions on the left can always be decomposed.
  let h8 := h2.left
  let h9 := h2.right
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h8



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_429314075892954382569121835838 : (((((((((p3 → p3) ∧ p5) ∧ p1) ∨ ((p1 ∨ False) → (p3 → (p2 → True)))) ∨ (p4 ∨ p4)) → ((p3 ∨ p5) ∨ p2)) ∨ (p2 → p2)) ∧ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- One of the premise coincides with the conclusion.
  exact h1
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_51342819525278486802129805765 : (((p5 → ((p5 → (((p5 ∨ p3) ∨ (False ∧ ((True → p5) → p2))) → (p1 ∨ False))) ∧ p5)) ∨ (p3 ∨ ((p5 → (p2 ∨ p5)) ∨ p4))) ∨ p2) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
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
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_56794372913438300554927114014 : ((((True ∨ p4) → p2) ∧ (((p5 ∧ ((p1 ∨ (p3 → True)) ∧ (((p3 ∨ ((True ∨ (p2 ∨ p5)) ∨ p3)) ∧ p3) ∧ p3))) ∨ p5) ∧ p3)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_709618456382024817171177283643 : ((((p2 ∨ ((p2 ∨ p4) ∨ ((False → p1) ∧ True))) → ((True → (False ∧ ((p1 → p5) ∧ True))) ∧ (True ∧ (p2 ∨ (p2 ∨ (False → False)))))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_347278187717123022103255770006 : (p3 → (((p4 → (p4 ∧ (p2 ∧ ((p3 ∨ p1) ∨ p1)))) ∨ p4) ∨ ((p5 ∨ (p4 → ((p3 ∧ (p4 ∨ p1)) → (p5 ∧ p5)))) ∨ (True → True)))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h2
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_49141344412355535834718471611 : (((((p5 ∨ (p5 ∨ False)) ∨ (((p1 ∨ p1) → p3) ∧ p4)) ∨ (p1 ∨ ((p3 → (True ∧ True)) ∧ (p2 ∨ p2)))) ∨ (p2 → (True ∧ p4))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_115857178637281438273521101399 : (((True → ((True ∧ False) ∧ p2)) ∧ ((True ∧ p5) ∨ (False ∨ ((p3 ∧ p4) ∧ ((((p3 ∧ (p3 ∧ p3)) ∨ False) ∧ p3) → p3))))) ∨ (True ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_601753915469964964004807690300 : ((((p4 ∧ ((False ∨ (p1 ∨ ((((p2 ∧ (p4 ∨ ((p2 → p3) ∨ p3))) ∨ p2) ∨ (((p2 → p2) → p1) ∨ p3)) ∧ p1))) ∨ True)) ∧ p2) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_134184507758975565114492621604 : (((((((p5 ∧ p4) → p5) → ((False → False) ∨ p1)) ∧ (p4 → p3)) ∨ ((p5 → p5) → (p3 ∧ (False ∧ p5)))) ∨ True) ∨ (False ∧ (p3 → True))) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_648121665509995855092681130056 : ((((((p1 ∧ p5) ∧ (True → ((p2 ∨ (p3 → (p3 ∧ p4))) ∧ (((p4 → (True ∧ p1)) ∨ p2) ∧ (p1 → p2))))) ∧ p4) ∧ (p5 → p5)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_55658065115990065891942136693 : ((((p4 ∧ (True → False)) ∧ True) ∧ ((((True ∨ p2) ∧ p4) → ((True → (((p3 → (p5 → p2)) ∨ p5) ∨ (p5 ∧ p5))) → True)) → p3)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_52020767253251421525984319929 : (((False ∨ ((((True → ((False ∧ p1) ∧ (False ∧ (False → p1)))) ∧ True) ∧ p2) ∧ p5)) ∨ (p2 ∨ (((p5 ∨ True) → p4) ∨ (False ∨ p5)))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_172923288968930962164847530785 : ((p2 ∧ (p3 → ((p2 ∨ (p3 ∨ (((p4 ∧ p3) ∨ (p3 ∧ p1)) ∧ False))) ∨ True))) ∨ ((p5 → ((False ∧ p2) ∨ (p4 ∨ (p4 ∧ p1)))) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_32528927678353344277503592037 : ((p2 ∨ ((((p2 → (True → (((p1 ∨ ((p5 ∨ False) ∨ (p2 ∧ p3))) ∧ p5) ∨ p4))) ∨ False) ∧ (True ∧ True)) ∨ (True ∧ (False → False)))) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- Implications on the right can always be decomposed.
  intro h1
  -- False on the left can always be used.
  apply False.elim h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_231860022680420382172823043236 : (((True ∨ True) → False) → ((p1 ∨ (((p3 ∨ (((((p2 ∨ False) ∨ p2) → p1) ∧ p1) ∧ (False ∨ p3))) ∨ (True → p3)) ∧ p5)) ∧ (p4 → True))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h2 : (True ∨ True) := by
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h3 := h1 h2
  -- False on the left can always be used.
  apply False.elim h3
  -- Implications on the right can always be decomposed.
  intro h4
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_113515328344683712244584397599 : ((((((((p2 ∨ p3) ∨ False) → p3) ∨ p1) ∧ ((p3 ∨ p1) ∧ p1)) → (p2 ∨ (p2 ∧ (p1 → (p2 → p1))))) ∨ (p2 → p2)) ∨ (p5 ∨ p1)) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_304039634725606054456174682528 : (p1 ∨ ((p4 ∧ (((False ∧ p2) ∧ (p5 → (p1 → ((p3 ∨ p5) ∨ ((p4 → True) ∧ ((p2 ∨ ((p2 → p1) → True)) ∧ p4)))))) ∧ False)) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_124120287389527279801227280314 : (((((True → p3) ∨ p2) ∨ (p2 ∧ (True → (p3 → p1)))) ∧ ((((p4 → ((p3 ∧ p5) → False)) ∧ p5) ∨ (p1 ∧ p5)) → p3)) → (p3 ∨ p2)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- Disjunctions on the left can always be decomposed.
  cases h2
  case inl h4 =>
    -- Disjunctions on the left can always be decomposed.
    cases h4
    case inl h5 =>
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- We want to use the implication h5 based on <expert-advice>. So we show its premise.
      have h6 : True := by
        -- True on the right can always be proven directly.
        apply True.intro
      -- We have shown the premise of h5, we can now drive its conclusion.
      let h7 := h5 h6
      -- One of the premise coincides with the conclusion.
      exact h7
    case inr h8 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- One of the premise coincides with the conclusion.
      exact h8
  case inr h9 =>
    -- Conjunctions on the left can always be decomposed.
    let h10 := h9.left
    let h11 := h9.right
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h10



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_66065363080249775301096588039 : ((p5 ∨ (((((False → p4) ∧ (((p4 ∨ p1) ∧ True) ∨ False)) → p2) ∨ (((p5 ∨ (p3 ∧ True)) ∧ p5) ∨ ((p2 ∧ True) ∧ p4))) ∨ True)) ∨ p5) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_130123815147757086502209190947 : ((((True ∧ (((p3 ∧ p3) → (p3 ∧ (p4 → False))) ∨ (p5 ∧ (p1 → False)))) → (p5 ∨ (p2 ∧ p3))) ∨ (False → p2)) ∧ ((p4 ∧ True) → True)) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- False on the left can always be used.
  apply False.elim h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_244637752384547788361293254817 : ((False ∧ p5) ∨ ((p4 ∨ ((p1 → ((p5 → (p3 ∨ p2)) ∨ True)) ∨ p2)) ∨ ((True ∨ p3) → (p5 ∧ (((p5 ∧ True) → (p5 ∧ False)) ∨ p4))))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_138309948041191112641018114978 : ((p3 → ((p3 ∧ (False → (True ∨ True))) → (((((p3 → True) ∨ ((p1 ∨ True) → (p3 → p1))) → p2) → p4) ∧ p5))) ∨ ((False → p2) → True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_696368304338007632721495738136 : ((((p4 → (((p2 → (False ∨ False)) → p3) → (p4 ∧ ((p2 → False) ∧ p5)))) → ((p3 ∧ ((p5 ∧ False) ∨ True)) ∨ (False → (p5 ∧ True)))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_148546962460806890521132651175 : ((((p3 ∨ ((p3 ∧ (p5 ∧ p4)) ∨ (p5 → False))) ∧ p5) ∧ ((p1 ∧ (p2 ∨ True)) → ((False ∨ p3) → p5))) ∨ (((False → p5) ∨ p5) ∨ p3)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_354339186394881799088364527293 : (p5 → (((((p2 ∨ ((False ∨ (p5 → p1)) ∧ (p4 ∧ p4))) ∨ p3) ∧ False) ∨ ((p2 → p1) ∨ (False → ((p4 → (p2 ∨ p4)) ∨ True)))) ∧ p5)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h2
  -- False on the left can always be used.
  apply False.elim h2
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_164457138703514847621451160504 : ((((p2 ∧ ((False → ((p1 ∨ ((p4 → (True ∨ p5)) → p2)) ∨ True)) ∧ p4)) ∧ p3) ∧ p1) ∨ (p3 → ((p2 ∨ (p2 → p4)) ∨ (p3 ∧ True)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- One of the premise coincides with the conclusion.
  exact h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_809533762029928375899775965390 : (((p5 → ((((p1 ∧ ((p1 ∧ True) ∧ p1)) → (p3 → p1)) ∨ ((p5 ∧ ((p3 → (p1 ∨ p1)) ∨ ((True ∧ p5) ∨ p5))) → False)) → False)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_698437041324597311275673486940 : (((((p4 ∧ (((p2 ∧ p2) ∧ p5) ∨ False)) ∧ (p5 → (True ∨ True))) ∨ ((((False → p3) ∨ ((False ∧ p3) ∨ p2)) → False) → (False ∨ p5))) ∨ p5) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h2 : ((False → p3) ∨ ((False ∧ p3) ∨ p2)) := by
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Implications on the right can always be decomposed.
    intro h3
    -- False on the left can always be used.
    apply False.elim h3
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h4 := h1 h2
  -- False on the left can always be used.
  apply False.elim h4
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_338939248850456728773784460223 : (p1 → ((p4 ∨ p1) → ((p5 ∨ ((((p3 → p2) ∧ (p2 ∨ (True ∨ p3))) ∨ (((p4 → p1) ∨ False) ∧ ((p2 → p3) ∨ p1))) ∧ True)) ∨ p2))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Disjunctions on the left can always be decomposed.
  cases h2
  case inl h3 =>
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Conjunctions on the right can always be decomposed.
    apply And.intro
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Conjunctions on the right can always be decomposed.
    apply And.intro
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Implications on the right can always be decomposed.
    intro h4
    -- One of the premise coincides with the conclusion.
    exact h1
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h1
    -- True on the right can always be proven directly.
    apply True.intro
  case inr h5 =>
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Conjunctions on the right can always be decomposed.
    apply And.intro
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Conjunctions on the right can always be decomposed.
    apply And.intro
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Implications on the right can always be decomposed.
    intro h6
    -- One of the premise coincides with the conclusion.
    exact h1
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h1
    -- True on the right can always be proven directly.
    apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_739455210639303762508558306478 : ((((p5 ∧ False) ∨ (((p3 → (True → (p1 ∧ p3))) → (((p5 ∨ p4) ∧ (p1 ∧ ((p5 → p4) ∨ (p4 ∨ p4)))) → p1)) ∧ (p3 ∧ True))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_251436513390542385071615894420 : ((p2 → p5) ∨ (((True ∧ ((p4 ∨ ((p4 → (p2 ∨ p1)) → (p5 ∨ p4))) ∨ False)) ∧ p2) ∨ (((p2 ∧ (True ∧ p1)) → True) ∨ (p2 ∨ p2)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_586562347061050290692901774950 : ((((((p2 → True) ∧ ((p1 → (((p3 ∧ p1) ∧ (p1 ∧ (p5 ∧ p3))) ∨ True)) ∨ ((p2 ∨ (p4 ∨ p2)) ∧ (p4 → p5)))) ∧ p2) ∧ p5) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_61452391571821407404733847774 : ((p1 ∧ (((((p5 ∨ True) ∧ False) ∧ (p4 ∧ ((True ∧ (p5 → p1)) ∧ (p3 → (True → p5))))) ∧ (p5 → (p4 ∧ p4))) ∧ (p3 ∧ p1))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_45874276469963152142571448928 : (((p3 → ((p3 ∨ (p2 ∨ (((p4 ∧ (p2 ∧ (p1 → p3))) ∨ p2) ∨ p5))) → (False ∨ (True → (False ∧ (p5 ∨ (True ∧ p3))))))) → p5) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_706310793783016202367734540008 : ((((p4 ∧ ((p1 ∧ False) ∨ (p2 ∧ (p3 → p3)))) ∧ (True ∧ ((True ∧ (((False → p1) → (p4 ∧ ((False → p3) ∨ False))) ∧ True)) ∧ p3))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



