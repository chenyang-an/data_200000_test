variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_113265035952665198875103797757 : ((((((p2 → (False ∨ (False → (False ∧ p1)))) ∨ p2) → ((p2 → (True → p2)) → p3)) ∨ ((p3 ∧ p3) ∨ p2)) ∧ (p4 → p4)) ∨ (p4 → True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_358504337848819406595761082539 : (p5 → (p1 → (p2 ∨ ((((True → p5) ∧ False) → p4) → (((p2 ∧ (((p2 ∧ (p2 ∨ p4)) → False) ∨ (p1 → p4))) ∧ (p2 ∧ p3)) ∨ p5))))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h3
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_300063652253420116617295795455 : (False ∨ (((((p3 ∧ ((False ∨ ((True ∧ p2) ∨ p2)) → (((p3 ∧ False) ∨ p2) → p2))) ∨ (True ∨ p5)) ∧ (p1 ∧ p3)) ∨ p2) ∨ (True ∨ False))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_874450909540748230734002228787 : ((((((p3 ∨ ((True ∧ ((p5 ∧ (p5 ∨ p2)) ∧ (((p2 ∧ p4) ∨ ((p4 ∧ False) ∧ p2)) ∧ False))) ∨ True)) → False) ∧ True) ∧ (True ∨ p5)) → p3) ∧ True) := by
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
  cases h3
  case inl h6 =>
    -- We want to use the implication h4 based on <expert-advice>. So we show its premise.
    have h7 : (p3 ∨ ((True ∧ ((p5 ∧ (p5 ∨ p2)) ∧ (((p2 ∧ p4) ∨ ((p4 ∧ False) ∧ p2)) ∧ False))) ∨ True)) := by
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- True on the right can always be proven directly.
      apply True.intro
    -- We have shown the premise of h4, we can now drive its conclusion.
    let h8 := h4 h7
    -- False on the left can always be used.
    apply False.elim h8
  case inr h9 =>
    -- We want to use the implication h4 based on <expert-advice>. So we show its premise.
    have h10 : (p3 ∨ ((True ∧ ((p5 ∧ (p5 ∨ p2)) ∧ (((p2 ∧ p4) ∨ ((p4 ∧ False) ∧ p2)) ∧ False))) ∨ True)) := by
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- True on the right can always be proven directly.
      apply True.intro
    -- We have shown the premise of h4, we can now drive its conclusion.
    let h11 := h4 h10
    -- False on the left can always be used.
    apply False.elim h11
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_340973117603199987138983588611 : (p2 → (((p5 → False) ∧ ((p4 ∧ False) ∧ ((p4 ∧ (False ∨ (((p1 ∨ (False → ((p4 → (p2 ∧ p5)) → False))) ∨ True) → p3))) ∨ p3))) ∨ p2)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_923804703681797214488501914316 : (((((p2 ∨ p4) ∧ ((((p2 → (p3 ∨ p2)) → p1) ∧ True) ∨ False)) ∧ ((((((p1 ∧ (False → True)) → p3) → False) ∨ p5) → p4) → False)) → p1) ∧ True) := by
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
  cases h4
  case inl h6 =>
    -- Disjunctions on the left can always be decomposed.
    cases h5
    case inl h7 =>
      -- Conjunctions on the left can always be decomposed.
      let h8 := h7.left
      let h9 := h7.right
      -- We want to use the implication h8 based on <expert-advice>. So we show its premise.
      have h10 : (p2 → (p3 ∨ p2)) := by
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
    case inr h13 =>
      -- False on the left can always be used.
      apply False.elim h13
  case inr h14 =>
    -- Disjunctions on the left can always be decomposed.
    cases h5
    case inl h15 =>
      -- Conjunctions on the left can always be decomposed.
      let h16 := h15.left
      let h17 := h15.right
      -- We want to use the implication h16 based on <expert-advice>. So we show its premise.
      have h18 : (p2 → (p3 ∨ p2)) := by
        -- Implications on the right can always be decomposed.
        intro h19
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- One of the premise coincides with the conclusion.
        exact h19
      -- We have shown the premise of h16, we can now drive its conclusion.
      let h20 := h16 h18
      -- One of the premise coincides with the conclusion.
      exact h20
    case inr h21 =>
      -- False on the left can always be used.
      apply False.elim h21
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_49225163263897391439685973572 : ((((p2 ∧ p3) ∨ ((((p4 → ((False → p5) ∧ ((p2 ∨ (p5 ∨ p5)) ∧ (p4 ∧ p3)))) → False) ∨ p4) ∨ p4)) ∨ (p3 ∨ (p2 ∧ p2))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_341680178260850865843323044786 : (p2 → (((((((p3 → p1) ∨ p5) ∨ (((p2 ∧ p5) ∨ (p5 ∧ p4)) ∨ ((p2 ∨ (p1 → p3)) ∧ False))) → True) ∨ p5) → p3) ∨ (True ∧ True))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_223436327985038717013289119155 : ((False ∨ (True ∧ True)) ∧ (p4 → (((((p1 → True) → p2) → p2) ∧ (p3 ∨ (((p3 ∨ (True ∨ p3)) ∧ (False ∧ p3)) ∨ (True ∧ p3)))) ∨ True))) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_302569765382818964199138624588 : (False ∨ (p1 ∨ (((p2 ∨ p3) ∧ ((p2 ∨ True) ∨ (((((p1 → p4) → p3) ∧ False) → (((True ∨ p2) ∨ True) → False)) ∨ p5))) ∨ (p2 → p2)))) := by
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
theorem thm_5_vars_50820070103771976144993599750 : (((p5 → (((True ∧ p4) → ((p4 ∧ p5) → (p5 ∧ (False ∨ (p3 → True))))) ∧ ((p5 ∨ False) → p3))) → (((p1 → p3) → p1) ∨ True)) ∨ p5) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_351001213690866128292094088064 : (p4 → ((False ∨ ((p3 ∨ ((p5 ∨ (p4 ∨ ((p1 ∨ True) → ((False → p2) ∨ p2)))) → p2)) ∧ ((p2 ∨ (False ∧ p1)) ∧ p2))) ∨ (p5 → True))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h2
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_172889111933092651831736014975 : ((p1 ∧ (False ∨ ((((p4 ∨ p4) ∨ (p4 ∧ p2)) ∨ p3) → (p2 → (False ∨ False))))) ∨ ((False → p4) ∨ ((p4 ∨ (p4 → (True ∨ p1))) ∧ p2))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_611382115804802551828490669483 : (((((True ∧ (p5 ∧ ((True ∧ p2) ∨ (p5 → ((((p4 ∨ p3) → (p4 ∧ p5)) ∧ p5) → (((p4 ∧ p1) → p1) ∧ p5)))))) → p1) ∨ True) ∨ p1) ∧ True) := by
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
theorem thm_5_vars_65108812441714725706757065210 : ((p2 ∨ (p4 ∨ ((((p1 ∧ p4) → p5) → p2) ∨ ((p5 → (p3 → ((p1 → p1) ∧ (p5 ∨ p5)))) ∨ ((p5 ∧ p4) → (True ∧ p3)))))) ∨ p4) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h3
  -- One of the premise coincides with the conclusion.
  exact h3
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_114427233690939099378973039252 : (((p2 ∧ (p2 ∨ (((p4 ∧ ((p4 ∧ p2) ∧ p2)) ∨ (False ∨ (p3 ∧ True))) ∨ (False ∧ True)))) ∨ ((True ∨ (p3 → p5)) ∨ p4)) ∨ (p2 ∧ p2)) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_58729118146021594644313641092 : (((p3 → p2) ∧ (((True → True) ∨ True) → (((((((((p4 → False) ∧ False) ∧ p5) ∨ p4) ∨ False) ∨ p5) ∨ p1) ∨ (False ∧ p2)) ∧ p5))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_349966627576224545500971754647 : (p4 → (((p5 ∧ (p3 → (((p2 ∧ False) ∨ (p2 → (p2 ∧ (p5 ∨ (((p3 ∧ p5) → p2) ∧ ((True → p3) ∧ False)))))) ∧ p2))) ∧ p4) ∨ p4)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_666511691565457518344433688476 : (((((((p5 → ((p3 ∧ p3) ∨ ((p3 ∨ p2) → p2))) ∨ True) ∧ (p1 ∨ p2)) ∨ (p3 ∨ (p3 → (p3 ∧ p3)))) ∧ (p2 ∨ (p2 ∨ True))) ∨ False) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- One of the premise coincides with the conclusion.
  exact h1
  -- One of the premise coincides with the conclusion.
  exact h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_40942094100729509464249349968 : (((((((p3 → (p2 ∧ (p4 → ((((p1 → p1) ∨ (True → p2)) → p4) ∨ p4)))) → p3) ∧ (False → p1)) → p1) ∨ (p1 ∧ False)) ∨ p5) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_304002519970840264231492409260 : (p1 ∨ (((p3 ∧ p2) → ((p2 ∧ (False → (p1 ∨ (((p2 → p2) → False) → (True ∨ (p1 ∧ p1)))))) → (((p4 ∨ p1) ∧ False) ∨ p5))) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_647683057891373360010720137670 : ((((p5 → ((p2 → p5) ∧ (p5 → (False ∨ (((((p3 → False) ∧ p1) ∧ p3) ∧ ((p4 ∧ (p3 → (p1 ∧ p2))) ∧ False)) → p5))))) → p4) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_358234848804229806232227734790 : (p5 → (p4 ∨ (((((p1 ∧ ((p5 → p2) ∨ False)) ∨ (p1 ∨ (p4 → p2))) ∨ p5) → (p4 ∧ (p2 → False))) → ((p1 ∧ (p4 ∧ p3)) ∨ p4)))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h2
  -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
  have h3 : (((p1 ∧ ((p5 → p2) ∨ False)) ∨ (p1 ∨ (p4 → p2))) ∨ p5) := by
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h1
  -- We have shown the premise of h2, we can now drive its conclusion.
  let h4 := h2 h3
  -- We need to get the left conjuct of h4 based on <expert-advice>.
  let h5 := h4.left
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h5



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_328705518203061333680350534883 : (True → (((p4 → (p4 → (True ∧ True))) ∧ (((False ∧ False) ∨ p1) ∨ p1)) ∨ ((p3 ∧ (((p5 ∨ p3) ∧ p1) → (p2 ∧ p4))) ∨ (True ∨ p2)))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_309333213567386034213110072695 : (p2 ∨ ((((((p5 ∧ p2) ∨ p1) ∧ (p4 ∧ (p5 → p5))) ∧ ((p5 ∧ p3) → (True ∨ (p5 ∨ (True ∨ p2))))) ∨ (p4 → True)) ∨ (p2 ∧ True))) := by
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
theorem thm_5_vars_134878820435183040210370370308 : (((p2 → (True ∨ (((p5 ∨ p2) → ((True ∧ p1) → p4)) → ((False ∧ (((True ∧ p4) → p3) ∨ p4)) → p5)))) → p1) ∨ (p4 ∨ (False → p5))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_973924174988382732217510048747 : ((((True → True) → ((((((p2 ∧ (True → p5)) ∧ p3) ∧ p3) → ((((((False ∧ p1) ∨ p5) ∧ p3) ∧ True) → p2) ∨ p4)) ∧ p5) ∧ p2)) → p2) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h1
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h2 : (True → True) := by
    -- Implications on the right can always be decomposed.
    intro h3
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h4 := h1 h2
  -- We need to get the right conjuct of h4 based on <expert-advice>.
  let h5 := h4.right
  -- One of the premise coincides with the conclusion.
  exact h5
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_637220264751221715327934023371 : (((((((p1 ∧ ((p2 → True) → True)) ∧ (p5 ∨ (p3 → p4))) ∧ p1) → (p4 ∨ ((((True ∧ (p5 → p1)) ∧ p2) → p5) ∧ p2))) → p5) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_58901152751394099760700007068 : (((False ∧ p5) ∨ (((((((p2 → p4) ∧ (True → p5)) ∨ p5) ∧ True) ∨ (((False ∧ p5) ∨ p4) → True)) → ((False → p4) → p1)) → p2)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_884539658354937244221235242 : ((p1 → (((p4 ∨ p4) → (True ∧ (p5 ∨ (((p1 ∧ ((False ∧ p3) ∧ (False ∧ p3))) ∨ p3) ∧ (True ∨ (p5 ∧ False)))))) ∨ p1)) ∨ p1) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_92017763870444646709911341355 : (((True ∧ True) → (((p3 ∨ p5) ∨ ((False ∨ p2) → p5)) ∧ (((((((p4 ∧ (True → p1)) ∧ p1) ∨ p1) → p4) → p1) ∨ False) ∧ p1))) → p1) := by
  -- Implications on the right can always be decomposed.
  intro h1
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
  -- We need to get the right conjuct of h3 based on <expert-advice>.
  let h4 := h3.right
  -- We need to get the right conjuct of h4 based on <expert-advice>.
  let h5 := h4.right
  -- One of the premise coincides with the conclusion.
  exact h5



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_105135202662908039206387571587 : ((((False ∧ (((p4 ∧ ((p1 → True) ∨ True)) → p1) ∨ p4)) ∨ ((True → False) → ((True ∨ p3) ∧ p5))) ∨ (p1 ∨ (False → p5))) ∧ (p4 ∨ True)) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- False on the left can always be used.
  apply False.elim h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_429832990652642124813585228510 : ((((((p4 ∨ (((p2 ∨ p2) → p5) ∨ False)) → ((p4 ∧ p2) → p3)) → ((p1 → False) ∨ (((p5 → p2) → False) ∧ True))) ∨ (False → p4)) ∧ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- False on the left can always be used.
  apply False.elim h1
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_148222969761088461832306880213 : (((((((False → (((True ∨ p2) ∧ p4) ∨ p1)) → p2) ∨ (p4 → p1)) → p5) ∨ p4) ∨ (False ∨ (p4 ∨ p2))) ∨ (False → (True → (True → p4)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Implications on the right can always be decomposed.
  intro h3
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_655625755893492253886937494546 : (((((True → (((True ∧ p4) ∧ (p2 ∨ (True ∨ (p2 ∨ ((True ∧ ((p2 ∧ p4) ∨ False)) → p4))))) ∨ p4)) → (p5 ∨ p5)) ∨ (p4 → True)) ∨ p5) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_216752653455153979092166346476 : ((((p1 → True) → p1) ∧ p5) → (p1 ∨ (((p1 ∨ (((p1 ∧ p3) ∨ p2) ∨ p1)) → p3) ∧ ((True ∨ True) → (((p2 → False) ∨ p2) ∧ p2))))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
  have h4 : (p1 → True) := by
    -- Implications on the right can always be decomposed.
    intro h5
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h2, we can now drive its conclusion.
  let h6 := h2 h4
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- One of the premise coincides with the conclusion.
  exact h6



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_165223132298728315545133206346 : ((((p1 ∧ ((True ∧ p1) ∨ p5)) ∧ ((False → p5) ∧ ((p2 ∨ p4) ∧ p5))) ∨ (True ∧ p3)) ∨ (p1 → (((p1 ∨ (True ∨ False)) ∧ True) ∨ False))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- One of the premise coincides with the conclusion.
  exact h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_656096979741865919567006312406 : ((((((((p2 ∨ (p5 ∨ p3)) → (((p1 ∨ p2) ∧ False) ∧ p5)) ∨ True) ∨ False) ∧ (((p2 ∧ p5) → (p5 ∧ p1)) → p5)) ∨ (True ∨ p5)) ∨ p3) ∧ True) := by
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
theorem thm_5_vars_301152217839539123038584311657 : (False ∨ (((p1 ∨ False) ∧ (((p2 ∨ False) ∧ False) ∨ False)) ∨ (((((False ∧ (True ∨ p4)) ∧ p1) ∨ p3) ∧ ((p1 ∧ p5) ∨ (True ∨ p1))) → p3))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- Disjunctions on the left can always be decomposed.
  cases h2
  case inl h4 =>
    -- Conjunctions on the left can always be decomposed.
    let h5 := h4.left
    let h6 := h4.right
    -- Conjunctions on the left can always be decomposed.
    let h7 := h5.left
    let h8 := h5.right
    -- False on the left can always be used.
    apply False.elim h7
  case inr h9 =>
    -- Disjunctions on the left can always be decomposed.
    cases h3
    case inl h10 =>
      -- Conjunctions on the left can always be decomposed.
      let h11 := h10.left
      let h12 := h10.right
      -- One of the premise coincides with the conclusion.
      exact h9
    case inr h13 =>
      -- Disjunctions on the left can always be decomposed.
      cases h13
      case inl h14 =>
        -- One of the premise coincides with the conclusion.
        exact h9
      case inr h15 =>
        -- One of the premise coincides with the conclusion.
        exact h9



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_39749450732409100308228241380 : (((True → ((p5 ∨ (((p2 ∨ True) ∨ p5) ∧ ((((((p4 ∨ p5) ∧ p2) ∧ (p5 ∧ p4)) ∨ True) ∧ (True → p5)) ∧ True))) ∧ p2)) ∧ True) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_157358050885927528462969866621 : (((False → (False → ((((p3 → p5) ∨ (p1 ∨ p3)) → (((p2 ∧ p4) → p1) ∧ False)) ∨ False))) → p1) ∨ ((True → (False ∧ (p1 ∧ p2))) → p2)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h2 : True := by
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h3 := h1 h2
  -- We need to get the left conjuct of h3 based on <expert-advice>.
  let h4 := h3.left
  -- False on the left can always be used.
  apply False.elim h4



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_667923766188998789370799819851 : ((((p2 ∨ ((False ∧ p1) ∨ ((p4 ∧ (False ∧ (((p4 ∨ ((True ∧ p4) ∨ p1)) → (p4 → True)) ∧ p5))) ∨ True))) ∧ (True ∧ (p4 → False))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_330921636328254738731252224734 : (True → (p4 → ((((((p4 ∧ True) ∨ (p1 ∧ p1)) ∧ (False → ((False ∧ True) ∨ p2))) → p3) → (True ∨ p5)) → (((True → p2) ∨ p5) ∨ True)))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Implications on the right can always be decomposed.
  intro h3
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_337298224443440720003535329904 : (p1 → (((((True ∨ (True ∨ False)) → p4) ∧ (p3 ∧ ((True ∧ True) ∧ (p3 ∧ p3)))) ∨ ((p3 ∨ (p5 ∨ True)) ∨ False)) ∧ ((True ∨ p3) ∨ p5))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_198407690982116822885291675202 : ((p4 ∧ (((p1 ∨ (p1 ∨ p5)) → p2) ∨ p1)) ∨ (((p1 ∧ ((p2 ∨ (p2 ∧ p3)) ∨ ((p5 → (p2 ∨ (False ∨ p5))) ∧ True))) ∧ True) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_784594029350214795080015446688 : (((p3 ∨ (p1 ∨ (p2 ∨ ((False ∨ (p1 ∧ p2)) ∨ (p4 → (p4 ∧ (((True → (p2 ∨ p1)) ∨ (((True → p3) ∨ p5) → p5)) → p4))))))) ∨ p1) ∧ True) := by
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
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- One of the premise coincides with the conclusion.
  exact h1
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
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_43147294578298562738942471327 : (((((True → ((p1 ∧ (True ∧ p3)) ∧ p2)) ∧ (((p1 ∨ (True → ((p4 ∧ p5) → False))) ∨ ((p1 ∨ p5) → True)) ∧ p2)) ∧ True) → p1) ∨ p4) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- Conjunctions on the left can always be decomposed.
  let h4 := h2.left
  let h5 := h2.right
  -- Conjunctions on the left can always be decomposed.
  let h6 := h5.left
  let h7 := h5.right
  -- Disjunctions on the left can always be decomposed.
  cases h6
  case inl h8 =>
    -- Disjunctions on the left can always be decomposed.
    cases h8
    case inl h9 =>
      -- One of the premise coincides with the conclusion.
      exact h9
    case inr h10 =>
      -- We want to use the implication h4 based on <expert-advice>. So we show its premise.
      have h11 : True := by
        -- True on the right can always be proven directly.
        apply True.intro
      -- We have shown the premise of h4, we can now drive its conclusion.
      let h12 := h4 h11
      -- We need to get the left conjuct of h12 based on <expert-advice>.
      let h13 := h12.left
      -- We need to get the left conjuct of h13 based on <expert-advice>.
      let h14 := h13.left
      -- One of the premise coincides with the conclusion.
      exact h14
  case inr h15 =>
    -- We want to use the implication h4 based on <expert-advice>. So we show its premise.
    have h16 : True := by
      -- True on the right can always be proven directly.
      apply True.intro
    -- We have shown the premise of h4, we can now drive its conclusion.
    let h17 := h4 h16
    -- We need to get the left conjuct of h17 based on <expert-advice>.
    let h18 := h17.left
    -- We need to get the left conjuct of h18 based on <expert-advice>.
    let h19 := h18.left
    -- One of the premise coincides with the conclusion.
    exact h19



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_113556538094177474235953586823 : ((((True ∨ True) ∧ ((((p2 ∧ p3) ∨ (p1 → True)) ∧ p3) ∨ (((True → (False ∧ p5)) ∧ (p3 ∨ p4)) → p1))) ∨ (p4 → p5)) ∨ (p1 → p4)) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- Disjunctions on the left can always be decomposed.
  cases h3
  case inl h4 =>
    -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
    have h5 : True := by
      -- True on the right can always be proven directly.
      apply True.intro
    -- We have shown the premise of h2, we can now drive its conclusion.
    let h6 := h2 h5
    -- We need to get the left conjuct of h6 based on <expert-advice>.
    let h7 := h6.left
    -- False on the left can always be used.
    apply False.elim h7
  case inr h8 =>
    -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
    have h9 : True := by
      -- True on the right can always be proven directly.
      apply True.intro
    -- We have shown the premise of h2, we can now drive its conclusion.
    let h10 := h2 h9
    -- We need to get the left conjuct of h10 based on <expert-advice>.
    let h11 := h10.left
    -- False on the left can always be used.
    apply False.elim h11



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_56782083722695953894606501211 : ((((p3 ∧ p2) → True) ∧ (((((p1 ∧ p5) ∨ ((((p4 → p3) ∧ (p1 ∨ False)) → True) ∧ ((p1 ∧ True) ∧ p5))) → p2) ∨ True) ∨ p4)) ∨ p1) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_242990285780253442939569271035 : ((p4 → True) ∧ ((((((True → (False ∧ ((p2 ∧ p4) ∨ p2))) → (p1 ∧ (True → True))) ∨ False) ∨ (p5 → p3)) ∧ p5) → ((True ∧ p1) ∨ True))) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro
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
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- True on the right can always be proven directly.
      apply True.intro
    case inr h7 =>
      -- False on the left can always be used.
      apply False.elim h7
  case inr h8 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_53962198229010342310033909047 : ((((((p1 ∨ (p5 ∧ p2)) ∧ p4) ∨ (False → True)) ∧ p5) → ((((p2 ∧ p1) ∧ p1) ∨ ((p5 ∨ False) ∧ p5)) ∧ (p2 → (p4 ∧ p5)))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_149251884455336552924011570607 : (((p2 ∨ p3) ∨ ((((p3 → p1) ∨ p2) ∧ ((p1 ∧ p4) ∨ (p4 → p2))) → ((p1 → False) ∧ (p4 ∧ p2)))) ∨ (p5 → (p5 → (p2 ∨ True)))) := by
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
theorem thm_5_vars_312250964260264127143103084481 : (p2 ∨ (p1 → ((True → (((p2 ∧ (((p3 ∧ False) ∨ p3) ∧ True)) ∧ p2) ∨ True)) ∧ (False → (((p3 ∨ p2) → ((p5 ∨ p3) → True)) ∨ True))))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h2
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- Implications on the right can always be decomposed.
  intro h3
  -- False on the left can always be used.
  apply False.elim h3



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_262302504317567794124966716991 : (True ∧ (((p2 ∧ ((((p2 → p1) ∧ ((p5 → False) ∧ True)) → p2) ∨ p3)) ∧ (((p2 → (p1 ∨ ((p4 ∧ p3) ∧ p1))) ∨ p1) → p2)) ∨ True)) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_697718667316837672661657546394 : ((((False → (((False → p5) → p5) → (p2 ∧ (p2 ∨ (p4 ∨ p5))))) ∧ (((False ∧ ((p5 → p2) → p4)) → p5) → ((p1 → p5) ∧ p3))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_180129596194091868090413651809 : ((((((p3 ∧ True) ∧ ((p1 ∨ p2) → (p2 ∨ False))) → p5) → p5) → p2) → ((p5 ∧ p1) ∨ (True → (p2 ∨ ((True → False) → (False → True)))))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h2
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h3
  -- Implications on the right can always be decomposed.
  intro h4
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_336447417955580973093558682843 : (p1 → ((p5 ∨ ((((False ∨ ((p4 → True) ∨ p4)) → p2) → (((p2 ∨ p2) ∧ (False ∨ (False ∧ (p1 → False)))) ∧ p4)) ∨ (True ∨ True))) ∨ p1)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_308589843311907281911047126006 : (p2 ∨ ((((False ∧ p5) ∨ p3) ∨ (p1 ∨ ((True ∨ ((((p3 ∨ False) ∧ ((True ∧ p5) ∧ p4)) ∨ p3) ∧ False)) ∨ (p1 ∧ (p3 → p3))))) ∨ False)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_114505545370504820241988329928 : ((((p3 ∧ (p3 ∨ p2)) ∨ (((p2 ∨ (p3 ∨ p5)) ∨ p4) → (p1 ∨ ((p3 → p4) ∧ p2)))) → (p5 ∧ (False ∨ (p1 ∨ p5)))) ∨ (p1 → p1)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_137365561537177991033424788499 : ((p3 ∧ ((p1 ∨ ((((((True → p1) → True) → p1) → p5) ∨ ((p1 → (p3 ∧ p1)) ∨ False)) → p4)) ∧ (True ∧ False))) ∨ ((p2 → True) → True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_707853009313481939847829519245 : ((((p2 ∧ ((p5 → False) → (p4 ∧ (p2 ∨ p3)))) ∨ ((((((((False ∨ True) ∨ p1) ∨ p4) ∧ (p5 → p4)) → p5) ∨ p5) ∨ True) ∨ p3)) ∨ p5) ∧ True) := by
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
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_118153134782774776461221062912 : ((False ∨ ((p4 ∧ (p1 ∧ ((True ∨ True) ∧ p2))) ∨ (p2 → (((((False → p5) ∨ p2) ∧ (p5 ∨ False)) ∧ p2) ∨ (False ∨ p1))))) ∨ (False → True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_156973603657055998382654757036 : (((((False ∨ p4) → ((((False → False) ∨ p3) → p3) ∨ p3)) → (((True → p2) ∧ p2) ∨ p2)) ∨ p4) ∨ (((p3 ∧ p2) ∨ False) → (True → True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_119478769354891778576894269617 : ((p4 → (p3 ∧ (((p5 → ((p3 → False) ∨ p5)) ∧ (False ∧ (((True ∧ (p3 → (True ∨ False))) ∨ True) ∨ p5))) ∨ (p3 ∧ p5)))) ∨ (True → True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_464559304942261381859832146559 : (((((p3 ∨ ((p4 ∧ ((True ∧ False) ∧ (p1 → True))) ∨ True)) → (p4 ∧ (p5 ∧ p2))) → (((((p2 → True) ∨ p4) ∨ True) → False) ∨ p5)) ∧ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h2 : (p3 ∨ ((p4 ∧ ((True ∧ False) ∧ (p1 → True))) ∨ True)) := by
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h3 := h1 h2
  -- We need to get the right conjuct of h3 based on <expert-advice>.
  let h4 := h3.right
  -- We need to get the left conjuct of h4 based on <expert-advice>.
  let h5 := h4.left
  -- One of the premise coincides with the conclusion.
  exact h5
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_49123128123354770062702849277 : (((((p2 → (((p1 ∨ p2) → (True ∨ True)) ∧ p5)) ∧ (p2 ∧ p1)) ∧ ((p3 → (p5 → p4)) ∧ (False ∨ p3))) ∨ ((p1 → p4) → p3)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_115816704712545637159206886281 : ((((p2 ∨ p2) ∧ (p5 → p3)) ∧ ((p2 ∨ (p1 ∨ True)) ∧ ((p3 → ((((True → True) → p1) ∨ p2) ∧ True)) ∨ (False ∨ p3)))) ∨ (False → p4)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_330467809381030850907407761382 : (True → (p3 ∨ (p2 → (((((((p4 → False) ∨ p1) ∧ p5) → p3) → (p4 → ((p3 → p5) ∨ (p5 ∨ p4)))) ∧ (p1 ∧ False)) ∨ (p1 → True))))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h2
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h3
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_66395581411614611017218730751 : ((p5 ∨ (True → (((p1 → p3) ∧ p2) ∨ (False ∧ (((((False ∧ p3) ∨ p1) ∨ p4) → (p2 ∧ (p1 ∧ p1))) ∨ ((False ∨ p3) → False)))))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_136367130701800229695532321732 : ((((p1 ∧ (True ∧ p5)) ∨ False) ∨ (((p3 → p4) → ((((p2 ∨ p1) ∨ (p5 → p3)) ∨ p5) → (p2 ∨ p4))) ∧ p2)) ∨ ((True ∧ False) → p2)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- False on the left can always be used.
  apply False.elim h3



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_174374133319223510134996798690 : (((((False ∨ (p3 → (True ∧ False))) ∨ False) ∨ True) ∧ ((p5 ∧ (p5 → p4)) ∧ p4)) → ((((((True ∧ False) ∨ p2) ∧ p1) → p4) → p3) ∨ p5)) := by
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
      -- Disjunctions on the left can always be decomposed.
      cases h5
      case inl h6 =>
        -- False on the left can always be used.
        apply False.elim h6
      case inr h7 =>
        -- Conjunctions on the left can always be decomposed.
        let h8 := h3.left
        let h9 := h3.right
        -- Conjunctions on the left can always be decomposed.
        let h10 := h8.left
        let h11 := h8.right
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- One of the premise coincides with the conclusion.
        exact h10
    case inr h12 =>
      -- False on the left can always be used.
      apply False.elim h12
  case inr h13 =>
    -- Conjunctions on the left can always be decomposed.
    let h14 := h3.left
    let h15 := h3.right
    -- Conjunctions on the left can always be decomposed.
    let h16 := h14.left
    let h17 := h14.right
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h16



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_781611817689087331356264964592 : (((p2 ∨ (p1 ∨ ((p2 ∧ True) → ((p2 ∧ True) ∧ ((p4 → (((p2 ∨ p4) → (p2 ∧ p1)) → ((p5 ∧ (p3 → p5)) ∨ p1))) ∧ p2))))) ∨ p4) ∧ True) := by
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
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- One of the premise coincides with the conclusion.
  exact h2
  -- True on the right can always be proven directly.
  apply True.intro
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h4
  -- Implications on the right can always be decomposed.
  intro h5
  -- Conjunctions on the left can always be decomposed.
  let h6 := h1.left
  let h7 := h1.right
  -- We want to use the implication h5 based on <expert-advice>. So we show its premise.
  have h8 : (p2 ∨ p4) := by
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- One of the premise coincides with the conclusion.
    exact h6
  -- We have shown the premise of h5, we can now drive its conclusion.
  let h9 := h5 h8
  -- We need to get the right conjuct of h9 based on <expert-advice>.
  let h10 := h9.right
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h10
  -- Conjunctions on the left can always be decomposed.
  let h11 := h1.left
  let h12 := h1.right
  -- One of the premise coincides with the conclusion.
  exact h11
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_257211482262044482496427423040 : ((p2 ∨ p2) → (((p3 ∨ p4) → (p1 ∧ (True → p3))) ∨ (((((False → p4) → p1) ∧ p3) ∨ True) ∧ ((((p1 → p1) ∧ p3) → p1) ∨ True)))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h2 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Conjunctions on the right can always be decomposed.
    apply And.intro
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro
  case inr h3 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Conjunctions on the right can always be decomposed.
    apply And.intro
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_299469584680179478230041283376 : (False ∨ ((True → ((((p4 ∨ True) ∧ p2) ∧ (True ∨ ((p5 ∧ (p3 → p5)) ∨ p3))) → ((((p3 → (p4 ∧ p5)) → p4) ∧ p3) ∨ False))) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_34370604473536602893770862651 : ((True → ((False ∨ p2) → ((p5 ∧ (p4 ∨ ((False ∨ (p3 ∧ (((p5 → p4) → p2) ∨ ((True ∨ (p3 → p1)) ∨ False)))) ∨ p3))) ∨ True))) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h1
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
    -- True on the right can always be proven directly.
    apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_442286332504155229016562652555 : (((((((p5 ∧ ((p1 → (p1 ∧ ((p4 ∧ False) ∨ p4))) ∧ p1)) → p2) → ((p4 ∨ True) ∧ (p2 ∧ False))) ∨ True) ∨ ((p2 → p1) ∧ p4)) ∧ True) ∧ True) := by
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
theorem thm_5_vars_675134035544235629121191017782 : ((((((p5 ∨ (((True ∨ ((p5 ∧ (p3 ∨ p2)) ∨ p2)) → (p1 ∨ p3)) ∨ (p5 → False))) → p1) ∨ p3) ∧ ((True ∧ (p3 ∧ p3)) → True)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_135481062844635216299389603107 : (((((True ∧ False) ∨ (p5 → True)) ∧ ((True ∧ p1) ∨ ((p3 ∨ p1) ∧ ((p4 → p5) ∨ p3)))) → (False ∨ (False → p5))) ∨ (p1 ∨ (False → p1))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_123969676478347191312687023150 : (((((True → ((p3 ∨ p5) ∨ (p2 ∧ p4))) ∨ (p2 ∨ p4)) ∨ p2) ∨ (True ∨ ((p5 → (p3 ∧ True)) ∨ ((p1 → True) → False)))) → (p2 ∨ True)) := by
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
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- True on the right can always be proven directly.
        apply True.intro
      case inr h5 =>
        -- Disjunctions on the left can always be decomposed.
        cases h5
        case inl h6 =>
          -- Show the left disjunct based on <expert-advice>.
          apply Or.inl
          -- One of the premise coincides with the conclusion.
          exact h6
        case inr h7 =>
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- True on the right can always be proven directly.
          apply True.intro
    case inr h8 =>
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- One of the premise coincides with the conclusion.
      exact h8
  case inr h9 =>
    -- Disjunctions on the left can always be decomposed.
    cases h9
    case inl h10 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- True on the right can always be proven directly.
      apply True.intro
    case inr h11 =>
      -- Disjunctions on the left can always be decomposed.
      cases h11
      case inl h12 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- True on the right can always be proven directly.
        apply True.intro
      case inr h13 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- True on the right can always be proven directly.
        apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_61423890294904196397710249822 : ((p1 ∧ ((((((p1 ∧ True) ∧ (p3 ∨ (p5 ∨ ((p2 ∧ p3) → False)))) ∧ p4) ∨ ((p3 → p2) → p1)) ∨ ((p4 ∨ p3) → p5)) → p2)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_140297195061851860829114814418 : ((((p4 ∨ (False → p2)) → ((p5 ∨ ((p5 ∧ ((False ∧ p5) ∧ (p2 → False))) ∧ p1)) ∧ p1)) ∧ (p1 → (False ∧ True))) → ((p4 ∨ p5) ∧ p5)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
  have h4 : (p4 ∨ (False → p2)) := by
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h5
    -- False on the left can always be used.
    apply False.elim h5
  -- We have shown the premise of h2, we can now drive its conclusion.
  let h6 := h2 h4
  -- We need to get the right conjuct of h6 based on <expert-advice>.
  let h7 := h6.right
  -- We want to use the implication h3 based on <expert-advice>. So we show its premise.
  have h8 : p1 := by
    -- One of the premise coincides with the conclusion.
    exact h7
  -- We have shown the premise of h3, we can now drive its conclusion.
  let h9 := h3 h8
  -- We need to get the left conjuct of h9 based on <expert-advice>.
  let h10 := h9.left
  -- False on the left can always be used.
  apply False.elim h10
  -- Conjunctions on the left can always be decomposed.
  let h11 := h1.left
  let h12 := h1.right
  -- We want to use the implication h11 based on <expert-advice>. So we show its premise.
  have h13 : (p4 ∨ (False → p2)) := by
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h14
    -- False on the left can always be used.
    apply False.elim h14
  -- We have shown the premise of h11, we can now drive its conclusion.
  let h15 := h11 h13
  -- We need to get the right conjuct of h15 based on <expert-advice>.
  let h16 := h15.right
  -- We want to use the implication h12 based on <expert-advice>. So we show its premise.
  have h17 : p1 := by
    -- One of the premise coincides with the conclusion.
    exact h16
  -- We have shown the premise of h12, we can now drive its conclusion.
  let h18 := h12 h17
  -- We need to get the left conjuct of h18 based on <expert-advice>.
  let h19 := h18.left
  -- False on the left can always be used.
  apply False.elim h19



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_321254148631690837775783339113 : (p4 ∨ (p4 ∨ ((False → (((p1 ∨ p5) → (True → p4)) → ((p1 ∨ p4) ∨ p2))) ∧ (p1 → (p2 ∨ ((True ∧ ((False ∧ p2) ∧ p5)) ∨ p1)))))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- False on the left can always be used.
  apply False.elim h1
  -- Implications on the right can always be decomposed.
  intro h3
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h3



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_653797940617696194888172465154 : (((((((((p5 ∨ (p2 → (p1 ∨ p2))) ∨ False) → (p3 ∨ p1)) ∨ (p1 ∨ p3)) → ((False ∨ (p1 ∨ True)) ∧ p2)) ∧ p4) ∨ (p1 → True)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_249428029997286132517371512412 : ((p5 ∨ False) ∨ ((((False ∧ ((p1 ∧ False) → ((p3 ∨ p2) ∧ p3))) → p3) → ((True → ((True ∨ p2) ∨ True)) ∧ False)) → (p2 ∨ (True ∧ p4)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h2 : ((False ∧ ((p1 ∧ False) → ((p3 ∨ p2) ∧ p3))) → p3) := by
    -- Implications on the right can always be decomposed.
    intro h3
    -- Conjunctions on the left can always be decomposed.
    let h4 := h3.left
    let h5 := h3.right
    -- False on the left can always be used.
    apply False.elim h4
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h6 := h1 h2
  -- We need to get the right conjuct of h6 based on <expert-advice>.
  let h7 := h6.right
  -- False on the left can always be used.
  apply False.elim h7



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_60379817447850882440963434411 : (((p3 → p2) → ((p5 → (((((p1 ∨ False) ∨ (p4 ∧ (p3 ∧ p5))) ∨ ((True ∨ (p2 ∧ p3)) → p2)) ∧ p2) ∨ (p5 ∨ p2))) ∨ p5)) ∨ p4) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h2
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- One of the premise coincides with the conclusion.
  exact h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_635547389915805770093543976844 : ((((((p1 → (((p4 ∨ p4) → p2) ∨ ((((p1 ∨ True) ∧ True) ∧ p2) ∨ (p2 ∨ p5)))) → p4) ∨ (p4 → (p3 ∧ (p4 ∧ p4)))) → p4) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_41674034419064352113273513157 : ((((((p4 → False) ∨ p5) ∧ (p3 → p4)) ∨ (p1 → ((True → (p3 ∨ (p2 → (p5 ∨ p1)))) ∨ ((p5 → False) → (True → False))))) ∨ False) ∨ p3) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
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
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h3
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_607963929290684945972538275710 : (((((p2 → (p4 ∨ ((p3 → p4) → (p2 → (p3 → (p1 ∨ (False ∨ (((p1 ∧ (p3 ∨ p4)) → (False ∨ p4)) ∨ p1)))))))) ∧ p5) ∨ True) ∨ p2) ∧ True) := by
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
theorem thm_5_vars_318609733166426380648398973593 : (p4 ∨ (((((p2 → False) ∧ p1) → p3) ∨ (False ∨ (((False ∨ (False ∨ p4)) ∨ ((p4 ∧ ((False → p3) ∧ True)) ∧ p1)) → p2))) ∨ (p3 ∨ True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_683927129365229726060333509897 : (((((((((((False → p2) → True) ∧ True) ∧ ((p5 → False) → p1)) ∧ p2) ∨ p1) ∨ p5) → p5) ∨ ((False → (True ∨ p4)) → (True ∨ p4))) ∨ p5) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_114627113142796690769914079812 : ((((((p1 ∧ p3) ∧ ((p1 ∧ p3) ∧ ((p1 → (p4 ∨ p1)) ∧ p4))) ∨ p5) ∨ p5) ∨ ((p3 ∧ p1) ∨ ((p1 → True) ∨ p2))) ∨ (p2 ∨ p4)) := by
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
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_347595363594573429572475361967 : (p3 → ((((p5 → p2) ∧ p1) ∨ p5) ∨ (False ∨ (((p4 → (p3 ∧ p3)) → ((False → (p5 → p2)) ∧ p4)) ∨ ((p3 ∧ (p3 → p2)) ∨ p3))))) := by
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
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_40345193088669741611974667682 : (((((p3 ∨ ((((p4 ∧ (p2 ∧ True)) → (((False → p5) ∨ (p1 → False)) ∨ (p5 → True))) → (False ∧ False)) ∧ p4)) ∨ p2) ∨ False) ∨ True) ∨ p5) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_248886117609614888883083024844 : ((p3 ∨ p5) ∨ (((p1 ∨ p2) ∧ ((p1 ∨ (p2 ∧ (p1 ∨ (p1 ∨ p3)))) ∨ (False → p4))) ∨ ((False → p3) ∧ ((p3 ∧ True) → (p3 ∨ p2))))) := by
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
  -- Conjunctions on the left can always be decomposed.
  let h3 := h2.left
  let h4 := h2.right
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- One of the premise coincides with the conclusion.
  exact h3



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_104656064694910822265415698279 : (((p2 ∧ ((p4 ∨ ((p3 ∨ p5) → ((p2 → (((p1 ∧ (True ∧ p5)) ∧ True) → (p2 ∧ p3))) → True))) → p1)) ∨ (p4 → p4)) ∧ (True ∨ p5)) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- One of the premise coincides with the conclusion.
  exact h1
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_349970735620853795366578566653 : (p4 → (((True → (p4 ∧ ((((p2 ∨ p3) ∧ (p4 ∨ p3)) ∧ ((((p4 ∨ p4) → False) ∨ ((True ∨ p5) ∧ True)) ∨ False)) → p5))) ∧ p5) ∨ p4)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_4046222760870008079754370383 : (p2 ∨ ((((((False → False) ∧ True) ∨ False) ∧ (p2 ∧ False)) ∨ (p3 ∧ p3)) ∨ (p4 ∨ (((True ∧ (p4 ∨ (p4 ∨ True))) → True) → True)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_65889388205373550905497935868 : ((p4 ∨ (True ∧ ((((True ∧ p1) → (True ∨ (p4 ∧ ((p2 ∧ (((p4 → True) ∨ (p4 ∧ p1)) ∧ p1)) → (p5 → False))))) ∧ True) → False))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_259553708721952946549041653664 : ((p1 → True) → (((p1 ∨ ((p1 ∧ (((False → (p2 ∧ (p3 ∨ p4))) ∧ (p3 ∧ p2)) → (p1 ∧ p3))) ∧ (p4 → p2))) → (p2 ∨ p4)) ∨ True)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_116971910427518734058203584845 : (((p4 ∧ p2) → ((((p3 ∧ p5) ∨ (((p4 ∧ True) ∧ (p5 ∨ p5)) ∧ (True ∧ p4))) ∨ (False ∧ (p5 ∧ (False → p4)))) ∨ p2)) ∨ (True ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



