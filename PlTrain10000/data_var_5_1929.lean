variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_138367155961202729237502625617 : ((p4 → ((p1 ∧ (((p4 → (True ∧ p4)) → p1) → (p2 ∨ (True → p5)))) ∧ (p5 ∧ (((p5 → p3) → p3) → p1)))) ∨ (p5 → (False ∨ p5))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_340833494048362932851866349871 : (p2 → (((((True ∨ ((False ∨ p2) ∧ ((p3 → p2) ∨ p4))) ∨ (p2 ∨ (p1 → p4))) → ((True → (p5 ∨ p2)) ∧ p1)) → (p1 ∨ p4)) ∨ p5)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h2
  -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
  have h3 : ((True ∨ ((False ∨ p2) ∧ ((p3 → p2) ∨ p4))) ∨ (p2 ∨ (p1 → p4))) := by
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h2, we can now drive its conclusion.
  let h4 := h2 h3
  -- We need to get the right conjuct of h4 based on <expert-advice>.
  let h5 := h4.right
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- One of the premise coincides with the conclusion.
  exact h5



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_654560959734820255062399777127 : (((((p1 ∨ (p1 ∨ (((((True → p1) → p3) → (p5 ∧ (True → ((p2 ∧ p3) ∨ p3)))) ∨ p1) ∨ (p1 → p1)))) ∨ p3) ∨ (p5 ∨ p5)) ∨ p1) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
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
  -- One of the premise coincides with the conclusion.
  exact h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_191256814398647476359125246160 : (((p3 ∧ p5) ∧ (((p2 ∨ p4) ∨ p1) ∨ (False → True))) ∨ ((p3 ∨ p2) → ((((False → (p5 ∨ (p2 → p2))) ∧ (p4 ∨ True)) ∨ p2) ∨ p4))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h2 =>
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Conjunctions on the right can always be decomposed.
    apply And.intro
    -- Implications on the right can always be decomposed.
    intro h3
    -- False on the left can always be used.
    apply False.elim h3
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro
  case inr h4 =>
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h4



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_136008536003657377023938662649 : (((p4 → (p3 → ((p5 ∧ (p3 ∨ False)) ∨ (False ∧ False)))) ∨ (((p3 ∨ ((p5 → True) ∨ p3)) ∨ False) ∨ (False ∨ p2))) ∨ (False ∧ (p1 → p2))) := by
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
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_158967414724507791466619270040 : ((p3 ∨ (((p2 → p4) → ((((p1 → (False ∨ True)) ∧ p4) ∧ ((p4 ∧ True) → p4)) ∧ p1)) ∧ False)) ∨ (p2 → ((p4 ∧ (p3 ∨ p5)) ∨ p2))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_52409162590971118310010671185 : (((((p4 ∨ p3) ∧ p2) ∨ ((((p1 ∧ (p4 ∧ p3)) → p3) ∨ True) ∧ p1)) ∧ ((False ∨ p3) → ((p3 ∧ ((p1 → p1) → p1)) ∧ p3))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_263389195719830435362998817222 : (True ∧ (((p4 ∧ (((False ∨ (p3 → p5)) ∨ ((p2 ∨ (p1 ∨ p1)) ∨ (p3 ∧ (p5 ∨ p2)))) ∨ True)) ∨ (False ∨ True)) ∨ ((False ∨ p4) ∨ p1))) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_875913392355823905553286066866 : (((((p4 → (((p1 ∨ (p1 → (p4 → (((p2 → (p3 → p1)) → p5) ∨ p4)))) ∨ p4) ∧ ((p4 → False) ∨ p4))) → p1) ∧ (p1 → False)) → p3) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
  have h4 : (p4 → (((p1 ∨ (p1 → (p4 → (((p2 → (p3 → p1)) → p5) ∨ p4)))) ∨ p4) ∧ ((p4 → False) ∨ p4))) := by
    -- Implications on the right can always be decomposed.
    intro h5
    -- Conjunctions on the right can always be decomposed.
    apply And.intro
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h5
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h5
  -- We have shown the premise of h2, we can now drive its conclusion.
  let h6 := h2 h4
  -- We want to use the implication h3 based on <expert-advice>. So we show its premise.
  have h7 : p1 := by
    -- One of the premise coincides with the conclusion.
    exact h6
  -- We have shown the premise of h3, we can now drive its conclusion.
  let h8 := h3 h7
  -- False on the left can always be used.
  apply False.elim h8
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_629887274908888213617853512045 : ((((((True ∧ (((p1 ∧ False) → (True ∧ p2)) → p3)) ∨ ((p4 → (((p1 → p4) ∧ p5) ∨ (p3 → (False ∧ p3)))) → p2)) ∨ p2) → p5) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_173087099218893547117777041326 : ((p1 ∨ ((((p4 → (p1 ∨ p5)) → p5) ∨ (False ∧ True)) ∨ (True ∨ (False ∧ p1)))) ∨ (p3 → ((False ∧ (True → ((p3 ∧ False) ∧ True))) ∨ p1))) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_40901216178766995970793243615 : (((((p2 → p3) ∨ (p2 ∧ ((p5 ∧ (True ∨ p3)) → (False ∧ (((p3 ∧ p3) ∧ ((True ∧ p1) ∨ False)) ∧ False))))) ∧ (False → True)) ∨ True) ∨ False) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_181461138119738896329785342461 : ((p4 ∨ ((((True ∨ p3) → (p1 ∨ p1)) ∧ (p3 → (p4 → p2))) ∨ p1)) → ((False ∨ (((p1 → p4) → ((p1 ∧ False) ∨ p5)) → p5)) ∨ True)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h2 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro
  case inr h3 =>
    -- Disjunctions on the left can always be decomposed.
    cases h3
    case inl h4 =>
      -- Conjunctions on the left can always be decomposed.
      let h5 := h4.left
      let h6 := h4.right
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- True on the right can always be proven directly.
      apply True.intro
    case inr h7 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- True on the right can always be proven directly.
      apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_38839341537882760360586238824 : (((((p3 → p5) ∧ True) ∧ ((p4 → ((p1 ∧ (False ∨ p5)) ∧ ((p2 → p2) → p2))) → (((p2 ∧ p2) → (p3 ∧ False)) ∧ False))) ∧ False) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_57304587428015970646986923037 : ((((p5 → p3) → p3) ∨ (((p2 → (p5 → p3)) ∨ ((((p1 ∨ (p4 ∧ p1)) ∨ (p2 ∧ False)) ∨ p2) → ((p5 ∨ p4) ∨ p5))) ∨ p1)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_252648831656218907579498452552 : ((p5 → p4) ∨ ((((p5 → p3) → p2) → ((p4 ∧ (((False ∨ (p1 → p2)) ∨ p1) ∧ (p3 ∨ p3))) ∨ p1)) → ((p4 ∨ p5) → (p4 → p4)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Implications on the right can always be decomposed.
  intro h3
  -- Disjunctions on the left can always be decomposed.
  cases h2
  case inl h4 =>
    -- One of the premise coincides with the conclusion.
    exact h4
  case inr h5 =>
    -- One of the premise coincides with the conclusion.
    exact h3



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_476634531429536088304947056498 : (((((p2 → p3) → ((((p2 ∨ p5) ∨ False) ∨ True) ∧ p2)) ∨ (((True ∨ p1) → p5) → (p4 → (p4 → (((p5 → p3) → p5) ∨ False))))) ∧ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Implications on the right can always be decomposed.
  intro h3
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h4
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h5 : (True ∨ p1) := by
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h6 := h1 h5
  -- One of the premise coincides with the conclusion.
  exact h6
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_158336896662797076860107579097 : (((p1 ∧ p5) ∧ (((p1 → (((True → p1) ∧ ((True → p4) ∨ (p5 ∧ p4))) → p2)) ∨ True) ∨ p2)) ∨ (((p4 → p4) ∧ p5) ∨ (p3 → p3))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_803063801489772816468967201311 : (((p3 → (((True ∧ p3) ∧ (p1 ∧ (((((p3 ∨ p2) → ((p1 ∨ ((p2 → True) ∨ False)) → False)) ∨ (p2 ∧ p3)) ∧ p5) ∨ p5))) ∧ False)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_154746830813209189383018278651 : ((((((p4 ∧ p2) ∨ p3) → p1) → ((True ∨ (p2 → (p3 ∨ (p2 ∧ p3)))) → False)) ∨ (p3 → True)) ∧ ((((p1 ∧ p1) ∨ True) ∧ True) ∨ p2)) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_92313257984952216082077788516 : (((True ∨ p3) → ((p4 → ((((True → (False ∧ False)) ∨ (p3 ∧ True)) ∨ (((p1 ∨ (p2 ∨ (p2 → p2))) ∨ p2) ∧ p2)) ∨ False)) ∧ p4)) → p4) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h2 : (True ∨ p3) := by
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
theorem thm_5_vars_300694014113779537407782485344 : (False ∨ ((p3 ∨ ((p3 ∧ (True → (p3 ∨ p5))) ∨ ((((False → p4) ∨ p4) ∨ True) → (p4 → p4)))) ∨ ((p5 ∨ (True → p1)) ∨ (p2 ∧ p1)))) := by
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
  -- Implications on the right can always be decomposed.
  intro h2
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h3 =>
    -- Disjunctions on the left can always be decomposed.
    cases h3
    case inl h4 =>
      -- One of the premise coincides with the conclusion.
      exact h2
    case inr h5 =>
      -- One of the premise coincides with the conclusion.
      exact h5
  case inr h6 =>
    -- One of the premise coincides with the conclusion.
    exact h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_184417427290269079513233286520 : (((((p4 ∨ p3) → ((p2 ∨ False) → p2)) → p5) ∧ (p1 ∧ True)) ∨ ((p3 → ((p1 → p3) ∨ (True → ((p1 ∧ p2) ∧ (p1 ∧ p4))))) → True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_258905125066272269462635587868 : ((True → p2) → ((False ∧ (p3 ∨ ((False → ((False ∨ ((p2 ∨ True) ∨ (p2 → p2))) ∧ p5)) → False))) ∨ ((False → p3) ∧ ((p5 → p3) → p2)))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h2
  -- False on the left can always be used.
  apply False.elim h2
  -- Implications on the right can always be decomposed.
  intro h3
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h4 : True := by
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h5 := h1 h4
  -- One of the premise coincides with the conclusion.
  exact h5



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_147210177508088465951929651805 : (((p2 → ((((p3 → False) ∨ (((((p2 ∧ (p2 → p4)) → p5) → p3) ∧ True) ∧ True)) ∨ p1) ∧ False)) ∧ p1) ∨ ((p2 ∨ False) ∨ (p5 ∨ True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_44155110382349488030850813143 : (((((p5 → ((False ∧ ((p3 ∨ True) → ((p3 ∨ (p1 ∧ p3)) ∨ (p5 → p5)))) ∨ (p1 ∧ False))) → p5) → (p4 ∧ (p1 ∧ p4))) → p1) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_788319442547509364836630959568 : (((p5 ∨ ((((((p1 ∨ p3) ∨ False) ∨ ((p1 → (p3 ∧ ((True ∧ p1) ∧ True))) ∨ (p3 ∨ p4))) ∨ ((p5 → p3) ∨ False)) ∨ p2) ∨ p1)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_218809169351578763912016916534 : ((p1 ∧ (p5 ∨ (p5 ∨ p1))) → (((((p4 ∨ p4) ∧ p1) ∧ p5) ∨ False) ∨ (((p4 ∨ (True ∨ (p2 ∧ ((False ∧ p1) → False)))) → p5) → p1))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- Disjunctions on the left can always be decomposed.
  cases h3
  case inl h4 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h5
    -- One of the premise coincides with the conclusion.
    exact h2
  case inr h6 =>
    -- Disjunctions on the left can always be decomposed.
    cases h6
    case inl h7 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Implications on the right can always be decomposed.
      intro h8
      -- One of the premise coincides with the conclusion.
      exact h2
    case inr h9 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Implications on the right can always be decomposed.
      intro h10
      -- One of the premise coincides with the conclusion.
      exact h9



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_314249404677949143738791948438 : (p3 ∨ (((p5 ∨ (((p1 → p4) ∨ (False ∨ (p1 ∧ ((p2 ∧ p1) ∧ True)))) ∧ p2)) ∨ ((True ∨ p1) ∧ (p4 ∧ False))) ∨ (True ∨ (p2 → p1)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_701963215912911231650277632033 : ((((p3 ∨ (p2 ∧ ((True ∧ (p2 ∧ True)) ∧ (p2 ∧ p5)))) ∧ (p1 → (((p1 ∨ (p3 → (False ∨ False))) → (p3 ∧ (p5 ∧ p4))) → p4))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_133873832393399441353318357457 : (((p4 ∧ (((p4 ∨ ((False ∧ (((p5 ∧ (p5 → p4)) ∨ p4) → (True → (p1 ∧ p2)))) ∧ p1)) ∧ p5) ∨ p1)) ∧ p3) ∨ ((False → p4) ∨ p1)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_201778183531977288581098966135 : (((((p5 ∧ p3) ∨ True) → p5) ∨ True) ∧ ((p4 ∧ ((((p3 → (((p3 ∨ False) → p2) ∨ (p3 ∧ p4))) ∧ (p2 ∧ p1)) ∧ True) ∨ False)) ∨ True)) := by
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
theorem thm_5_vars_56847068133783683810512123938 : (((True ∧ (True ∨ p4)) ∧ (p2 ∨ (((p5 ∧ p1) → (p4 ∧ ((((p3 ∧ p1) ∧ False) ∨ (p1 ∧ (p3 ∨ True))) ∧ (p1 ∧ p5)))) ∨ True))) ∨ p5) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_622747855096643273409142157637 : ((((p4 ∧ (p2 ∧ ((((p1 ∨ (False ∨ p5)) ∧ (True ∨ (True → p1))) → (((False ∧ p1) ∨ p3) → p2)) → ((True ∨ p2) ∧ p5)))) ∨ True) ∨ False) ∧ True) := by
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
theorem thm_5_vars_312414005831947712137693009723 : (p2 ∨ (p4 → ((False ∨ ((p2 → (p4 ∨ p1)) ∧ ((p2 ∧ ((p4 → ((p4 → (p3 ∧ p4)) ∨ p2)) ∧ (True → (p5 ∨ True)))) ∨ p4))) ∨ p2))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h2
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- One of the premise coincides with the conclusion.
  exact h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_690580722289058563498735251059 : (((((((p5 → p3) → ((True → (p2 → p2)) ∧ ((p5 ∧ False) → True))) ∨ p4) ∨ True) → ((p2 ∨ (True → ((False ∧ False) ∨ p2))) ∨ True)) ∨ p4) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
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
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_247973589062624295627775770502 : ((p1 ∨ p4) ∨ (((((p1 → p1) ∧ (p1 ∨ ((p1 ∨ p2) → (p4 ∨ p3)))) ∨ p4) → (p4 → False)) ∨ (False → (((p4 ∨ p1) ∧ p1) → p1)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Conjunctions on the left can always be decomposed.
  let h3 := h2.left
  let h4 := h2.right
  -- Disjunctions on the left can always be decomposed.
  cases h3
  case inl h5 =>
    -- False on the left can always be used.
    apply False.elim h1
  case inr h6 =>
    -- False on the left can always be used.
    apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_346617310767465875326085503718 : (p3 → (((((p4 → p1) ∨ p1) → (p4 ∨ True)) ∧ (((((False ∧ (True → (True ∨ p1))) ∧ p2) → p5) → p1) ∨ False)) ∨ (False → (p3 ∧ p5)))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h2
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- False on the left can always be used.
  apply False.elim h2
  -- False on the left can always be used.
  apply False.elim h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_157005525857857196209694287085 : (((((p4 → True) → p4) ∧ (False → (((p5 → False) → (p2 ∨ (True ∨ (p5 ∨ p5)))) → p3))) ∨ p2) ∨ ((p4 ∨ p4) ∨ ((True ∧ p4) → p4))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- One of the premise coincides with the conclusion.
  exact h3



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_654069970887616049129810497855 : (((((p1 → (((p5 → False) → p3) ∧ ((p3 ∧ ((((p5 → True) ∧ p3) ∧ p2) ∨ p4)) ∨ ((False ∨ p5) ∧ p2)))) ∧ False) ∨ (False → p4)) ∨ p3) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- False on the left can always be used.
  apply False.elim h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_299254753660428039871380666270 : (False ∨ (((p2 ∨ ((p1 ∨ ((True ∧ ((p3 ∨ p2) ∨ (p3 ∧ p1))) → True)) → ((True ∧ p5) ∧ True))) ∧ ((p4 ∨ (True ∧ False)) ∧ False)) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_52518917057098637832740799842 : ((((p1 → (((p4 ∨ (p4 ∧ p3)) → (p5 ∨ (p3 ∨ p3))) → p3)) ∧ p3) ∨ (((p5 ∨ (True ∨ p2)) ∨ False) ∨ (p2 ∨ (p1 → p3)))) ∨ p4) := by
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
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_314935959745224468453591593791 : (p3 ∨ ((p2 ∨ (p5 ∨ (((p3 ∨ p2) → True) → (p5 ∨ False)))) ∨ ((p4 → True) ∧ (True ∨ ((((True → False) → p2) ∨ (p4 ∨ p2)) → True))))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_178331591756907607941538092063 : ((((p4 ∨ (p2 → (p1 → False))) ∨ ((p5 → p3) → p5)) ∨ (False ∨ True)) ∨ ((p5 ∧ ((((p2 ∨ (p5 → p2)) ∨ False) → p3) ∨ False)) → p5)) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_115440123442830781253771880359 : ((((p3 → ((p3 ∧ False) → p1)) ∧ (p5 → p3)) ∨ (((p5 ∧ (p1 ∧ p4)) ∧ (((p5 ∧ p1) → p2) ∧ False)) ∨ (p2 ∨ p5))) ∨ (p3 → p3)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_253073148265115822216570565210 : ((True ∧ p4) → (((True → (p1 → (((p2 ∨ p2) → p3) ∨ (p2 ∨ ((p5 ∨ p4) → True))))) → (p5 ∧ p1)) ∨ ((False → False) ∨ (p3 ∨ p5)))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h4
  -- False on the left can always be used.
  apply False.elim h4



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_198069251498388448658261455855 : (((p1 ∨ p1) ∨ ((p1 → (p2 ∨ p3)) ∧ p5)) ∨ ((((p5 ∧ (((p1 ∧ p1) ∨ p5) ∨ p5)) ∧ (p5 ∧ p5)) ∧ ((False ∧ True) → p4)) → p5)) := by
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
  -- Conjunctions on the left can always be decomposed.
  let h6 := h4.left
  let h7 := h4.right
  -- Disjunctions on the left can always be decomposed.
  cases h7
  case inl h8 =>
    -- Disjunctions on the left can always be decomposed.
    cases h8
    case inl h9 =>
      -- Conjunctions on the left can always be decomposed.
      let h10 := h9.left
      let h11 := h9.right
      -- Conjunctions on the left can always be decomposed.
      let h12 := h5.left
      let h13 := h5.right
      -- One of the premise coincides with the conclusion.
      exact h13
    case inr h14 =>
      -- Conjunctions on the left can always be decomposed.
      let h15 := h5.left
      let h16 := h5.right
      -- One of the premise coincides with the conclusion.
      exact h16
  case inr h17 =>
    -- Conjunctions on the left can always be decomposed.
    let h18 := h5.left
    let h19 := h5.right
    -- One of the premise coincides with the conclusion.
    exact h19



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_172064651144850077502972016262 : (((((True ∨ (p4 → False)) ∧ (True ∧ (p2 ∧ (p5 ∨ False)))) → p5) → (p4 ∧ p5)) ∨ (((p4 ∧ (p2 ∧ (False ∨ (False ∧ True)))) → p2) ∧ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
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
  -- Disjunctions on the left can always be decomposed.
  cases h5
  case inl h6 =>
    -- False on the left can always be used.
    apply False.elim h6
  case inr h7 =>
    -- Conjunctions on the left can always be decomposed.
    let h8 := h7.left
    let h9 := h7.right
    -- False on the left can always be used.
    apply False.elim h8
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_135910541393835778148149660365 : (((((False ∧ (p1 ∧ p2)) ∨ p5) ∧ (p2 → (p1 → (p1 → p2)))) → ((p4 ∨ (p2 → p3)) → ((p5 → False) ∨ True))) ∨ ((p3 ∧ p3) → p2)) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Disjunctions on the left can always be decomposed.
  cases h2
  case inl h3 =>
    -- Conjunctions on the left can always be decomposed.
    let h4 := h1.left
    let h5 := h1.right
    -- Disjunctions on the left can always be decomposed.
    cases h4
    case inl h6 =>
      -- Conjunctions on the left can always be decomposed.
      let h7 := h6.left
      let h8 := h6.right
      -- False on the left can always be used.
      apply False.elim h7
    case inr h9 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- True on the right can always be proven directly.
      apply True.intro
  case inr h10 =>
    -- Conjunctions on the left can always be decomposed.
    let h11 := h1.left
    let h12 := h1.right
    -- Disjunctions on the left can always be decomposed.
    cases h11
    case inl h13 =>
      -- Conjunctions on the left can always be decomposed.
      let h14 := h13.left
      let h15 := h13.right
      -- False on the left can always be used.
      apply False.elim h14
    case inr h16 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- True on the right can always be proven directly.
      apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_111588483358371015364461489102 : ((((p2 ∨ (((((((p2 ∧ p5) → True) ∨ p4) → False) ∨ p5) ∨ ((p1 → p2) ∧ (p5 → p2))) ∧ (False ∨ p5))) ∧ p3) ∨ True) ∨ (False ∨ True)) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_150922017872905172472061029498 : ((((False → p5) ∨ (((((False → p1) ∨ p3) ∨ (True ∨ p2)) → ((p4 → True) ∨ True)) ∧ (p4 → p4))) ∨ p4) → (((p4 → p3) → p5) ∨ True)) := by
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
      -- Conjunctions on the left can always be decomposed.
      let h5 := h4.left
      let h6 := h4.right
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- True on the right can always be proven directly.
      apply True.intro
  case inr h7 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_205614619754898978089953633524 : (((False ∧ p1) ∨ (p1 ∨ (p4 ∧ p2))) ∨ ((p4 → (p2 ∨ p1)) ∨ (True ∨ (((p4 ∨ (p5 ∨ True)) ∧ (p2 ∧ ((True → False) → p1))) ∧ True)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_131275966843143092769757566338 : ((((p4 ∧ False) ∧ ((p3 → p1) ∧ p1)) ∨ ((((p5 ∧ ((p2 ∧ False) ∧ ((p4 ∨ p4) ∧ p2))) ∧ p5) ∨ True) ∨ False)) ∧ (False → (False ∧ p2))) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- False on the left can always be used.
  apply False.elim h1
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_54551321135649912206951756563 : (((p1 ∧ ((p3 ∨ (p5 ∨ p2)) ∨ (p3 ∨ False))) ∨ ((((p5 → (p2 → p2)) ∨ ((p1 ∨ (p3 ∧ (p2 ∨ False))) → p1)) ∨ True) ∨ p4)) ∨ p5) := by
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



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_218352505473129576722079900473 : (((p2 → p2) ∨ (p4 ∨ p2)) → ((((p2 ∨ (((True ∨ ((p1 → True) → p5)) ∨ (p3 ∨ p4)) ∧ p5)) ∨ p5) ∧ (p1 ∧ True)) ∨ (False → p3))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h2 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h3
    -- False on the left can always be used.
    apply False.elim h3
  case inr h4 =>
    -- Disjunctions on the left can always be decomposed.
    cases h4
    case inl h5 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Implications on the right can always be decomposed.
      intro h6
      -- False on the left can always be used.
      apply False.elim h6
    case inr h7 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Implications on the right can always be decomposed.
      intro h8
      -- False on the left can always be used.
      apply False.elim h8



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_62402821997793905061890609986 : ((p3 ∧ ((((p4 ∨ (p3 → False)) ∧ (p1 ∧ p4)) → p3) ∧ ((p3 ∨ False) ∧ ((p2 → True) → ((p4 → True) → (p5 ∨ (p1 ∨ p5))))))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_111720096677179358545804622392 : ((((((False ∨ p1) → (p1 ∧ p4)) ∧ (((((p5 ∧ p2) → p4) ∧ p1) ∨ p5) ∨ (p4 ∧ ((p1 ∨ p5) ∨ p5)))) → p3) ∨ p2) ∨ (True ∨ p4)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_232727821550972958365286106768 : ((p1 ∧ (True → p2)) → (((True ∨ p3) → (p5 ∧ p1)) → (((p1 ∨ ((((True ∨ p5) → p2) → (p5 → (p2 ∨ p1))) → True)) → False) ∨ p1))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Conjunctions on the left can always be decomposed.
  let h3 := h1.left
  let h4 := h1.right
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h3



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_653979489386329660447275209492 : (((((p3 ∧ ((((p5 ∨ (p1 ∧ (p2 → p3))) ∨ (p5 → p4)) ∨ (((p5 ∨ False) → p3) ∨ (True → p4))) ∨ p5)) ∧ True) ∨ (False → p5)) ∨ False) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- False on the left can always be used.
  apply False.elim h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_80830236380421391569435585816 : (((((p4 ∨ ((p3 ∨ True) ∨ (True → ((((p2 ∨ (p2 ∨ p1)) → p1) ∨ False) ∨ p5)))) → (p1 ∧ p4)) ∧ True) ∧ ((p4 → p1) ∨ p2)) → p1) := by
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
    have h7 : (p4 ∨ ((p3 ∨ True) ∨ (True → ((((p2 ∨ (p2 ∨ p1)) → p1) ∨ False) ∨ p5)))) := by
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- True on the right can always be proven directly.
      apply True.intro
    -- We have shown the premise of h4, we can now drive its conclusion.
    let h8 := h4 h7
    -- We need to get the left conjuct of h8 based on <expert-advice>.
    let h9 := h8.left
    -- One of the premise coincides with the conclusion.
    exact h9
  case inr h10 =>
    -- We want to use the implication h4 based on <expert-advice>. So we show its premise.
    have h11 : (p4 ∨ ((p3 ∨ True) ∨ (True → ((((p2 ∨ (p2 ∨ p1)) → p1) ∨ False) ∨ p5)))) := by
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- True on the right can always be proven directly.
      apply True.intro
    -- We have shown the premise of h4, we can now drive its conclusion.
    let h12 := h4 h11
    -- We need to get the left conjuct of h12 based on <expert-advice>.
    let h13 := h12.left
    -- One of the premise coincides with the conclusion.
    exact h13



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_164811390383260693253048026199 : ((((p2 ∨ p1) ∧ ((((p5 → (((p2 → p3) ∧ p5) ∧ p1)) ∧ True) ∧ p4) → p2)) ∨ False) ∨ (True ∨ (p2 → ((p5 ∧ (p5 ∨ p3)) → p4)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_62861601066102677848522744161 : ((p4 ∧ (((p1 → False) ∧ p4) ∧ ((((p5 ∨ p1) ∧ ((p3 ∧ (False → (p2 ∨ (p2 → p2)))) ∨ p1)) → ((p2 ∨ False) → p4)) ∨ p3))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_774525653242357465534281431613 : (((False ∨ ((True ∧ (p2 → ((False ∨ ((True ∧ p3) → (p2 ∧ p5))) ∧ (False ∨ False)))) ∨ (((False ∧ ((p5 ∨ True) ∧ p1)) ∧ p3) ∨ True))) ∨ p3) ∧ True) := by
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
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_52636916396345826014772144888 : ((((p3 ∨ False) ∨ (((p4 ∨ p4) ∨ p3) ∨ (False ∨ ((p1 ∨ False) ∨ p4)))) ∨ (((p3 ∨ (p5 ∧ (p3 ∧ p1))) → p1) → (True ∨ p3))) ∨ p2) := by
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



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_790680844345376124216856290301 : (((p5 ∨ (p5 ∨ ((True ∧ ((p3 ∧ (p3 ∧ (p3 → p3))) ∨ (((p2 ∧ (False ∧ p1)) → False) ∨ ((False ∨ False) ∨ False)))) ∧ (p3 ∨ True)))) ∨ p3) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- Conjunctions on the left can always be decomposed.
  let h4 := h3.left
  let h5 := h3.right
  -- False on the left can always be used.
  apply False.elim h4
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_659819443980273642341092835137 : (((((p3 ∨ ((((p1 → (p5 → False)) → p4) → p1) → ((((p1 → p2) → False) ∧ False) ∧ ((p1 ∨ True) ∧ p4)))) ∧ p3) → (p2 ∨ p1)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_116024479738400430943725516238 : (((p1 ∧ (p5 → (p5 → p3))) → ((((p3 → True) → (p2 ∨ p5)) ∧ (p2 ∧ p2)) ∧ ((False → p2) → (False ∧ (p2 → p1))))) ∨ (p1 → p1)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_635243008337994679267761419450 : (((((False → ((p1 → (p1 ∨ (((p4 → ((False ∧ (p3 → p5)) ∨ True)) → (p2 → p4)) ∧ False))) ∧ p1)) → (True ∨ (p2 → p5))) → p4) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_788903494944395059420498339592 : (((p5 ∨ ((p4 ∨ (p1 ∨ ((p1 ∨ p2) ∧ ((((True ∨ (p1 ∨ p2)) ∨ ((True ∨ False) → False)) ∨ (p1 ∧ False)) ∧ p5)))) ∧ (True → p1))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_351642094981891606470981246900 : (p4 → (((True ∨ (p2 ∧ p1)) → ((((True → True) ∧ False) ∧ (p1 ∨ (False ∨ p2))) ∧ False)) ∨ (((False → (p2 ∨ False)) ∨ (p2 ∧ p1)) → True))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h2
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_67872534300166449260543364697 : ((p2 → (((p5 ∨ ((p4 ∧ (False ∧ (p4 → (((p5 ∨ p1) → (p1 → p2)) → p1)))) → True)) ∨ (True ∧ p1)) → ((p4 → p1) ∨ True))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_124393727361756599383145999581 : (((p5 ∧ ((True ∨ ((p5 ∨ p2) ∧ p2)) ∨ True)) ∨ ((p2 → (((p4 ∨ ((False ∧ True) ∨ p2)) ∧ (False ∨ False)) → p4)) ∨ p3)) → (p1 ∨ True)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h2 =>
    -- Conjunctions on the left can always be decomposed.
    let h3 := h2.left
    let h4 := h2.right
    -- Disjunctions on the left can always be decomposed.
    cases h4
    case inl h5 =>
      -- Disjunctions on the left can always be decomposed.
      cases h5
      case inl h6 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- True on the right can always be proven directly.
        apply True.intro
      case inr h7 =>
        -- Conjunctions on the left can always be decomposed.
        let h8 := h7.left
        let h9 := h7.right
        -- Disjunctions on the left can always be decomposed.
        cases h8
        case inl h10 =>
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- True on the right can always be proven directly.
          apply True.intro
        case inr h11 =>
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- True on the right can always be proven directly.
          apply True.intro
    case inr h12 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- True on the right can always be proven directly.
      apply True.intro
  case inr h13 =>
    -- Disjunctions on the left can always be decomposed.
    cases h13
    case inl h14 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- True on the right can always be proven directly.
      apply True.intro
    case inr h15 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- True on the right can always be proven directly.
      apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_207255972085312827489661621802 : ((((True → (p3 ∧ p4)) ∨ p5) ∨ p5) → ((((p2 ∨ ((p1 ∧ ((p3 ∨ p4) → ((p2 ∧ p1) → p5))) → p3)) ∨ False) → p2) ∨ (False → False))) := by
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
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Implications on the right can always be decomposed.
      intro h6
      -- False on the left can always be used.
      apply False.elim h6
  case inr h7 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h8
    -- False on the left can always be used.
    apply False.elim h8



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_49150138171088564787567049503 : ((((False ∧ ((p5 → (p1 ∨ (p5 ∧ p5))) ∧ p3)) ∧ ((((p2 ∨ (p3 ∧ p1)) ∨ p2) ∨ (p2 ∧ True)) ∨ p5)) ∨ (True ∧ (p3 → p3))) ∨ p3) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- Implications on the right can always be decomposed.
  intro h1
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_159236834463961533763209008512 : ((p3 → ((p2 ∨ (p3 → ((True → ((p4 → p5) ∧ ((True → False) → p3))) → (p5 ∨ p5)))) → p4)) ∨ (False → (p1 ∨ (p5 ∨ (p2 ∨ p4))))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_204264898021640103358162754234 : ((((p2 ∨ p1) ∨ (p4 ∧ p1)) ∧ p1) ∨ (p2 ∨ (p2 ∨ ((p2 ∧ False) → (p4 ∧ (((((True ∨ (p4 ∧ p1)) → p1) ∧ p5) ∧ p4) ∨ p1)))))) := by
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
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- False on the left can always be used.
  apply False.elim h3
  -- Conjunctions on the left can always be decomposed.
  let h4 := h1.left
  let h5 := h1.right
  -- False on the left can always be used.
  apply False.elim h5



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_172060346800182718322814431902 : ((((p3 ∨ ((p1 ∧ ((True ∧ p1) ∨ (True ∧ p4))) ∨ p1)) ∨ p3) → (p2 ∧ False)) ∨ ((True ∨ (p2 ∨ False)) ∨ ((p1 → False) ∨ (False → True)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_87837723687281306214916015102 : (((((p2 → p4) ∧ p1) ∨ (p5 → True)) → (p3 ∧ ((True → (((True ∨ p3) ∧ ((p5 ∧ ((p5 → p4) → p2)) ∧ True)) → p3)) ∧ p1))) → p1) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h2 : (((p2 → p4) ∧ p1) ∨ (p5 → True)) := by
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h3
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h4 := h1 h2
  -- We need to get the right conjuct of h4 based on <expert-advice>.
  let h5 := h4.right
  -- We need to get the right conjuct of h5 based on <expert-advice>.
  let h6 := h5.right
  -- One of the premise coincides with the conclusion.
  exact h6



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_38119504056273702707777853497 : ((((((False ∨ ((p5 ∧ p4) ∨ p1)) → ((((p3 ∨ (p1 ∧ True)) ∧ p1) ∨ p2) ∨ p3)) → (p4 ∨ False)) ∧ ((p3 → p5) ∨ p3)) ∧ True) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_324529671482237486965279807426 : (p5 ∨ (((p3 ∧ (p3 → False)) ∨ False) → (((((p1 ∨ ((p2 ∨ True) ∨ False)) → p1) ∨ ((False ∧ p2) ∧ ((False ∧ p1) ∨ p1))) ∧ False) ∧ p2))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h2 =>
    -- Conjunctions on the left can always be decomposed.
    let h3 := h2.left
    let h4 := h2.right
    -- We want to use the implication h4 based on <expert-advice>. So we show its premise.
    have h5 : p3 := by
      -- One of the premise coincides with the conclusion.
      exact h3
    -- We have shown the premise of h4, we can now drive its conclusion.
    let h6 := h4 h5
    -- False on the left can always be used.
    apply False.elim h6
  case inr h7 =>
    -- False on the left can always be used.
    apply False.elim h7
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h8 =>
    -- Conjunctions on the left can always be decomposed.
    let h9 := h8.left
    let h10 := h8.right
    -- We want to use the implication h10 based on <expert-advice>. So we show its premise.
    have h11 : p3 := by
      -- One of the premise coincides with the conclusion.
      exact h9
    -- We have shown the premise of h10, we can now drive its conclusion.
    let h12 := h10 h11
    -- False on the left can always be used.
    apply False.elim h12
  case inr h13 =>
    -- False on the left can always be used.
    apply False.elim h13
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h14 =>
    -- Conjunctions on the left can always be decomposed.
    let h15 := h14.left
    let h16 := h14.right
    -- We want to use the implication h16 based on <expert-advice>. So we show its premise.
    have h17 : p3 := by
      -- One of the premise coincides with the conclusion.
      exact h15
    -- We have shown the premise of h16, we can now drive its conclusion.
    let h18 := h16 h17
    -- False on the left can always be used.
    apply False.elim h18
  case inr h19 =>
    -- False on the left can always be used.
    apply False.elim h19



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_670118522850988490687877392679 : ((((((p3 ∧ ((p1 ∨ p3) ∧ p5)) ∨ p5) ∨ (p1 → (((True ∧ ((p4 ∧ p2) ∧ p4)) ∧ (True ∧ p2)) → p4))) ∨ ((p4 ∧ p3) → p3)) ∨ p3) ∧ True) := by
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
  -- One of the premise coincides with the conclusion.
  exact h3
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_300216253461364733687805938696 : (False ∨ (((p4 ∧ ((((True → p5) ∨ ((True ∨ p5) ∧ (True ∧ False))) ∧ True) ∧ (p2 ∨ True))) ∧ (True ∨ (p4 → (True → False)))) → (False ∨ p4))) := by
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
  -- Conjunctions on the left can always be decomposed.
  let h6 := h5.left
  let h7 := h5.right
  -- Conjunctions on the left can always be decomposed.
  let h8 := h6.left
  let h9 := h6.right
  -- Disjunctions on the left can always be decomposed.
  cases h8
  case inl h10 =>
    -- Disjunctions on the left can always be decomposed.
    cases h7
    case inl h11 =>
      -- Disjunctions on the left can always be decomposed.
      cases h3
      case inl h12 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- One of the premise coincides with the conclusion.
        exact h4
      case inr h13 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- One of the premise coincides with the conclusion.
        exact h4
    case inr h14 =>
      -- Disjunctions on the left can always be decomposed.
      cases h3
      case inl h15 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- One of the premise coincides with the conclusion.
        exact h4
      case inr h16 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- One of the premise coincides with the conclusion.
        exact h4
  case inr h17 =>
    -- Conjunctions on the left can always be decomposed.
    let h18 := h17.left
    let h19 := h17.right
    -- Disjunctions on the left can always be decomposed.
    cases h18
    case inl h20 =>
      -- Conjunctions on the left can always be decomposed.
      let h21 := h19.left
      let h22 := h19.right
      -- False on the left can always be used.
      apply False.elim h22
    case inr h23 =>
      -- Conjunctions on the left can always be decomposed.
      let h24 := h19.left
      let h25 := h19.right
      -- False on the left can always be used.
      apply False.elim h25



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_198202718436583113392135044741 : (((p3 → p1) → ((p5 ∧ (False ∧ p5)) ∧ p5)) ∨ (True ∨ (p2 → (False ∧ (p2 ∧ ((((p5 → p3) → p2) ∨ p5) → ((p1 → p1) ∧ True))))))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_340534001765038480970437497270 : (p2 → ((((False → p2) → False) → (p5 ∧ ((p3 ∨ ((p2 → (((p2 ∧ (p1 → (p2 ∧ p5))) ∨ False) → p1)) ∨ p3)) ∨ (True → p2)))) ∧ p2)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h2
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
  have h3 : (False → p2) := by
    -- Implications on the right can always be decomposed.
    intro h4
    -- False on the left can always be used.
    apply False.elim h4
  -- We have shown the premise of h2, we can now drive its conclusion.
  let h5 := h2 h3
  -- False on the left can always be used.
  apply False.elim h5
  -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
  have h6 : (False → p2) := by
    -- Implications on the right can always be decomposed.
    intro h7
    -- False on the left can always be used.
    apply False.elim h7
  -- We have shown the premise of h2, we can now drive its conclusion.
  let h8 := h2 h6
  -- False on the left can always be used.
  apply False.elim h8
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_60737396259202428585518346368 : ((True ∧ (((False ∧ False) → p3) ∧ ((p4 ∨ ((False ∨ False) → ((p5 → (True → ((p3 ∧ False) ∨ p5))) → p2))) → ((p1 ∨ p4) ∧ p4)))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_326371451622390006644969174758 : (p5 ∨ (p5 → ((p3 ∧ (p3 ∧ p2)) ∨ (((((False ∧ (False → True)) ∨ True) ∨ ((p5 ∧ True) → p3)) ∨ ((p3 ∧ (p4 → p5)) ∨ p1)) ∧ p5)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_349285578127048896711540145841 : (p3 → (p2 → (((p1 → ((((p4 ∧ (p3 → (p5 ∨ ((p4 → p3) ∧ p5)))) → (False ∧ False)) ∧ p3) ∧ p4)) ∨ (p1 ∨ p4)) ∨ (True ∧ p3)))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_185740608559490246486257488348 : ((p3 → ((p5 → (p3 ∧ (p5 ∧ p2))) → (p5 ∧ (True ∧ False)))) ∨ ((True ∨ (((p4 ∨ True) ∨ p5) → False)) ∨ (False ∨ ((p4 ∧ p3) → p4)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_111018998991230969383070266423 : (((((((((p3 ∨ p4) → p1) ∨ (p5 ∧ p2)) → (p3 ∨ ((False → p5) ∨ False))) ∨ p5) ∨ True) → ((False ∨ p4) ∧ p3)) ∧ p1) ∨ (True ∧ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_356924913972453993577921125480 : (p5 → ((p2 → (p2 → (p3 ∨ False))) → (((p5 → ((False ∨ True) ∧ (((False ∨ p5) ∨ False) → (p3 ∨ False)))) ∨ (False ∧ (True ∨ True))) → p3))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Implications on the right can always be decomposed.
  intro h3
  -- Disjunctions on the left can always be decomposed.
  cases h3
  case inl h4 =>
    -- We want to use the implication h4 based on <expert-advice>. So we show its premise.
    have h5 : p5 := by
      -- One of the premise coincides with the conclusion.
      exact h1
    -- We have shown the premise of h4, we can now drive its conclusion.
    let h6 := h4 h5
    -- We need to get the right conjuct of h6 based on <expert-advice>.
    let h7 := h6.right
    -- We want to use the implication h7 based on <expert-advice>. So we show its premise.
    have h8 : ((False ∨ p5) ∨ False) := by
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- One of the premise coincides with the conclusion.
      exact h1
    -- We have shown the premise of h7, we can now drive its conclusion.
    let h9 := h7 h8
    -- Disjunctions on the left can always be decomposed.
    cases h9
    case inl h10 =>
      -- One of the premise coincides with the conclusion.
      exact h10
    case inr h11 =>
      -- False on the left can always be used.
      apply False.elim h11
  case inr h12 =>
    -- Conjunctions on the left can always be decomposed.
    let h13 := h12.left
    let h14 := h12.right
    -- False on the left can always be used.
    apply False.elim h13



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_185016025023576147286260561445 : (((p1 ∨ p4) ∧ ((p2 → (p5 ∨ (True ∨ (p1 → False)))) ∧ p4)) ∨ (((((p4 ∨ False) ∨ (p5 → False)) → False) ∨ (p2 ∨ (p2 ∧ p5))) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_137981107270685610731155271727 : ((p5 ∨ ((True ∧ (p2 → False)) ∨ ((p5 ∨ (p3 ∨ (p2 → p5))) ∧ (((p1 ∧ p2) ∧ (p3 ∨ (p1 ∧ p4))) ∨ False)))) ∨ ((True → p2) → True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_216330860362160470656731415456 : ((p2 → (True → (p4 ∨ False))) ∨ (((True → ((((p3 ∨ p1) → (True ∨ (True ∧ p3))) → False) ∧ p5)) ∨ (False → (True ∨ p1))) ∨ (p2 → True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_136055417923214995342288475352 : ((((p1 ∧ ((p1 ∧ (True ∧ p5)) → p1)) ∨ p4) ∧ (p1 ∨ (((p2 ∨ (p4 ∨ p4)) → p1) ∧ (p3 ∧ (p3 → p2))))) ∨ ((p3 → p4) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_173865556969794336551558533587 : ((((((p2 → p3) → (True ∧ p3)) → ((True ∧ (p5 → p5)) ∨ p3)) ∧ True) → False) → ((p1 ∧ (((p4 → p2) → (p2 → p3)) ∧ False)) ∨ False)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h2 : ((((p2 → p3) → (True ∧ p3)) → ((True ∧ (p5 → p5)) ∨ p3)) ∧ True) := by
    -- Conjunctions on the right can always be decomposed.
    apply And.intro
    -- Implications on the right can always be decomposed.
    intro h3
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Conjunctions on the right can always be decomposed.
    apply And.intro
    -- True on the right can always be proven directly.
    apply True.intro
    -- Implications on the right can always be decomposed.
    intro h4
    -- One of the premise coincides with the conclusion.
    exact h4
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h5 := h1 h2
  -- False on the left can always be used.
  apply False.elim h5



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_673551061847555446074652231176 : ((((((p4 → p4) → p1) ∧ ((p1 ∨ p1) ∨ (p2 ∧ ((p3 ∨ (((p4 ∨ p2) ∨ (True ∧ p3)) ∧ p5)) ∨ p3)))) → ((p4 ∨ False) ∨ True)) ∨ p3) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- Disjunctions on the left can always be decomposed.
  cases h3
  case inl h4 =>
    -- Disjunctions on the left can always be decomposed.
    cases h4
    case inl h5 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- True on the right can always be proven directly.
      apply True.intro
    case inr h6 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- True on the right can always be proven directly.
      apply True.intro
  case inr h7 =>
    -- Conjunctions on the left can always be decomposed.
    let h8 := h7.left
    let h9 := h7.right
    -- Disjunctions on the left can always be decomposed.
    cases h9
    case inl h10 =>
      -- Disjunctions on the left can always be decomposed.
      cases h10
      case inl h11 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- True on the right can always be proven directly.
        apply True.intro
      case inr h12 =>
        -- Conjunctions on the left can always be decomposed.
        let h13 := h12.left
        let h14 := h12.right
        -- Disjunctions on the left can always be decomposed.
        cases h13
        case inl h15 =>
          -- Disjunctions on the left can always be decomposed.
          cases h15
          case inl h16 =>
            -- Show the right disjunct based on <expert-advice>.
            apply Or.inr
            -- True on the right can always be proven directly.
            apply True.intro
          case inr h17 =>
            -- Show the right disjunct based on <expert-advice>.
            apply Or.inr
            -- True on the right can always be proven directly.
            apply True.intro
        case inr h18 =>
          -- Conjunctions on the left can always be decomposed.
          let h19 := h18.left
          let h20 := h18.right
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- True on the right can always be proven directly.
          apply True.intro
    case inr h21 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- True on the right can always be proven directly.
      apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_157731231998645324866927285119 : (((p3 ∨ (((True ∨ p3) ∨ p4) ∨ (p5 → ((p5 → p3) ∧ (p3 → False))))) → ((p3 ∨ p2) ∨ p1)) ∨ (p2 ∨ ((p1 → p3) → (False → p4)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- False on the left can always be used.
  apply False.elim h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_336390028594828010009687528820 : (p1 → ((p2 ∧ ((((((p5 ∨ p3) → (True ∧ True)) ∨ ((p4 ∨ False) → (False ∧ p2))) ∧ ((p4 → False) ∨ (False ∨ p5))) → p2) ∨ False)) ∨ p1)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_205299464407938732857570700118 : (((p5 ∧ (p4 ∨ p2)) ∨ (False ∨ p4)) ∨ (p5 ∨ ((p4 ∧ (p3 ∧ ((p4 → p4) → ((True ∨ (p2 → p2)) ∨ p4)))) → (p2 → (True ∨ p4))))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Conjunctions on the left can always be decomposed.
  let h3 := h1.left
  let h4 := h1.right
  -- Conjunctions on the left can always be decomposed.
  let h5 := h4.left
  let h6 := h4.right
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_178374115914601744123305799148 : (((((((p2 ∨ p3) ∨ p2) ∧ True) ∨ (p3 ∧ p5)) ∨ p1) → (p5 ∨ p1)) ∨ (True ∨ ((False ∧ p5) ∧ (p1 ∨ (p1 ∨ (p2 ∨ (True ∧ p3))))))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



