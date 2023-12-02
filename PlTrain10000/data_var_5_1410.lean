variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_38832365083249715885549165762 : ((((p5 → ((p2 ∨ True) ∨ p2)) → (p2 ∧ ((p5 ∨ (p5 ∧ (False → (p2 → (((p3 → p1) → True) → p2))))) ∨ (False ∧ p1)))) ∧ p3) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_158751040206579173683820421924 : ((p4 ∧ ((p4 ∨ (p4 → ((p2 ∨ p4) ∧ ((p1 ∨ (p1 → (True → False))) ∨ (p3 ∧ False))))) → False)) ∨ (p4 ∨ (True ∨ (True → (p4 ∧ p5))))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_658589766813647876707768575909 : ((((p3 ∨ ((p5 ∧ ((p5 ∨ (p3 ∧ (((p1 ∧ p5) ∨ p3) ∨ False))) ∧ (p2 ∧ (p4 ∨ ((True ∨ True) ∨ p5))))) ∨ p3)) ∨ (True ∨ False)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_174555901229777911332836415263 : ((((False ∨ (p1 → False)) ∨ False) ∧ ((((True → (p1 ∨ p5)) ∨ True) ∧ p4) → p5)) → ((True → (p4 ∧ (p2 ∨ ((p3 ∧ p1) ∧ p3)))) → p5)) := by
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
      -- False on the left can always be used.
      apply False.elim h6
    case inr h7 =>
      -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
      have h8 : True := by
        -- True on the right can always be proven directly.
        apply True.intro
      -- We have shown the premise of h2, we can now drive its conclusion.
      let h9 := h2 h8
      -- We need to get the left conjuct of h9 based on <expert-advice>.
      let h10 := h9.left
      -- We want to use the implication h4 based on <expert-advice>. So we show its premise.
      have h11 : (((True → (p1 ∨ p5)) ∨ True) ∧ p4) := by
        -- Conjunctions on the right can always be decomposed.
        apply And.intro
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- True on the right can always be proven directly.
        apply True.intro
        -- One of the premise coincides with the conclusion.
        exact h10
      -- We have shown the premise of h4, we can now drive its conclusion.
      let h12 := h4 h11
      -- One of the premise coincides with the conclusion.
      exact h12
  case inr h13 =>
    -- False on the left can always be used.
    apply False.elim h13



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_327830297070179518401090566304 : (True → ((((((p4 ∨ (((True ∨ p4) → p3) ∧ (p3 → (p2 ∨ (p1 ∨ p4))))) ∧ p5) ∨ True) ∨ True) ∧ ((p1 ∧ True) ∨ p4)) ∨ (p5 → True))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h2
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_40310311751783113383823663551 : ((((((((True → p5) → ((False → p2) ∧ p2)) ∧ p1) ∨ ((((p4 ∨ (p2 → p4)) ∧ p1) → p5) ∧ (False ∧ p3))) ∧ p4) ∨ True) ∨ p5) ∨ p3) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_687543039267788196314948499520 : ((((((p4 ∨ (p5 ∧ ((p1 ∨ (True ∨ p2)) → (p5 → (p1 → True))))) ∧ p5) → p1) ∧ ((p1 → (p3 ∧ False)) → (True ∧ (p2 → False)))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_739359140060139093090787444512 : ((((p4 ∧ p4) ∨ (p2 ∨ (((((p5 ∨ p5) ∨ p1) ∧ (p3 → (((p1 ∧ ((p2 → p5) ∨ (True ∨ False))) → p4) → p1))) ∧ True) ∨ True))) ∨ p1) ∧ True) := by
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
theorem thm_5_vars_303215545845019584522491329332 : (False ∨ (p4 → (p2 → (((False ∧ p4) → (p1 → (p3 → p1))) ∧ ((((p3 ∧ (p4 ∨ p1)) ∧ (False ∧ p3)) ∨ ((p2 ∧ p5) ∧ p4)) ∨ True))))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h3
  -- Implications on the right can always be decomposed.
  intro h4
  -- Implications on the right can always be decomposed.
  intro h5
  -- Conjunctions on the left can always be decomposed.
  let h6 := h3.left
  let h7 := h3.right
  -- False on the left can always be used.
  apply False.elim h6
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_177778229338188264715539415809 : (((p2 ∧ (p3 → (((p2 → p1) → (p1 ∧ (p2 ∨ p2))) ∨ p2))) ∧ p2) ∨ ((True ∧ p4) → (p3 ∨ ((((p1 → p5) ∧ False) ∧ p5) → p2)))) := by
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
  -- Conjunctions on the left can always be decomposed.
  let h5 := h4.left
  let h6 := h4.right
  -- Conjunctions on the left can always be decomposed.
  let h7 := h5.left
  let h8 := h5.right
  -- False on the left can always be used.
  apply False.elim h8



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_57380300983291697902630873909 : (((p5 ∧ (False → p5)) ∨ ((((((True → ((p3 → p2) → True)) → (True ∧ p2)) ∨ True) ∧ (p5 ∧ (True ∨ (p5 ∧ p2)))) ∧ p3) ∧ p4)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_308434268422034976672937041738 : (p2 ∨ ((((p5 → p5) → (((((p3 → (((p5 ∨ p5) ∧ False) → (p3 ∧ p5))) ∧ (p3 ∧ p3)) ∨ False) ∧ p4) → (p4 ∨ p4))) → p2) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_348076091433891299863258647280 : (p3 → ((p5 ∨ p5) ∨ ((p2 ∨ ((((p4 ∧ (((p5 → p5) ∧ (p4 ∧ (False ∧ p2))) ∧ p3)) → False) ∧ (p4 ∨ p4)) → (p1 ∧ True))) ∨ p3))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_190855785357422443976953397605 : ((((False → ((p2 → p4) ∧ p2)) ∨ p4) → (p2 ∨ p1)) ∨ (((p3 ∧ (p1 → p5)) ∨ (True ∨ (((p3 ∨ (p3 ∧ p2)) → p3) ∨ p1))) ∨ p1)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_632881022557089131126025214609 : ((((((p1 → ((((p5 ∨ p4) ∧ p1) → (((True → True) ∨ p5) ∨ (p1 → (p4 → (False ∨ False))))) → p3)) → True) ∧ (p2 ∧ p3)) → p1) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_178585793429432001430107947081 : ((((((p5 → p2) ∨ p3) ∧ p4) ∨ p3) ∨ ((False → p5) ∧ (p1 ∨ p1))) ∨ (p2 → (p2 ∨ ((p1 ∧ (p2 ∨ p1)) ∧ ((False → p1) → p4))))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_134195804237584086097171042059 : ((((p1 → (((p4 ∨ True) → p2) → (p1 → (False ∧ p1)))) ∧ (True → ((False ∧ (p4 ∨ (p1 ∨ p2))) ∨ p1))) ∨ True) ∨ ((p5 ∧ False) → p3)) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_171347161195863196134618742860 : (((((p3 ∨ p4) ∧ (((False ∧ p1) → p5) ∧ (p3 ∧ (False → p1)))) → p5) ∧ False) ∨ (p1 ∨ ((p3 → p2) ∨ (((p4 ∧ p3) ∨ True) ∨ p4)))) := by
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
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_661691293524595648799798688039 : (((((((False → (p1 ∧ True)) ∧ ((True ∨ ((p5 ∧ (p1 → p5)) → p1)) ∨ p5)) ∧ p2) ∧ (True ∧ ((p5 ∧ False) ∨ p2))) → (p1 ∨ p2)) ∨ p1) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
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
  let h6 := h4.left
  let h7 := h4.right
  -- Disjunctions on the left can always be decomposed.
  cases h7
  case inl h8 =>
    -- Disjunctions on the left can always be decomposed.
    cases h8
    case inl h9 =>
      -- Conjunctions on the left can always be decomposed.
      let h10 := h3.left
      let h11 := h3.right
      -- Disjunctions on the left can always be decomposed.
      cases h11
      case inl h12 =>
        -- Conjunctions on the left can always be decomposed.
        let h13 := h12.left
        let h14 := h12.right
        -- False on the left can always be used.
        apply False.elim h14
      case inr h15 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- One of the premise coincides with the conclusion.
        exact h15
    case inr h16 =>
      -- Conjunctions on the left can always be decomposed.
      let h17 := h3.left
      let h18 := h3.right
      -- Disjunctions on the left can always be decomposed.
      cases h18
      case inl h19 =>
        -- Conjunctions on the left can always be decomposed.
        let h20 := h19.left
        let h21 := h19.right
        -- False on the left can always be used.
        apply False.elim h21
      case inr h22 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- One of the premise coincides with the conclusion.
        exact h22
  case inr h23 =>
    -- Conjunctions on the left can always be decomposed.
    let h24 := h3.left
    let h25 := h3.right
    -- Disjunctions on the left can always be decomposed.
    cases h25
    case inl h26 =>
      -- Conjunctions on the left can always be decomposed.
      let h27 := h26.left
      let h28 := h26.right
      -- False on the left can always be used.
      apply False.elim h28
    case inr h29 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- One of the premise coincides with the conclusion.
      exact h29
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_69161868766107363466911828774 : ((p5 → (((((p1 ∧ ((p4 ∧ ((False → p2) ∧ p2)) ∧ (True → p3))) ∨ p1) ∧ (p1 → p3)) → p1) → ((p5 ∧ False) ∧ (p2 → p2)))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_192233584798552137646585806449 : (((((p2 ∨ (True → p2)) ∧ p5) ∨ (p2 ∧ False)) ∧ p2) → ((((p2 → ((p4 → ((p5 → False) ∧ p4)) → (p2 ∧ p5))) ∨ p1) → p1) ∨ p2)) := by
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
    -- Disjunctions on the left can always be decomposed.
    cases h5
    case inl h7 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- One of the premise coincides with the conclusion.
      exact h3
    case inr h8 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- One of the premise coincides with the conclusion.
      exact h3
  case inr h9 =>
    -- Conjunctions on the left can always be decomposed.
    let h10 := h9.left
    let h11 := h9.right
    -- False on the left can always be used.
    apply False.elim h11



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_338430815766435457157888073623 : (p1 → ((False → (p3 ∨ (False ∨ p5))) → ((((p5 ∨ (((p1 ∧ ((False → p3) ∨ p5)) → False) ∨ True)) ∨ False) ∨ True) ∨ ((p3 → p4) ∨ p1)))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_655895363308514998546610895078 : (((((False → (True ∨ ((p5 → (((p5 ∧ p2) → (p1 → False)) → (p4 → p3))) → (p1 ∨ True)))) → ((False → p1) ∧ False)) ∨ (p1 → p1)) ∨ p1) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- One of the premise coincides with the conclusion.
  exact h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_173167172858503508782325230764 : ((p4 ∨ ((p5 ∨ (((((p4 → (p5 → p5)) ∧ p4) → p1) ∧ p4) ∧ p2)) ∧ p1)) ∨ ((((p4 ∨ (p4 ∨ False)) → p2) ∨ (True ∨ False)) ∨ p5)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_44010576459756229445260645808 : ((((((True → True) → ((p5 ∧ (((False ∨ p3) ∧ p3) ∧ False)) ∨ (False ∨ False))) ∧ (((False → p2) ∨ p3) ∨ p1)) → (p4 ∧ p1)) → p5) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_50273717406847440943365855289 : (((((p4 ∨ (p3 ∧ ((p1 ∨ ((False → p1) → p2)) → (False → (p3 ∧ p1))))) → p2) ∨ (p3 ∧ False)) ∨ ((True → (p4 ∧ False)) → p5)) ∨ p5) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
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
  -- We need to get the right conjuct of h3 based on <expert-advice>.
  let h4 := h3.right
  -- False on the left can always be used.
  apply False.elim h4



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_512290594721182665237607636396 : ((((p2 ∧ p5) ∨ (((True ∧ p2) ∨ (p2 ∧ (True ∧ (((p1 → (p5 ∧ p1)) ∨ ((((False → p4) ∧ p3) → False) ∨ p3)) → False)))) ∨ True)) ∧ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_257329897611627232263391066903 : ((p2 ∨ p4) → (((((True ∨ p2) ∧ ((p3 ∨ p1) → p4)) → p3) ∧ False) ∨ (((p3 ∧ False) ∨ p1) ∨ (False → (((p1 → p5) → p1) ∨ p5))))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h2 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h3
    -- False on the left can always be used.
    apply False.elim h3
  case inr h4 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h5
    -- False on the left can always be used.
    apply False.elim h5



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_49004705146486141158447068832 : ((((((p3 ∨ (p5 ∨ (p3 → (False → (((True ∨ p4) ∧ p1) ∧ True))))) ∧ ((p2 ∨ p5) → False)) ∧ p1) → p4) ∨ ((True ∧ p3) → p3)) ∨ p5) := by
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



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_345369027256415042835594650675 : (p3 → ((((((p1 → (p2 ∨ False)) ∧ (p1 ∧ p2)) ∨ (p2 → (p4 ∨ (p2 ∨ p1)))) → (((p5 → (False ∧ False)) ∧ p5) ∧ p3)) ∨ p3) ∨ True)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_50080510827195490016566976750 : (((False ∧ ((p1 ∨ (p2 ∧ (((((p4 ∨ True) ∧ p1) → (False ∧ p4)) ∧ (True → False)) → True))) ∨ p3)) ∧ ((p3 ∧ (True → p3)) ∧ False)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_785513835801219875045811593065 : (((p4 ∨ ((p1 ∧ ((((((p1 ∨ p4) ∨ p5) → ((p4 → True) ∨ True)) ∧ (p2 → ((p3 ∨ p5) → p5))) ∨ (False ∨ False)) ∧ False)) ∨ True)) ∨ p1) ∧ True) := by
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
theorem thm_5_vars_47326019137962046294843970402 : ((((p1 ∨ (p2 ∧ p4)) → (((p1 ∨ (p4 ∧ p5)) ∨ (p3 ∧ ((True ∧ ((p1 → True) ∧ p1)) ∨ p1))) ∨ (p4 → p1))) ∨ (False → p5)) ∨ False) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_158764519119721779934482247998 : ((p4 ∧ ((p2 ∨ False) ∧ (p2 ∨ (p4 → ((p2 → (((p4 ∧ (p3 ∧ p2)) → p4) ∨ p4)) → False))))) ∨ (p2 → ((True → p3) → (p2 → p2)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Implications on the right can always be decomposed.
  intro h3
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_162501759373221348452794021374 : (((False ∨ (True → ((p5 → (((p2 → (p3 ∧ False)) → (True ∨ p5)) ∨ p1)) ∨ p3))) ∨ p1) ∧ ((p1 ∨ True) → ((p4 ∨ p4) ∨ (False → p4)))) := by
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
  -- Implications on the right can always be decomposed.
  intro h2
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h3
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro
  -- Implications on the right can always be decomposed.
  intro h4
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
theorem thm_5_vars_52604531901776453735919750900 : ((((((p4 → p5) ∨ p3) ∧ p2) ∧ (((p3 ∨ p3) → True) → (p2 ∨ p1))) ∨ (True → (p5 → (p5 ∧ ((p2 → True) → (p5 ∨ p4)))))) ∨ p1) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- One of the premise coincides with the conclusion.
  exact h2
  -- Implications on the right can always be decomposed.
  intro h3
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- One of the premise coincides with the conclusion.
  exact h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_666847128497631790708599620895 : ((((((p3 ∧ (p1 → (True ∨ p4))) ∨ False) ∧ (p3 → ((p2 ∧ (p5 ∨ False)) ∧ (p4 ∨ (p4 ∨ (p4 ∨ p1)))))) ∧ ((p1 ∨ p1) ∧ p5)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_170196353679244114532423706682 : ((((p4 → True) → (p1 ∨ (p1 → True))) ∧ (True ∨ ((p2 ∨ True) ∧ (True → p4)))) ∧ ((((((p3 → p5) ∨ p2) → p4) ∨ True) ∨ p4) ∨ p4)) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h2
  -- True on the right can always be proven directly.
  apply True.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_61483357751690655160095632112 : ((p1 ∧ (((((p3 ∨ (p1 ∨ (p5 ∧ (p2 ∧ (True ∧ p1))))) ∨ (p3 ∧ p3)) ∧ (p3 ∨ p2)) ∨ (True → p5)) ∧ (True ∧ (True → p5)))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_196836717678639865529753994287 : (((p4 ∧ (((True → True) ∨ p5) → False)) ∧ p5) ∨ ((p2 → (p5 ∨ ((p5 → (((p2 → False) ∨ (p3 ∧ False)) ∧ True)) → (p1 → p1)))) ∨ False)) := by
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
  -- One of the premise coincides with the conclusion.
  exact h3



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_218145037379626898142607860355 : (((p4 → p3) ∧ (p2 → p1)) → ((((p5 → False) ∨ p4) ∨ ((True ∨ (((p2 → (p2 → ((p2 ∨ p4) → p5))) ∧ p4) ∧ p2)) → True)) ∨ p3)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h4
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_172000794044746498085203959651 : (((((p1 → (((p4 → p5) ∨ False) ∨ p2)) ∨ (False ∨ True)) → p2) ∨ (False → True)) ∨ (p3 → (p3 ∧ ((p1 ∧ (True ∨ True)) → (p2 ∧ p4))))) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_225370242230577137994074291562 : (((p2 ∨ False) ∧ True) ∨ (((p1 ∨ ((False ∧ False) ∧ (((p1 → p5) → (p2 → p1)) → (p5 ∨ True)))) → p4) → (p5 ∨ ((p2 → True) ∨ p2)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
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



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_64357761807047337763059348759 : ((p1 ∨ ((((p3 → ((p5 ∨ (False ∧ (p5 ∨ True))) ∧ (False → (p3 ∨ (p1 ∨ (p2 ∨ True)))))) → (True → p5)) ∨ (True → p5)) ∨ True)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_729535396104255590598468754699 : (((((p2 ∨ p2) ∨ p3) → (p2 → (((p1 ∧ (p3 ∨ (p4 ∧ (p5 ∨ ((p2 ∧ ((True ∨ False) → p3)) ∧ p5))))) ∨ (p2 → False)) ∧ p2))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_626592265778682892314653580084 : ((((p4 → ((p4 → p1) → (p2 ∨ ((p2 ∧ ((True → p2) → (p4 ∨ (p3 → (p2 ∨ (((True ∧ p3) → False) ∧ p5)))))) ∧ p2)))) ∨ True) ∨ p5) ∧ True) := by
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
theorem thm_5_vars_805162812338725921389030447747 : (((p3 → (p2 ∧ (((((p5 ∨ (p5 ∨ (False ∧ ((p4 ∨ p1) → (p3 → ((p4 → p4) ∨ False)))))) ∧ p1) ∧ p5) → (p4 ∨ p5)) → p4))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_623915238235125558754407379011 : ((((p2 ∨ (((((p4 ∧ (p3 ∨ p4)) ∨ ((p2 → ((p1 ∧ p1) ∧ (p4 → (True ∧ p3)))) ∧ (p1 → p2))) → False) ∧ p3) ∧ p1)) ∨ True) ∨ p5) ∧ True) := by
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
theorem thm_5_vars_354713629947662069047568318364 : (p5 → (((p3 ∧ ((((False ∧ (p1 → ((p4 ∨ ((p5 → p3) → p5)) ∨ p4))) ∨ False) ∧ (p5 → p4)) ∨ p1)) ∧ ((p4 ∨ p1) → True)) ∨ True)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_180370794499159085100936420127 : (((((False ∧ (p4 ∧ p1)) → (True ∧ False)) ∧ (p2 ∨ p5)) ∨ (False ∧ p3)) → ((p3 ∧ p1) ∨ (p5 ∨ (((True ∨ p4) ∧ (p5 → False)) → True)))) := by
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
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Implications on the right can always be decomposed.
      intro h6
      -- True on the right can always be proven directly.
      apply True.intro
    case inr h7 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- One of the premise coincides with the conclusion.
      exact h7
  case inr h8 =>
    -- Conjunctions on the left can always be decomposed.
    let h9 := h8.left
    let h10 := h8.right
    -- False on the left can always be used.
    apply False.elim h9



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_130549153536773975600567636453 : (((True → ((p5 ∧ (True → p4)) ∧ (((True ∧ (True ∨ p5)) ∧ p2) ∧ ((p5 ∧ p3) ∧ p3)))) → (p4 → (p1 → p3))) ∧ ((True ∨ p4) ∨ p3)) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Implications on the right can always be decomposed.
  intro h3
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h4 : True := by
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h5 := h1 h4
  -- We need to get the right conjuct of h5 based on <expert-advice>.
  let h6 := h5.right
  -- We need to get the right conjuct of h6 based on <expert-advice>.
  let h7 := h6.right
  -- We need to get the right conjuct of h7 based on <expert-advice>.
  let h8 := h7.right
  -- One of the premise coincides with the conclusion.
  exact h8
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_257232352998211730235927837259 : ((p2 ∨ p2) → (p5 ∨ (((((p4 → (p3 ∧ p5)) ∨ p4) ∨ p1) ∧ p3) ∨ ((p5 ∨ p3) → ((p1 ∨ p2) ∨ (((p2 → True) → True) ∨ False)))))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h2 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h3
    -- Disjunctions on the left can always be decomposed.
    cases h3
    case inl h4 =>
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- One of the premise coincides with the conclusion.
      exact h2
    case inr h5 =>
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- One of the premise coincides with the conclusion.
      exact h2
  case inr h6 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h7
    -- Disjunctions on the left can always be decomposed.
    cases h7
    case inl h8 =>
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- One of the premise coincides with the conclusion.
      exact h6
    case inr h9 =>
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- One of the premise coincides with the conclusion.
      exact h6



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_40076745576488275434804313765 : ((((((((p3 ∨ p3) ∨ (p5 → (p3 ∧ (p4 ∨ p5)))) ∨ ((p1 → (p5 → (True ∨ (p2 → p4)))) ∨ p3)) ∨ p3) → p4) ∧ p3) ∨ p2) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_112244782739846526400862321720 : (((p3 ∨ (((p2 ∨ (p3 → p2)) ∧ (p4 → p5)) ∨ ((p4 ∧ True) ∧ (((p1 ∧ ((True ∧ False) → True)) ∨ p2) ∧ p5)))) ∨ p5) ∨ (True ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_158583611322888403951085606688 : ((True ∧ (p5 ∧ ((((p4 ∨ p2) ∧ p4) ∧ (p5 → ((False → p4) ∧ p2))) → (p5 ∧ (p2 ∨ p1))))) ∨ (((p4 → p4) ∨ (p4 → p5)) ∨ False)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_193155330737357998884833616987 : (((p3 ∨ (p5 ∧ (False ∨ p5))) ∨ (p4 ∧ (True ∧ False))) → ((p3 ∧ (p3 ∧ ((p1 ∧ (((p2 → p1) ∧ p1) ∧ (True ∧ False))) ∧ p3))) ∨ True)) := by
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
      -- Disjunctions on the left can always be decomposed.
      cases h6
      case inl h7 =>
        -- False on the left can always be used.
        apply False.elim h7
      case inr h8 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- True on the right can always be proven directly.
        apply True.intro
  case inr h9 =>
    -- Conjunctions on the left can always be decomposed.
    let h10 := h9.left
    let h11 := h9.right
    -- Conjunctions on the left can always be decomposed.
    let h12 := h11.left
    let h13 := h11.right
    -- False on the left can always be used.
    apply False.elim h13



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_313922827510145824105952060137 : (p3 ∨ (((((p5 ∨ ((p5 → True) → p2)) ∨ ((((p1 ∧ False) ∧ False) ∧ (True ∨ p1)) ∨ p5)) ∨ ((p5 ∨ True) ∨ p3)) ∧ p5) ∨ (True ∨ p4))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_194141231582854950066786287454 : ((p1 → ((p3 → ((p2 → True) ∨ p1)) ∨ (p1 ∧ p5))) → (p1 ∨ ((((p2 ∨ p1) → ((False ∨ p5) ∧ p4)) ∧ (p5 ∨ (p3 ∨ p5))) ∨ True))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_388541665720123140567650801157 : (((((True → ((((((p1 ∧ p5) → p1) ∨ (False → True)) ∧ ((False ∨ p3) → False)) → p4) → False)) → (p5 → ((p2 ∨ p2) ∧ False))) ∨ True) ∧ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_306153564035122073398177615669 : (p1 ∨ (((p3 ∧ p1) ∨ p1) ∨ ((p2 ∧ (p4 ∧ p1)) ∨ (p1 → (p4 → (p1 ∧ (((p5 ∨ ((p4 → p3) → True)) → (p4 → True)) ∨ p4))))))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- One of the premise coincides with the conclusion.
  exact h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_148055525711900348843100724718 : (((p2 ∨ ((p2 ∨ p1) ∧ (((p5 ∧ p1) → (p5 ∨ p4)) → ((p4 ∨ p1) ∧ (p4 ∨ p4))))) ∨ (p1 → p1)) ∨ ((False ∨ False) ∧ (p3 ∧ p2))) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_45368493378599212379294508345 : (((p4 ∧ ((p3 ∨ (p3 → p5)) → (p3 → ((p3 ∨ p2) → (p5 ∧ (((p5 ∨ ((p5 ∨ p2) ∨ p5)) → True) ∧ (p2 → p4))))))) → False) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_658674630593262092395656123207 : ((((p4 ∨ ((p2 ∨ (p5 → ((False → p5) ∧ (((True ∨ (False → ((True ∧ p1) ∧ p5))) → (p4 ∨ p1)) → p5)))) → p5)) ∨ (p4 ∨ True)) ∨ p1) ∧ True) := by
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
theorem thm_5_vars_587914823605055728245886366469 : ((((((((p1 → (p5 → ((p5 ∧ p2) ∧ (p3 ∨ ((True ∧ p5) → p5))))) ∧ p4) ∧ (p4 ∨ p2)) ∧ (p2 ∧ (p1 ∨ False))) ∨ p2) ∧ p5) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_42157267593745816161217921366 : ((((p2 → p1) → (((True ∧ False) ∧ (((p1 ∧ (p3 ∧ p4)) ∨ (((False ∨ True) ∧ True) ∨ p2)) ∧ ((True ∧ p3) ∧ p3))) ∨ True)) ∨ False) ∨ p5) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_168000304258451072458451608796 : ((((((False ∨ True) → p1) ∧ p1) ∧ p1) ∨ (((False ∧ False) ∨ ((False ∨ True) → p5)) ∧ True)) → ((p4 ∧ (p2 ∧ p5)) → (p5 ∨ (p5 ∧ False)))) := by
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
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h7 =>
    -- Conjunctions on the left can always be decomposed.
    let h8 := h7.left
    let h9 := h7.right
    -- Conjunctions on the left can always be decomposed.
    let h10 := h8.left
    let h11 := h8.right
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- One of the premise coincides with the conclusion.
    exact h6
  case inr h12 =>
    -- Conjunctions on the left can always be decomposed.
    let h13 := h12.left
    let h14 := h12.right
    -- Disjunctions on the left can always be decomposed.
    cases h13
    case inl h15 =>
      -- Conjunctions on the left can always be decomposed.
      let h16 := h15.left
      let h17 := h15.right
      -- False on the left can always be used.
      apply False.elim h16
    case inr h18 =>
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- One of the premise coincides with the conclusion.
      exact h6



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_114697348406912873372964209779 : ((((((p1 ∧ ((p3 ∧ p5) → p4)) ∧ (p1 ∧ True)) ∨ ((p3 ∨ p3) ∨ p4)) ∧ p2) → (p1 → ((True → (p4 ∧ p4)) ∧ p3))) ∨ (False → True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_218642544359977803264803350809 : ((True ∧ ((p2 → p1) ∨ p5)) → ((p3 ∧ p1) ∨ ((True → p2) ∨ (False ∨ (False → ((p3 ∨ p2) ∨ ((p2 ∨ p4) ∧ (False → (False ∨ p5))))))))) := by
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
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h5
    -- False on the left can always be used.
    apply False.elim h5
  case inr h6 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h7
    -- False on the left can always be used.
    apply False.elim h7



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_325795302022844747377904496857 : (p5 ∨ (p3 ∨ ((((True → p1) → (((p1 → p4) ∨ p4) ∨ ((p1 ∨ True) → True))) ∨ ((False ∧ ((True ∧ p3) ∧ False)) → (p5 → p3))) ∨ False))) := by
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
  -- Conjunctions on the left can always be decomposed.
  let h3 := h1.left
  let h4 := h1.right
  -- False on the left can always be used.
  apply False.elim h3



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_112107677705565373243354432842 : ((((p3 ∨ p2) → ((((((p4 ∨ p3) ∨ p4) ∨ (p2 ∧ (p3 ∨ (True ∧ (True → p2))))) ∧ p2) → (p4 ∧ p2)) ∨ p4)) ∨ True) ∨ (p4 ∨ p1)) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_185281573253372697694395075707 : ((p2 ∧ ((True → ((((True → True) ∧ p5) ∨ p3) ∨ False)) ∨ True)) ∨ (((((p1 → (p1 → p3)) → (p4 ∧ p3)) ∧ p3) → p2) → (p2 ∨ True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_670549911811405654087995625074 : (((((p5 ∧ True) ∨ (((p4 → (p1 ∧ False)) ∨ ((False → (p4 ∨ False)) ∧ p3)) ∨ (p4 → (p4 ∧ (False ∨ p5))))) ∨ (p3 ∨ (p5 → p5))) ∨ p5) ∧ True) := by
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
  -- One of the premise coincides with the conclusion.
  exact h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_356258713630475745765698485823 : (p5 → (((p2 ∧ ((((p1 ∧ p3) ∧ False) ∧ (True ∨ p5)) ∧ p3)) ∨ ((p2 ∨ False) ∨ p5)) ∨ ((((True ∧ (p4 ∨ True)) → True) ∨ p3) ∨ p2))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_116788175338149595265016649198 : (((p1 ∨ p4) ∨ ((((False → (True → p5)) ∧ False) → (((False ∧ p5) ∧ p3) ∨ (p2 ∨ False))) → ((p1 ∧ False) ∧ (True ∧ p2)))) ∨ (p4 ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_325066260836397351424920458424 : (p5 ∨ ((p3 ∨ p3) → ((p2 → ((True → (p3 → True)) → (p5 ∧ ((((p4 ∧ p4) ∨ p4) → (p1 ∨ p5)) ∧ p4)))) ∨ (True ∨ (False → p4))))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h2 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- True on the right can always be proven directly.
    apply True.intro
  case inr h3 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- True on the right can always be proven directly.
    apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_312001555028839201197186878789 : (p2 ∨ (p4 ∨ ((((False → p4) ∧ (False ∧ p4)) ∧ ((p4 ∧ (True → False)) ∧ ((p3 ∧ ((True → p2) → p1)) → p2))) ∨ (True → (True ∨ p5))))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_147001773902154108483944645398 : ((((False ∨ (p3 ∧ (p3 → ((((((False ∧ p5) ∧ p1) → False) → False) → p4) ∧ p5)))) ∧ (p3 ∧ True)) ∧ p5) ∨ (((False ∧ p5) ∧ False) → p3)) := by
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
  -- False on the left can always be used.
  apply False.elim h4



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_238259683488636132968335069919 : ((True ∨ p5) ∧ ((((p2 ∨ False) ∧ (p1 ∧ True)) ∧ ((p2 ∨ p5) → (p1 ∧ p3))) ∨ ((((p4 ∨ (p2 ∨ p5)) ∨ p5) ∧ (p1 ∧ False)) → False))) := by
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
  cases h2
  case inl h4 =>
    -- Disjunctions on the left can always be decomposed.
    cases h4
    case inl h5 =>
      -- Conjunctions on the left can always be decomposed.
      let h6 := h3.left
      let h7 := h3.right
      -- False on the left can always be used.
      apply False.elim h7
    case inr h8 =>
      -- Disjunctions on the left can always be decomposed.
      cases h8
      case inl h9 =>
        -- Conjunctions on the left can always be decomposed.
        let h10 := h3.left
        let h11 := h3.right
        -- False on the left can always be used.
        apply False.elim h11
      case inr h12 =>
        -- Conjunctions on the left can always be decomposed.
        let h13 := h3.left
        let h14 := h3.right
        -- False on the left can always be used.
        apply False.elim h14
  case inr h15 =>
    -- Conjunctions on the left can always be decomposed.
    let h16 := h3.left
    let h17 := h3.right
    -- False on the left can always be used.
    apply False.elim h17



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_641131833739195800188820558156 : (((((False ∨ p3) ∨ (((p3 ∧ (((p2 ∧ True) ∨ p4) → p3)) ∧ p3) → (((p5 ∧ p2) ∨ (((False ∨ True) ∨ True) ∨ p3)) → False))) → False) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_786193376965569989586940447825 : (((p4 ∨ ((((p3 ∨ True) ∨ ((False → (p2 ∨ ((False → ((False ∧ p5) → p2)) ∧ p2))) ∧ p4)) → (p1 ∧ False)) → (p5 → (p3 ∨ p3)))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_199471839216441026382978039551 : (((p1 ∨ ((p1 → p3) ∨ (p5 ∧ p3))) ∨ p5) → (p1 ∨ ((p4 ∧ (p1 ∧ (((p3 → p4) → (True ∧ False)) ∧ ((p1 ∨ False) ∧ True)))) → p5))) := by
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
      -- One of the premise coincides with the conclusion.
      exact h3
    case inr h4 =>
      -- Disjunctions on the left can always be decomposed.
      cases h4
      case inl h5 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- Implications on the right can always be decomposed.
        intro h6
        -- Conjunctions on the left can always be decomposed.
        let h7 := h6.left
        let h8 := h6.right
        -- Conjunctions on the left can always be decomposed.
        let h9 := h8.left
        let h10 := h8.right
        -- Conjunctions on the left can always be decomposed.
        let h11 := h10.left
        let h12 := h10.right
        -- Conjunctions on the left can always be decomposed.
        let h13 := h12.left
        let h14 := h12.right
        -- Disjunctions on the left can always be decomposed.
        cases h13
        case inl h15 =>
          -- We want to use the implication h11 based on <expert-advice>. So we show its premise.
          have h16 : (p3 → p4) := by
            -- Implications on the right can always be decomposed.
            intro h17
            -- One of the premise coincides with the conclusion.
            exact h7
          -- We have shown the premise of h11, we can now drive its conclusion.
          let h18 := h11 h16
          -- We need to get the right conjuct of h18 based on <expert-advice>.
          let h19 := h18.right
          -- False on the left can always be used.
          apply False.elim h19
        case inr h20 =>
          -- False on the left can always be used.
          apply False.elim h20
      case inr h21 =>
        -- Conjunctions on the left can always be decomposed.
        let h22 := h21.left
        let h23 := h21.right
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- Implications on the right can always be decomposed.
        intro h24
        -- Conjunctions on the left can always be decomposed.
        let h25 := h24.left
        let h26 := h24.right
        -- Conjunctions on the left can always be decomposed.
        let h27 := h26.left
        let h28 := h26.right
        -- Conjunctions on the left can always be decomposed.
        let h29 := h28.left
        let h30 := h28.right
        -- Conjunctions on the left can always be decomposed.
        let h31 := h30.left
        let h32 := h30.right
        -- Disjunctions on the left can always be decomposed.
        cases h31
        case inl h33 =>
          -- One of the premise coincides with the conclusion.
          exact h22
        case inr h34 =>
          -- False on the left can always be used.
          apply False.elim h34
  case inr h35 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h36
    -- Conjunctions on the left can always be decomposed.
    let h37 := h36.left
    let h38 := h36.right
    -- Conjunctions on the left can always be decomposed.
    let h39 := h38.left
    let h40 := h38.right
    -- Conjunctions on the left can always be decomposed.
    let h41 := h40.left
    let h42 := h40.right
    -- Conjunctions on the left can always be decomposed.
    let h43 := h42.left
    let h44 := h42.right
    -- Disjunctions on the left can always be decomposed.
    cases h43
    case inl h45 =>
      -- One of the premise coincides with the conclusion.
      exact h35
    case inr h46 =>
      -- False on the left can always be used.
      apply False.elim h46



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_22937219932356710056420138179 : (((p4 ∧ ((False ∨ (p1 ∨ False)) ∨ p4)) ∨ (((((True ∨ p3) ∧ p2) → p3) ∧ False) → (p5 → (p3 → ((p2 ∧ p1) ∨ (p4 → False)))))) ∧ True) := by
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
  -- Conjunctions on the left can always be decomposed.
  let h4 := h1.left
  let h5 := h1.right
  -- False on the left can always be used.
  apply False.elim h5
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_14445251510486788340576059098 : (((((p1 → (((p3 ∧ p2) ∧ ((((p4 ∨ True) → ((p5 ∨ p2) → (p5 → p5))) → p3) ∨ p3)) → False)) ∧ p1) ∧ False) ∨ (p5 → p5)) ∧ True) := by
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



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_670466424802773998582962751259 : (((((p5 ∧ p5) ∧ (False ∧ ((((p1 ∨ ((False ∧ p5) → p5)) ∨ (p3 ∨ p4)) ∧ ((p2 ∨ p2) ∧ p2)) ∧ p4))) ∨ ((p3 ∨ False) → p3)) ∨ False) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h2 =>
    -- One of the premise coincides with the conclusion.
    exact h2
  case inr h3 =>
    -- False on the left can always be used.
    apply False.elim h3
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_258661041191448345499985901227 : ((p5 ∨ p5) → (((True ∨ ((p1 ∨ False) ∧ True)) → (((p4 ∨ (True ∧ (p4 → p3))) → (p4 ∨ p1)) ∧ False)) → ((p1 ∨ (p1 → p5)) → p2))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Implications on the right can always be decomposed.
  intro h3
  -- Disjunctions on the left can always be decomposed.
  cases h3
  case inl h4 =>
    -- Disjunctions on the left can always be decomposed.
    cases h1
    case inl h5 =>
      -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
      have h6 : (True ∨ ((p1 ∨ False) ∧ True)) := by
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- True on the right can always be proven directly.
        apply True.intro
      -- We have shown the premise of h2, we can now drive its conclusion.
      let h7 := h2 h6
      -- We need to get the right conjuct of h7 based on <expert-advice>.
      let h8 := h7.right
      -- False on the left can always be used.
      apply False.elim h8
    case inr h9 =>
      -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
      have h10 : (True ∨ ((p1 ∨ False) ∧ True)) := by
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- True on the right can always be proven directly.
        apply True.intro
      -- We have shown the premise of h2, we can now drive its conclusion.
      let h11 := h2 h10
      -- We need to get the right conjuct of h11 based on <expert-advice>.
      let h12 := h11.right
      -- False on the left can always be used.
      apply False.elim h12
  case inr h13 =>
    -- Disjunctions on the left can always be decomposed.
    cases h1
    case inl h14 =>
      -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
      have h15 : (True ∨ ((p1 ∨ False) ∧ True)) := by
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- True on the right can always be proven directly.
        apply True.intro
      -- We have shown the premise of h2, we can now drive its conclusion.
      let h16 := h2 h15
      -- We need to get the right conjuct of h16 based on <expert-advice>.
      let h17 := h16.right
      -- False on the left can always be used.
      apply False.elim h17
    case inr h18 =>
      -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
      have h19 : (True ∨ ((p1 ∨ False) ∧ True)) := by
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- True on the right can always be proven directly.
        apply True.intro
      -- We have shown the premise of h2, we can now drive its conclusion.
      let h20 := h2 h19
      -- We need to get the right conjuct of h20 based on <expert-advice>.
      let h21 := h20.right
      -- False on the left can always be used.
      apply False.elim h21



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_2659409298735602671010883637 : ((((p5 ∨ p4) → p5) → (False ∨ p4)) ∨ ((((p4 ∧ (p4 ∨ (p1 → True))) → p1) → p4) ∨ ((p3 → ((p4 ∧ p1) → p1)) ∨ p2))) := by
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
  -- Conjunctions on the left can always be decomposed.
  let h3 := h2.left
  let h4 := h2.right
  -- One of the premise coincides with the conclusion.
  exact h4



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_178829129602297040139261918566 : ((((True ∧ p4) ∧ True) → ((True → ((p3 → p3) → True)) → (p3 ∧ False))) ∨ (p5 → (p1 → (((p5 → p4) → ((p5 ∧ False) ∨ p2)) ∨ True)))) := by
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
theorem thm_5_vars_347601999518070156965412606611 : (p3 → ((((True ∨ p3) ∨ p5) → p4) ∨ (True → ((((((p2 ∧ p2) ∨ (p2 ∧ p2)) → ((p4 → p1) → p3)) ∧ True) → (p3 → p2)) ∨ p3)))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h2
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_182454477777616294008836764346 : ((((p5 ∧ p5) ∧ ((p1 ∨ (True ∧ p5)) ∨ p2)) ∨ (p5 ∨ True)) ∧ ((False → (p3 ∨ p1)) → (True ∧ (((p4 ∨ False) ∨ (p5 → p5)) ∨ p1)))) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h2
  -- One of the premise coincides with the conclusion.
  exact h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_179306323263849723085020164078 : ((False ∨ ((True → (True ∨ (p3 → False))) ∧ ((p3 ∨ (p4 ∧ p5)) ∧ p1))) ∨ (((((p3 ∧ p5) → p2) → (p1 ∧ (True ∧ p3))) ∨ p5) → True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_654782069042240328791647642457 : ((((((p1 ∧ (p4 ∧ ((((True ∧ p4) ∧ (p2 ∨ p4)) ∧ ((False ∨ p4) ∨ (False ∧ (True ∧ p2)))) ∧ True))) → p5) → p1) ∨ (p2 → p4)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_90933936185426799317880854249 : (((True → p2) ∧ (p4 ∧ ((p4 → p3) → (True ∧ (((True → p5) → p5) ∧ (p3 ∨ ((False ∨ p4) → ((p2 → True) ∨ (p2 ∨ p2))))))))) → p2) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- Conjunctions on the left can always be decomposed.
  let h4 := h3.left
  let h5 := h3.right
  -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
  have h6 : True := by
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h2, we can now drive its conclusion.
  let h7 := h2 h6
  -- One of the premise coincides with the conclusion.
  exact h7



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_338455636647557890920573935618 : (p1 → (((p2 → p2) ∨ True) ∧ ((((((p2 ∨ (p1 ∨ p1)) ∧ True) ∧ (((p1 ∨ p1) ∧ p2) ∧ p5)) → (False ∧ (p3 → False))) ∨ True) ∧ True))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_148584029239350597235150063221 : ((((p4 ∧ (((p1 ∧ p5) ∨ (p2 ∧ p2)) → p2)) → p3) ∨ (((p4 ∧ p2) ∨ ((p5 → p5) → p5)) → p5)) ∨ ((p2 ∧ (False → p4)) → True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_168778086061670017642364499845 : ((p1 ∨ (((p2 ∧ True) ∨ (p2 ∧ False)) ∨ ((False → p5) ∨ (p2 → ((p3 ∧ p4) ∧ True))))) → (((p1 ∧ ((p5 ∨ True) ∧ p2)) ∨ p2) ∨ True)) := by
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
      -- Disjunctions on the left can always be decomposed.
      cases h4
      case inl h5 =>
        -- Conjunctions on the left can always be decomposed.
        let h6 := h5.left
        let h7 := h5.right
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- True on the right can always be proven directly.
        apply True.intro
      case inr h8 =>
        -- Conjunctions on the left can always be decomposed.
        let h9 := h8.left
        let h10 := h8.right
        -- False on the left can always be used.
        apply False.elim h10
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
theorem thm_5_vars_53365533762088613343555071027 : ((((p2 ∧ (p5 ∨ (p3 ∧ (((False → p2) → p3) ∨ p5)))) ∨ p1) → (((p2 ∧ ((p3 ∧ p2) ∨ (True ∨ True))) → False) ∨ (p5 → True))) ∨ p1) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
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
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Implications on the right can always be decomposed.
      intro h6
      -- True on the right can always be proven directly.
      apply True.intro
    case inr h7 =>
      -- Conjunctions on the left can always be decomposed.
      let h8 := h7.left
      let h9 := h7.right
      -- Disjunctions on the left can always be decomposed.
      cases h9
      case inl h10 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- Implications on the right can always be decomposed.
        intro h11
        -- True on the right can always be proven directly.
        apply True.intro
      case inr h12 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- Implications on the right can always be decomposed.
        intro h13
        -- True on the right can always be proven directly.
        apply True.intro
  case inr h14 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h15
    -- True on the right can always be proven directly.
    apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_121417936610314674196884530560 : ((((False ∨ (p5 ∧ (((((p2 → p5) ∨ ((p1 ∧ (p4 → (p1 → p5))) → p1)) ∨ (p5 → True)) → p2) ∨ False))) ∨ True) → p2) → (p2 ∨ p4)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h2 : ((False ∨ (p5 ∧ (((((p2 → p5) ∨ ((p1 ∧ (p4 → (p1 → p5))) → p1)) ∨ (p5 → True)) → p2) ∨ False))) ∨ True) := by
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h3 := h1 h2
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- One of the premise coincides with the conclusion.
  exact h3



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_180833620975598184368135512326 : (((p2 → (p4 → p1)) ∧ ((True ∨ (((p2 ∧ p4) ∨ p4) ∧ p1)) ∧ p4)) → ((((((True ∨ p1) → p5) ∨ p2) ∧ (p2 ∧ p1)) ∨ p2) ∨ True)) := by
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
      -- Conjunctions on the left can always be decomposed.
      let h11 := h10.left
      let h12 := h10.right
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
theorem thm_5_vars_191338856666772320918228619144 : (((p5 ∧ p3) ∨ (True ∧ (p5 ∧ ((True → p4) → False)))) ∨ (p2 → (((p5 → (((True ∨ p4) → False) → (False ∨ p2))) ∨ (p1 ∧ True)) ∨ p5))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h2
  -- Implications on the right can always be decomposed.
  intro h3
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_52823249948428082075931915452 : (((((True → p2) → (p2 → True)) → ((False → False) ∧ (p5 ∨ (p5 ∨ p4)))) → ((((p2 ∨ p3) → ((p1 → p4) ∧ p5)) → p4) ∨ True)) ∨ p4) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



