variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_42417126595551892806769122360 : (((p5 ∧ ((p1 ∧ (False ∨ (p5 ∨ ((p2 ∨ (((p2 ∧ ((p5 ∨ False) ∧ (True ∨ p3))) ∨ (p4 ∨ p2)) → False)) ∨ p1)))) → p4)) ∨ p2) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_983515663438786086779054810520 : (((p1 ∧ (((p5 ∨ p5) → (p5 ∧ p2)) ∧ ((((False ∧ ((((p5 ∧ (p5 → p3)) → p1) → p3) → (p2 → False))) ∨ p1) → p3) ∨ False))) → p3) ∧ True) := by
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
    -- We want to use the implication h6 based on <expert-advice>. So we show its premise.
    have h7 : ((False ∧ ((((p5 ∧ (p5 → p3)) → p1) → p3) → (p2 → False))) ∨ p1) := by
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- One of the premise coincides with the conclusion.
      exact h2
    -- We have shown the premise of h6, we can now drive its conclusion.
    let h8 := h6 h7
    -- One of the premise coincides with the conclusion.
    exact h8
  case inr h9 =>
    -- False on the left can always be used.
    apply False.elim h9
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_607153631854140439367117989709 : ((((((((p2 → (p4 ∨ p4)) ∨ True) → True) ∧ (((((p1 ∨ p5) → (p1 → p2)) ∨ (p1 ∧ (p4 → False))) → p1) → p2)) ∧ p4) ∨ p3) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_49713229230849873309967027611 : (((True ∧ ((p2 ∨ ((p5 ∨ p3) ∨ ((p2 ∧ (p2 → ((p2 ∨ p5) ∧ p5))) → True))) ∧ ((p2 → False) ∧ p2))) → ((p3 ∨ True) ∧ p5)) ∨ p5) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- Conjunctions on the left can always be decomposed.
  let h4 := h3.left
  let h5 := h3.right
  -- Disjunctions on the left can always be decomposed.
  cases h4
  case inl h6 =>
    -- Conjunctions on the left can always be decomposed.
    let h7 := h5.left
    let h8 := h5.right
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro
  case inr h9 =>
    -- Disjunctions on the left can always be decomposed.
    cases h9
    case inl h10 =>
      -- Disjunctions on the left can always be decomposed.
      cases h10
      case inl h11 =>
        -- Conjunctions on the left can always be decomposed.
        let h12 := h5.left
        let h13 := h5.right
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- True on the right can always be proven directly.
        apply True.intro
      case inr h14 =>
        -- Conjunctions on the left can always be decomposed.
        let h15 := h5.left
        let h16 := h5.right
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- One of the premise coincides with the conclusion.
        exact h14
    case inr h17 =>
      -- Conjunctions on the left can always be decomposed.
      let h18 := h5.left
      let h19 := h5.right
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- True on the right can always be proven directly.
      apply True.intro
  -- Conjunctions on the left can always be decomposed.
  let h20 := h1.left
  let h21 := h1.right
  -- Conjunctions on the left can always be decomposed.
  let h22 := h21.left
  let h23 := h21.right
  -- Disjunctions on the left can always be decomposed.
  cases h22
  case inl h24 =>
    -- Conjunctions on the left can always be decomposed.
    let h25 := h23.left
    let h26 := h23.right
    -- We want to use the implication h25 based on <expert-advice>. So we show its premise.
    have h27 : p2 := by
      -- One of the premise coincides with the conclusion.
      exact h26
    -- We have shown the premise of h25, we can now drive its conclusion.
    let h28 := h25 h27
    -- False on the left can always be used.
    apply False.elim h28
  case inr h29 =>
    -- Disjunctions on the left can always be decomposed.
    cases h29
    case inl h30 =>
      -- Disjunctions on the left can always be decomposed.
      cases h30
      case inl h31 =>
        -- Conjunctions on the left can always be decomposed.
        let h32 := h23.left
        let h33 := h23.right
        -- One of the premise coincides with the conclusion.
        exact h31
      case inr h34 =>
        -- Conjunctions on the left can always be decomposed.
        let h35 := h23.left
        let h36 := h23.right
        -- We want to use the implication h35 based on <expert-advice>. So we show its premise.
        have h37 : p2 := by
          -- One of the premise coincides with the conclusion.
          exact h36
        -- We have shown the premise of h35, we can now drive its conclusion.
        let h38 := h35 h37
        -- False on the left can always be used.
        apply False.elim h38
    case inr h39 =>
      -- Conjunctions on the left can always be decomposed.
      let h40 := h23.left
      let h41 := h23.right
      -- We want to use the implication h40 based on <expert-advice>. So we show its premise.
      have h42 : p2 := by
        -- One of the premise coincides with the conclusion.
        exact h41
      -- We have shown the premise of h40, we can now drive its conclusion.
      let h43 := h40 h42
      -- False on the left can always be used.
      apply False.elim h43



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_786969366591234051433066377162 : (((p4 ∨ ((p4 ∧ False) ∧ ((((p2 → True) ∧ p1) → p4) → (p5 ∧ ((((p2 ∨ False) ∧ p1) ∨ p4) ∨ ((p1 → (p3 ∧ p2)) ∧ False)))))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_683912422540799385629043021289 : (((((((((p2 ∧ p1) ∨ True) ∨ (True ∧ (p5 → (p1 ∧ (p1 ∨ p3))))) → p3) ∧ p3) → False) ∨ (p2 → (p2 ∨ (p1 ∧ (p2 ∧ p5))))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_324160211384879916710916375889 : (p5 ∨ ((((((p2 → p3) → (True → False)) ∧ p3) ∨ p5) ∨ p5) ∨ (p1 ∨ (True ∨ ((p2 ∨ (p1 ∧ (p5 ∧ p2))) ∨ ((False → p5) → p2)))))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_33179039560397624410928424055 : ((p3 ∨ (p5 ∨ (True ∧ ((((False ∨ ((p2 ∧ p4) → p1)) → False) ∨ ((p5 ∧ (False ∨ False)) → ((True → p2) ∧ p3))) ∨ (False ∨ False))))) ∧ True) := by
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
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
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
  -- Disjunctions on the left can always be decomposed.
  cases h4
  case inl h5 =>
    -- False on the left can always be used.
    apply False.elim h5
  case inr h6 =>
    -- False on the left can always be used.
    apply False.elim h6
  -- Conjunctions on the left can always be decomposed.
  let h7 := h1.left
  let h8 := h1.right
  -- Disjunctions on the left can always be decomposed.
  cases h8
  case inl h9 =>
    -- False on the left can always be used.
    apply False.elim h9
  case inr h10 =>
    -- False on the left can always be used.
    apply False.elim h10
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_654768470418070601800293274951 : (((((((p4 → (p1 ∨ (p3 ∧ ((p4 ∧ (True ∧ p2)) → True)))) → ((p1 ∨ p2) ∨ (True ∨ (p1 ∨ p4)))) → p3) → p2) ∨ (True → True)) ∨ p3) ∧ True) := by
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
theorem thm_5_vars_345530107179779438339819809208 : (p3 → (((p5 → (((p3 ∨ ((p5 ∨ p4) ∧ False)) ∨ p4) → p4)) ∨ (p5 ∨ (((p1 → False) → p1) → (((False → p4) → p5) → p5)))) ∨ p4)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h2
  -- Implications on the right can always be decomposed.
  intro h3
  -- We want to use the implication h3 based on <expert-advice>. So we show its premise.
  have h4 : (False → p4) := by
    -- Implications on the right can always be decomposed.
    intro h5
    -- False on the left can always be used.
    apply False.elim h5
  -- We have shown the premise of h3, we can now drive its conclusion.
  let h6 := h3 h4
  -- One of the premise coincides with the conclusion.
  exact h6



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_217873754955903254213003217470 : (((p1 → (False ∧ p2)) → p5) → (p5 → (((p3 ∨ (p1 → (True → (((((False ∨ p1) → p5) → p5) ∧ p3) ∧ p4)))) ∨ (p1 → p5)) ∨ p5))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_60070478453083292547386246921 : (((p2 ∨ p3) → ((p2 ∨ (p2 ∧ ((p2 ∨ p1) ∨ ((False ∧ p1) ∧ (((p1 ∧ (((p1 ∧ False) → p4) → True)) → p2) → p3))))) ∨ True)) ∨ False) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
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
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_57428138188954018063655014805 : (((p3 ∨ (p1 ∧ True)) ∨ (((p4 → (p1 → ((True ∧ p2) ∨ (True ∨ p5)))) ∧ ((((p1 ∧ (True → False)) ∧ p1) ∨ False) → p2)) ∧ p3)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_568964671728575455383323707 : ((((p4 → ((((p4 ∧ p2) ∨ (p3 ∨ (p4 ∨ (((p1 ∨ p3) ∧ (p2 ∧ p2)) ∨ False)))) → p2) ∧ (p4 ∨ p4))) ∧ p4) → p1) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_229023585338327630054325167850 : ((p5 ∨ (p5 ∧ p4)) ∨ ((p5 → (((p5 ∨ (p1 ∨ True)) ∨ p3) → (((((p5 ∧ p4) ∧ True) → (p5 → False)) → p1) ∨ p5))) ∨ (p3 ∨ p5))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
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
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- One of the premise coincides with the conclusion.
      exact h1
    case inr h5 =>
      -- Disjunctions on the left can always be decomposed.
      cases h5
      case inl h6 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- One of the premise coincides with the conclusion.
        exact h1
      case inr h7 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- One of the premise coincides with the conclusion.
        exact h1
  case inr h8 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_322333620078483435306975568756 : (p5 ∨ (((False ∧ (True ∧ (p5 ∨ ((((p1 ∧ (p4 → (p3 → (p4 ∨ p1)))) ∧ p1) ∧ p5) ∨ ((p4 ∨ p2) ∧ False))))) ∨ (False → p3)) ∨ p4)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_260741538006596799752228002066 : ((p3 → p4) → ((p3 ∨ p3) ∨ ((((p5 ∧ False) → (p1 ∨ (False ∧ False))) ∧ (p4 → p4)) → ((p4 ∧ ((p3 ∨ (p1 ∧ p2)) → False)) ∨ True)))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h2
  -- Conjunctions on the left can always be decomposed.
  let h3 := h2.left
  let h4 := h2.right
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_60765376528763473463043331058 : ((True ∧ ((True ∧ p4) ∨ ((p3 ∨ ((p4 ∧ ((p2 ∨ (p2 ∨ (True ∧ p5))) ∨ (p1 ∨ p3))) → p2)) → ((p4 → p3) ∨ (True ∧ p3))))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_166555786207061818727263919867 : ((p5 ∨ ((p1 ∧ p3) ∧ ((((True → p3) ∨ (p3 ∨ p4)) ∧ ((p5 ∧ p5) ∧ p5)) → False))) ∨ (True ∨ ((p3 ∨ p3) ∧ (True → (p3 ∨ p1))))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_256655969453282469877221384053 : ((p1 ∨ False) → (((((((p1 ∨ True) ∨ p3) → (p4 ∨ (p5 ∨ ((False ∨ True) ∧ p2)))) ∧ p1) ∨ p1) ∧ p2) ∨ ((False ∨ p5) ∨ (True ∨ True)))) := by
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
    -- True on the right can always be proven directly.
    apply True.intro
  case inr h3 =>
    -- False on the left can always be used.
    apply False.elim h3



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_68381717337363885823221685451 : ((p3 → ((False ∨ (p5 ∨ (p2 ∨ p5))) ∨ ((False ∨ True) ∨ ((((p3 ∧ (p3 → p4)) ∨ True) ∧ p2) ∨ ((False → (p3 ∨ p3)) → p2))))) ∨ p3) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_83170564360943451904919829360 : (((p2 → (p2 → (((p3 ∨ ((p4 → p3) → False)) ∨ ((True ∧ False) → p1)) ∨ ((p1 ∨ p5) → p5)))) → (True ∧ (False ∧ (p3 → False)))) → False) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h2 : (p2 → (p2 → (((p3 ∨ ((p4 → p3) → False)) ∨ ((True ∧ False) → p1)) ∨ ((p1 ∨ p5) → p5)))) := by
    -- Implications on the right can always be decomposed.
    intro h3
    -- Implications on the right can always be decomposed.
    intro h4
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h5
    -- Conjunctions on the left can always be decomposed.
    let h6 := h5.left
    let h7 := h5.right
    -- False on the left can always be used.
    apply False.elim h7
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h8 := h1 h2
  -- We need to get the right conjuct of h8 based on <expert-advice>.
  let h9 := h8.right
  -- We need to get the left conjuct of h9 based on <expert-advice>.
  let h10 := h9.left
  -- False on the left can always be used.
  apply False.elim h10



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_249171598272520210642109647215 : ((p4 ∨ p3) ∨ ((False ∨ ((p1 ∨ ((((p1 → ((p5 ∨ p1) ∨ p5)) → p2) ∨ ((p1 ∨ False) ∨ p1)) ∨ ((False ∧ p4) → p3))) ∨ p5)) ∨ False)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
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
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- False on the left can always be used.
  apply False.elim h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_174096477400432646839450747710 : ((((p1 ∨ ((p3 → True) ∧ p3)) ∨ ((p5 ∨ (False ∨ p5)) ∨ p3)) ∧ (True → False)) → ((p3 ∨ (((False → True) ∧ (p5 ∧ p2)) ∨ False)) ∨ p3)) := by
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
      -- We want to use the implication h3 based on <expert-advice>. So we show its premise.
      have h6 : True := by
        -- True on the right can always be proven directly.
        apply True.intro
      -- We have shown the premise of h3, we can now drive its conclusion.
      let h7 := h3 h6
      -- False on the left can always be used.
      apply False.elim h7
    case inr h8 =>
      -- Conjunctions on the left can always be decomposed.
      let h9 := h8.left
      let h10 := h8.right
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- One of the premise coincides with the conclusion.
      exact h10
  case inr h11 =>
    -- Disjunctions on the left can always be decomposed.
    cases h11
    case inl h12 =>
      -- Disjunctions on the left can always be decomposed.
      cases h12
      case inl h13 =>
        -- We want to use the implication h3 based on <expert-advice>. So we show its premise.
        have h14 : True := by
          -- True on the right can always be proven directly.
          apply True.intro
        -- We have shown the premise of h3, we can now drive its conclusion.
        let h15 := h3 h14
        -- False on the left can always be used.
        apply False.elim h15
      case inr h16 =>
        -- Disjunctions on the left can always be decomposed.
        cases h16
        case inl h17 =>
          -- False on the left can always be used.
          apply False.elim h17
        case inr h18 =>
          -- We want to use the implication h3 based on <expert-advice>. So we show its premise.
          have h19 : True := by
            -- True on the right can always be proven directly.
            apply True.intro
          -- We have shown the premise of h3, we can now drive its conclusion.
          let h20 := h3 h19
          -- False on the left can always be used.
          apply False.elim h20
    case inr h21 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- One of the premise coincides with the conclusion.
      exact h21



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_358215089934531385395039272247 : (p5 → (p4 ∨ (((p4 ∧ ((((((p2 ∧ False) ∧ p2) ∨ (p4 → p4)) ∨ (((p3 ∧ p2) ∨ True) ∧ (p2 ∧ p3))) ∨ p1) → p2)) ∧ p1) ∨ True))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_118576202390043446508671639453 : ((p4 ∨ (((((p4 → (p3 → p3)) ∨ p4) → (p3 → (((False ∨ p3) ∧ True) → True))) → ((p2 → (p5 ∧ p4)) ∧ p3)) ∨ True)) ∨ (p3 → p3)) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_243026377458749479099155903096 : ((p4 → True) ∧ (p4 → (((((((p2 → p3) → True) ∧ False) → p1) ∧ p2) ∨ (p3 → (p5 → p5))) → (((p2 ∧ p1) → (p2 ∧ p5)) ∨ p4)))) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro
  -- Implications on the right can always be decomposed.
  intro h2
  -- Implications on the right can always be decomposed.
  intro h3
  -- Disjunctions on the left can always be decomposed.
  cases h3
  case inl h4 =>
    -- Conjunctions on the left can always be decomposed.
    let h5 := h4.left
    let h6 := h4.right
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h2
  case inr h7 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_666078157325663617614078450325 : ((((((((((p5 ∨ p5) → (False → p1)) → p2) → ((p5 → p5) ∧ False)) ∨ p3) ∨ (p3 ∨ p4)) ∧ (True ∧ p4)) ∧ ((p1 ∧ False) ∧ p5)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_609307921741890569357659243142 : ((((((p3 ∨ p2) ∧ ((p4 ∨ False) ∧ (False ∨ (((((p4 ∨ (True → p1)) → (True ∨ p1)) ∧ p3) → False) ∨ (p1 ∨ p5))))) ∨ True) ∨ p5) ∨ p3) ∧ True) := by
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
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_669922525144128103797385508401 : ((((((p1 ∧ (False ∧ (p2 ∧ p4))) → ((p5 ∧ p4) → p1)) ∧ ((((p3 → (p1 → p4)) ∧ p3) → p2) ∨ p1)) ∨ (p3 ∨ (True ∨ True))) ∨ p1) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
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
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_81893889355641997798679367446 : ((((p1 ∨ ((p4 ∧ p3) ∨ ((p5 ∨ ((p1 ∧ ((False ∨ (p4 ∨ p1)) ∧ False)) ∨ True)) → p5))) ∨ (p2 ∨ True)) → (p3 ∧ (False ∧ p2))) → p5) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h2 : ((p1 ∨ ((p4 ∧ p3) ∨ ((p5 ∨ ((p1 ∧ ((False ∨ (p4 ∨ p1)) ∧ False)) ∨ True)) → p5))) ∨ (p2 ∨ True)) := by
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
  -- False on the left can always be used.
  apply False.elim h5



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_49951046127958078157700845667 : ((((p3 ∧ ((((p1 ∧ p5) ∧ (p5 ∧ (p4 ∨ True))) ∨ p1) ∨ (p5 ∧ (p3 ∧ p4)))) ∨ (p1 ∨ True)) ∧ (True ∨ ((p1 ∨ p2) ∧ p1))) ∨ p5) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_322268488694280735472177128565 : (p5 ∨ (((False ∨ ((p4 ∧ (((p5 ∧ p2) ∨ ((p5 ∧ p1) → (False ∧ p2))) ∧ p1)) ∧ ((p1 ∨ False) ∧ ((False ∧ p5) ∨ True)))) ∨ p4) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_136893460091135928189906660893 : (((p3 ∨ p5) ∨ (((((p4 ∧ p4) → p5) ∨ (p4 → (False → p5))) ∨ ((p5 ∨ p2) ∧ p4)) → (p1 ∨ (p2 → p2)))) ∨ (p2 ∨ (p5 ∨ p2))) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
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
      -- One of the premise coincides with the conclusion.
      exact h4
    case inr h5 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Implications on the right can always be decomposed.
      intro h6
      -- One of the premise coincides with the conclusion.
      exact h6
  case inr h7 =>
    -- Conjunctions on the left can always be decomposed.
    let h8 := h7.left
    let h9 := h7.right
    -- Disjunctions on the left can always be decomposed.
    cases h8
    case inl h10 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Implications on the right can always be decomposed.
      intro h11
      -- One of the premise coincides with the conclusion.
      exact h11
    case inr h12 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Implications on the right can always be decomposed.
      intro h13
      -- One of the premise coincides with the conclusion.
      exact h13



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_136508894675135352326043600198 : (((p3 ∧ (p1 ∧ p5)) ∧ ((((p5 ∧ ((p5 ∨ True) → False)) ∧ (p5 ∧ True)) → (((True ∧ p3) ∨ True) ∨ p2)) ∧ p5)) ∨ (False → (p5 → True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_950310257144259059645120796727 : (((((p2 → p4) → p1) ∧ ((((p5 → p4) ∧ (p5 ∨ p1)) ∧ (True → (False ∧ ((False ∨ p2) ∨ True)))) ∧ ((p4 ∨ p3) ∧ (p1 ∧ p3)))) → p5) ∧ True) := by
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
  let h8 := h6.left
  let h9 := h6.right
  -- Disjunctions on the left can always be decomposed.
  cases h9
  case inl h10 =>
    -- Conjunctions on the left can always be decomposed.
    let h11 := h5.left
    let h12 := h5.right
    -- Disjunctions on the left can always be decomposed.
    cases h11
    case inl h13 =>
      -- Conjunctions on the left can always be decomposed.
      let h14 := h12.left
      let h15 := h12.right
      -- One of the premise coincides with the conclusion.
      exact h10
    case inr h16 =>
      -- Conjunctions on the left can always be decomposed.
      let h17 := h12.left
      let h18 := h12.right
      -- One of the premise coincides with the conclusion.
      exact h10
  case inr h19 =>
    -- Conjunctions on the left can always be decomposed.
    let h20 := h5.left
    let h21 := h5.right
    -- Disjunctions on the left can always be decomposed.
    cases h20
    case inl h22 =>
      -- Conjunctions on the left can always be decomposed.
      let h23 := h21.left
      let h24 := h21.right
      -- We want to use the implication h7 based on <expert-advice>. So we show its premise.
      have h25 : True := by
        -- True on the right can always be proven directly.
        apply True.intro
      -- We have shown the premise of h7, we can now drive its conclusion.
      let h26 := h7 h25
      -- We need to get the left conjuct of h26 based on <expert-advice>.
      let h27 := h26.left
      -- False on the left can always be used.
      apply False.elim h27
    case inr h28 =>
      -- Conjunctions on the left can always be decomposed.
      let h29 := h21.left
      let h30 := h21.right
      -- We want to use the implication h7 based on <expert-advice>. So we show its premise.
      have h31 : True := by
        -- True on the right can always be proven directly.
        apply True.intro
      -- We have shown the premise of h7, we can now drive its conclusion.
      let h32 := h7 h31
      -- We need to get the left conjuct of h32 based on <expert-advice>.
      let h33 := h32.left
      -- False on the left can always be used.
      apply False.elim h33
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_135097397505452682443183261312 : ((((((p3 ∧ p1) ∧ p5) ∨ (p4 ∨ False)) ∧ (p3 → ((((p1 ∨ False) ∨ False) ∧ p5) ∨ (p5 ∨ False)))) ∨ (p1 ∨ p1)) ∨ ((p4 ∧ p1) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_165036419419991838653814583953 : ((((p2 ∧ p2) ∧ (((((p2 ∨ p1) ∨ ((p5 ∧ p3) ∨ p4)) → p1) ∨ p2) → True)) → p5) ∨ (p1 → (p3 → ((p4 ∧ (p2 ∧ False)) → p3)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Implications on the right can always be decomposed.
  intro h3
  -- Conjunctions on the left can always be decomposed.
  let h4 := h3.left
  let h5 := h3.right
  -- Conjunctions on the left can always be decomposed.
  let h6 := h5.left
  let h7 := h5.right
  -- False on the left can always be used.
  apply False.elim h7



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_133914773843616854965831891179 : (((p3 ∨ ((p4 ∨ p2) ∨ (((True → (False → ((p2 ∧ p2) → p3))) → (p4 → (p5 ∨ False))) → (p3 ∧ p4)))) ∧ p5) ∨ (False → (p3 → p4))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_629916451374478318462669992805 : (((((((p2 ∨ (False → False)) → (True ∧ p3)) ∧ (((((p5 ∨ (p3 ∨ p2)) ∨ (False → (p4 ∨ p2))) ∨ True) → p2) → p3)) ∨ p1) → p5) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_165599978734636379045763833848 : (((((p1 ∧ (p4 ∨ p4)) → p2) ∧ (p5 → False)) → ((p1 ∨ p4) → (p4 → (p3 ∨ p5)))) ∨ ((p1 ∧ (True → False)) → (p2 ∨ (p4 ∧ False)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- We want to use the implication h3 based on <expert-advice>. So we show its premise.
  have h4 : True := by
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h3, we can now drive its conclusion.
  let h5 := h3 h4
  -- False on the left can always be used.
  apply False.elim h5



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_136016239101750953820968592465 : ((((p2 ∧ ((p5 → p1) → ((p5 ∧ p2) ∧ p1))) ∨ p1) → (((p1 → p5) → (p2 ∨ ((p5 → p3) ∨ p4))) ∨ p1)) ∨ ((p1 → p5) ∧ False)) := by
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
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Implications on the right can always be decomposed.
    intro h5
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- One of the premise coincides with the conclusion.
    exact h3
  case inr h6 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h6



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_215444882397734891682509584557 : ((p3 ∧ ((True → p3) → False)) ∨ (((False ∨ (p1 ∨ (((p4 ∧ (p3 ∧ (p4 ∧ (p4 ∧ p3)))) ∧ p1) ∨ p1))) ∨ p1) ∨ ((True → False) → p1))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
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
  -- False on the left can always be used.
  apply False.elim h3



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_208126675111349770570879159821 : ((((p4 ∨ p5) ∨ True) → (False ∨ False)) → (p2 ∧ ((((p3 ∧ (p4 ∧ ((((p1 ∨ p3) → True) ∧ p3) ∨ (p5 ∨ p3)))) ∧ p2) → p1) ∨ p3))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h2 : ((p4 ∨ p5) ∨ True) := by
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h3 := h1 h2
  -- Disjunctions on the left can always be decomposed.
  cases h3
  case inl h4 =>
    -- False on the left can always be used.
    apply False.elim h4
  case inr h5 =>
    -- False on the left can always be used.
    apply False.elim h5
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h6 : ((p4 ∨ p5) ∨ True) := by
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h7 := h1 h6
  -- Disjunctions on the left can always be decomposed.
  cases h7
  case inl h8 =>
    -- False on the left can always be used.
    apply False.elim h8
  case inr h9 =>
    -- False on the left can always be used.
    apply False.elim h9



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_178316325239056669095403693847 : ((((((p4 ∨ (p3 → p5)) ∧ (p1 → p4)) ∨ p3) → False) ∨ (False → False)) ∨ ((p4 ∧ ((p2 ∨ True) ∨ (False → (p1 ∨ True)))) → (p1 → True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_350277513424164023689206822661 : (p4 → ((p5 ∧ (((p1 ∧ (((p1 → ((p3 ∨ p4) ∧ True)) → (((p4 → p5) → False) ∧ True)) ∨ p3)) ∨ p1) ∨ (p3 ∨ (p4 → True)))) ∨ p4)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_42351522457533990035943013979 : (((p3 ∧ (((p3 → p5) ∨ (p2 ∨ p2)) → (p5 ∨ ((((True ∨ True) ∨ ((p4 ∧ True) ∨ p5)) ∨ (p3 ∨ p4)) → (p4 ∧ p1))))) ∨ True) ∨ p5) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_134765110457515878146537777856 : ((((p1 → p1) → (p4 ∨ (False ∨ (False ∨ (p2 ∧ (p3 ∧ (((p3 → p4) ∨ (p4 ∨ (p4 → p2))) → False))))))) → False) ∨ ((False → p2) ∨ p4)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_710328985389654684157267095583 : (((((((p5 ∧ p2) → p5) ∧ p5) → False) ∧ (p2 ∨ (p2 ∧ (((p1 ∧ False) → p1) ∨ ((True ∨ (False → (p5 ∨ (True → True)))) → p3))))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_185886626938478134873052911925 : (((((p5 ∧ p2) ∨ (False → (p5 → p2))) ∧ (p3 ∨ p2)) ∧ p1) → ((p4 ∨ (p3 → (False ∨ p4))) → ((p3 → (True → p4)) ∨ (p4 ∧ p1)))) := by
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
    -- Conjunctions on the left can always be decomposed.
    let h6 := h4.left
    let h7 := h4.right
    -- Disjunctions on the left can always be decomposed.
    cases h6
    case inl h8 =>
      -- Conjunctions on the left can always be decomposed.
      let h9 := h8.left
      let h10 := h8.right
      -- Disjunctions on the left can always be decomposed.
      cases h7
      case inl h11 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- Conjunctions on the right can always be decomposed.
        apply And.intro
        -- One of the premise coincides with the conclusion.
        exact h3
        -- One of the premise coincides with the conclusion.
        exact h5
      case inr h12 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- Conjunctions on the right can always be decomposed.
        apply And.intro
        -- One of the premise coincides with the conclusion.
        exact h3
        -- One of the premise coincides with the conclusion.
        exact h5
    case inr h13 =>
      -- Disjunctions on the left can always be decomposed.
      cases h7
      case inl h14 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- Conjunctions on the right can always be decomposed.
        apply And.intro
        -- One of the premise coincides with the conclusion.
        exact h3
        -- One of the premise coincides with the conclusion.
        exact h5
      case inr h15 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- Conjunctions on the right can always be decomposed.
        apply And.intro
        -- One of the premise coincides with the conclusion.
        exact h3
        -- One of the premise coincides with the conclusion.
        exact h5
  case inr h16 =>
    -- Conjunctions on the left can always be decomposed.
    let h17 := h1.left
    let h18 := h1.right
    -- Conjunctions on the left can always be decomposed.
    let h19 := h17.left
    let h20 := h17.right
    -- Disjunctions on the left can always be decomposed.
    cases h19
    case inl h21 =>
      -- Conjunctions on the left can always be decomposed.
      let h22 := h21.left
      let h23 := h21.right
      -- Disjunctions on the left can always be decomposed.
      cases h20
      case inl h24 =>
        -- We want to use the implication h16 based on <expert-advice>. So we show its premise.
        have h25 : p3 := by
          -- One of the premise coincides with the conclusion.
          exact h24
        -- We have shown the premise of h16, we can now drive its conclusion.
        let h26 := h16 h25
        -- Disjunctions on the left can always be decomposed.
        cases h26
        case inl h27 =>
          -- False on the left can always be used.
          apply False.elim h27
        case inr h28 =>
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- Conjunctions on the right can always be decomposed.
          apply And.intro
          -- One of the premise coincides with the conclusion.
          exact h28
          -- One of the premise coincides with the conclusion.
          exact h18
      case inr h29 =>
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- Implications on the right can always be decomposed.
        intro h30
        -- Implications on the right can always be decomposed.
        intro h31
        -- We want to use the implication h16 based on <expert-advice>. So we show its premise.
        have h32 : p3 := by
          -- One of the premise coincides with the conclusion.
          exact h30
        -- We have shown the premise of h16, we can now drive its conclusion.
        let h33 := h16 h32
        -- Disjunctions on the left can always be decomposed.
        cases h33
        case inl h34 =>
          -- False on the left can always be used.
          apply False.elim h34
        case inr h35 =>
          -- One of the premise coincides with the conclusion.
          exact h35
    case inr h36 =>
      -- Disjunctions on the left can always be decomposed.
      cases h20
      case inl h37 =>
        -- We want to use the implication h16 based on <expert-advice>. So we show its premise.
        have h38 : p3 := by
          -- One of the premise coincides with the conclusion.
          exact h37
        -- We have shown the premise of h16, we can now drive its conclusion.
        let h39 := h16 h38
        -- Disjunctions on the left can always be decomposed.
        cases h39
        case inl h40 =>
          -- False on the left can always be used.
          apply False.elim h40
        case inr h41 =>
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- Conjunctions on the right can always be decomposed.
          apply And.intro
          -- One of the premise coincides with the conclusion.
          exact h41
          -- One of the premise coincides with the conclusion.
          exact h18
      case inr h42 =>
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- Implications on the right can always be decomposed.
        intro h43
        -- Implications on the right can always be decomposed.
        intro h44
        -- We want to use the implication h16 based on <expert-advice>. So we show its premise.
        have h45 : p3 := by
          -- One of the premise coincides with the conclusion.
          exact h43
        -- We have shown the premise of h16, we can now drive its conclusion.
        let h46 := h16 h45
        -- Disjunctions on the left can always be decomposed.
        cases h46
        case inl h47 =>
          -- False on the left can always be used.
          apply False.elim h47
        case inr h48 =>
          -- One of the premise coincides with the conclusion.
          exact h48



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_56579822341886217327128887502 : (((False → (p2 → (True ∨ p4))) → ((((p1 ∨ p4) ∨ False) ∨ ((p4 → p1) ∧ (p2 ∧ (p3 ∧ p5)))) → (p4 ∧ ((p1 ∧ False) ∨ p3)))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_205498802012496291956093951056 : (((p2 ∧ p4) ∧ (p2 ∧ (p3 ∧ p2))) ∨ ((((p1 → (p3 ∨ True)) ∨ (True ∨ (True ∨ (p1 ∨ True)))) ∧ (p5 ∨ (p1 ∨ True))) ∨ (True → p3))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
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
theorem thm_5_vars_310421159277448113795559797071 : (p2 ∨ (((((p2 → p2) ∨ p3) ∨ (p4 → p4)) → p2) → ((p3 ∧ ((((False ∧ (p2 → p2)) ∧ True) → p3) ∧ p3)) ∨ (p2 ∨ (p5 ∨ p2))))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h2 : (((p2 → p2) ∨ p3) ∨ (p4 → p4)) := by
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h3
    -- One of the premise coincides with the conclusion.
    exact h3
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h4 := h1 h2
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- One of the premise coincides with the conclusion.
  exact h4



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_158621080314012993476059191778 : ((False ∧ (p5 ∧ (((p1 ∨ p1) → False) → (True ∧ (((True ∧ p2) ∧ ((p1 ∨ p3) ∧ p5)) ∧ p5))))) ∨ ((p1 ∧ (True ∧ (p4 ∧ False))) → True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_53149007769069938525115480789 : (((((p1 ∧ ((p5 → p1) → ((p5 ∧ p1) ∧ p2))) ∨ p5) ∨ True) ∨ ((True ∧ p2) ∧ (((p3 → True) ∨ p5) → (p4 → (p4 ∧ False))))) ∨ p1) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_41818834215505523557248812911 : (((((False ∨ p3) ∨ p3) ∧ (p1 ∧ (False ∧ ((p4 ∨ (p2 ∧ ((p4 → (p3 ∧ p3)) ∧ False))) ∧ ((False ∨ p3) ∨ (False ∧ p3)))))) ∨ True) ∨ False) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_658477176301690090254325099922 : ((((p1 ∨ ((False → p2) → (False ∨ (p5 ∨ (p2 ∧ ((p5 → p2) ∨ (((p3 ∧ p4) → p5) ∧ (p5 ∨ (p2 → p5))))))))) ∨ (True → p4)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_342962646011583961783214387855 : (p2 → ((p3 → ((p5 ∨ False) ∨ p3)) ∧ (False ∨ ((p4 → (True ∨ True)) ∧ ((((p5 → p3) ∧ True) ∧ False) ∨ (False → (p3 → (p4 → p2)))))))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h2
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h2
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h3
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h4
  -- Implications on the right can always be decomposed.
  intro h5
  -- Implications on the right can always be decomposed.
  intro h6
  -- False on the left can always be used.
  apply False.elim h4



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_46750367404349759901252854095 : (((p1 → ((p2 ∨ (((p1 ∧ p2) ∨ p5) → (p3 ∨ p5))) ∨ ((p4 ∨ (True ∧ p1)) → ((p1 ∧ p4) ∨ (True ∨ p3))))) ∧ (True ∨ p5)) ∨ p1) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h2
  -- Disjunctions on the left can always be decomposed.
  cases h2
  case inl h3 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- True on the right can always be proven directly.
    apply True.intro
  case inr h4 =>
    -- Conjunctions on the left can always be decomposed.
    let h5 := h4.left
    let h6 := h4.right
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- True on the right can always be proven directly.
    apply True.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_135423184340115790904617772639 : (((p3 ∧ ((p5 ∨ (((p5 ∧ False) ∨ p5) ∨ (((True → True) → p5) → (False ∨ p2)))) ∧ p5)) ∨ (True ∧ (False → p2))) ∨ (True → (p3 ∧ p5))) := by
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
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_233797784052599528760510392350 : ((p3 ∨ (False → p4)) → (((((p4 ∧ p1) ∨ p1) ∨ p2) ∧ True) ∨ ((((True ∧ p4) ∧ p5) → (((p1 → (False ∧ False)) → True) ∧ p5)) ∨ False))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h2 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Implications on the right can always be decomposed.
    intro h3
    -- Conjunctions on the right can always be decomposed.
    apply And.intro
    -- Implications on the right can always be decomposed.
    intro h4
    -- True on the right can always be proven directly.
    apply True.intro
    -- Conjunctions on the left can always be decomposed.
    let h5 := h3.left
    let h6 := h3.right
    -- Conjunctions on the left can always be decomposed.
    let h7 := h5.left
    let h8 := h5.right
    -- One of the premise coincides with the conclusion.
    exact h6
  case inr h9 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Implications on the right can always be decomposed.
    intro h10
    -- Conjunctions on the right can always be decomposed.
    apply And.intro
    -- Implications on the right can always be decomposed.
    intro h11
    -- True on the right can always be proven directly.
    apply True.intro
    -- Conjunctions on the left can always be decomposed.
    let h12 := h10.left
    let h13 := h10.right
    -- Conjunctions on the left can always be decomposed.
    let h14 := h12.left
    let h15 := h12.right
    -- One of the premise coincides with the conclusion.
    exact h13



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_148569356690080988385262212135 : (((False ∨ (p4 ∨ ((((True ∧ p3) ∨ p3) → False) ∧ p3))) ∧ (((False ∧ p1) → (p4 ∧ p2)) → (p1 → False))) ∨ ((False → p1) ∨ (p2 → True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_137374987201188509370444592057 : ((p3 ∧ (((p2 ∨ (p3 ∧ (((p4 ∨ p1) ∧ False) ∧ False))) ∧ (p4 → p3)) ∧ ((True ∧ (p3 ∧ p4)) ∧ (p4 → p3)))) ∨ ((True ∨ False) ∨ p3)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_50696696060092675704960287883 : ((((p3 → (p3 ∨ True)) ∨ (((p4 → p5) → (True → ((p1 ∨ ((p4 ∧ False) → False)) → False))) ∨ p5)) → (((p2 → True) ∧ p5) → p5)) ∨ p2) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Conjunctions on the left can always be decomposed.
  let h3 := h2.left
  let h4 := h2.right
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h5 =>
    -- One of the premise coincides with the conclusion.
    exact h4
  case inr h6 =>
    -- Disjunctions on the left can always be decomposed.
    cases h6
    case inl h7 =>
      -- One of the premise coincides with the conclusion.
      exact h4
    case inr h8 =>
      -- One of the premise coincides with the conclusion.
      exact h8



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_64310272815514446604886109303 : ((p1 ∨ ((((p1 ∨ (p2 → (((p3 ∨ ((False ∨ p4) → False)) ∨ (True → True)) ∨ (p2 → ((True ∨ p5) ∨ p4))))) ∨ p2) ∨ p5) ∧ p1)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_192496106916740904059565357763 : ((((True ∧ (p3 → p4)) → ((p5 ∨ False) → True)) ∨ False) → (p2 ∨ (((((p3 ∧ p5) → (p3 → p5)) → p3) ∨ (True ∨ False)) ∨ (p3 → p5)))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h2 =>
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
  case inr h3 =>
    -- False on the left can always be used.
    apply False.elim h3



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_718701190959713091076278752350 : (((((p1 → p2) ∧ (p5 ∨ p2)) ∨ ((((((p3 ∨ p2) ∨ (p1 ∨ (True ∧ (True ∧ (p2 ∧ p3))))) ∨ p4) ∧ (p5 ∧ p5)) ∧ p2) ∨ p5)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_725605985589367135276506839881 : (((((p3 ∧ p4) ∧ True) ∨ (p1 ∨ (p2 → (False ∨ (((False → p3) ∧ ((((False → False) ∧ True) ∨ p3) ∧ (p1 ∨ (True ∨ p4)))) ∧ True))))) ∨ p2) ∧ True) := by
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
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h2
  -- False on the left can always be used.
  apply False.elim h2
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h3
  -- False on the left can always be used.
  apply False.elim h3
  -- True on the right can always be proven directly.
  apply True.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_116992220296261310426019826176 : (((True ∨ p1) → ((((p1 ∨ ((False ∨ False) → (False ∧ (p2 ∨ ((False ∨ p3) → False))))) ∧ p2) ∧ (p3 ∨ (p3 ∨ p4))) ∧ p5)) ∨ (False ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_37347828266519734086397258299 : (((((((p2 ∨ ((((True → (p2 → p4)) ∧ (p2 → (False ∨ (p3 ∧ p4)))) → (p1 ∧ p3)) ∧ p1)) → p4) ∧ p4) ∨ False) ∨ False) ∧ True) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_156699615452194911898803309083 : ((((((p3 → True) → ((p3 ∨ (p5 ∧ p1)) ∧ (p5 → p5))) → p4) → ((p4 ∧ p2) ∧ p4)) ∧ True) ∨ (((p1 → (p3 ∨ p3)) ∧ False) → p5)) := by
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
theorem thm_5_vars_618439778409138309798337901549 : (((((((False ∧ p5) ∨ p2) ∨ False) → ((p2 ∧ p3) ∧ (((p5 → p4) ∧ ((((p2 → p2) ∧ p2) → (False ∨ False)) ∧ False)) ∨ p3))) ∨ True) ∨ p4) ∧ True) := by
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
theorem thm_5_vars_352490752447931193666234088063 : (p4 → ((p5 ∨ (p3 ∧ p4)) → ((((p3 → p1) → ((True → (False → p4)) → ((p5 → (p2 → (p4 → (p3 ∨ p3)))) ∧ True))) ∨ p5) ∨ p2))) := by
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
    -- One of the premise coincides with the conclusion.
    exact h3
  case inr h4 =>
    -- Conjunctions on the left can always be decomposed.
    let h5 := h4.left
    let h6 := h4.right
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Implications on the right can always be decomposed.
    intro h7
    -- Implications on the right can always be decomposed.
    intro h8
    -- Conjunctions on the right can always be decomposed.
    apply And.intro
    -- Implications on the right can always be decomposed.
    intro h9
    -- Implications on the right can always be decomposed.
    intro h10
    -- Implications on the right can always be decomposed.
    intro h11
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- One of the premise coincides with the conclusion.
    exact h5
    -- True on the right can always be proven directly.
    apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_136419942007863041635677022531 : (((((p3 ∧ p3) → p3) ∨ True) → ((((p1 → (p3 ∨ (p5 ∧ p3))) ∨ p5) ∧ (((p2 ∧ p4) ∨ p1) → p5)) ∨ p2)) ∨ (p3 → (p3 ∨ False))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_340208325559564214617912918786 : (p1 → (p5 → ((((((p5 ∧ ((p3 ∧ (False → ((p5 ∧ (p2 → False)) ∨ True))) ∧ ((True ∧ p4) → False))) ∧ p2) ∧ False) ∧ p3) ∧ p3) ∨ p5))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_776495830364075589633173339374 : (((p1 ∨ (((((p3 ∨ (p2 ∨ ((p5 ∨ (p2 ∨ (p5 ∧ p1))) ∨ p1))) ∧ (p4 ∨ p5)) → p2) ∨ ((p2 ∨ (p1 ∨ p5)) ∨ True)) ∨ p3)) ∨ p1) ∧ True) := by
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
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_325050601492988578510856890986 : (p5 ∨ ((False ∨ p4) → (p5 ∨ (((((True ∧ (((False ∧ (p3 ∨ (False ∧ (p4 ∨ p1)))) ∧ p1) → False)) ∧ False) → (False ∨ p4)) → p1) ∨ p4)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h2 =>
    -- False on the left can always be used.
    apply False.elim h2
  case inr h3 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h3



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_51889417812400984284552413032 : (((((p5 ∧ ((False → (p4 → (p2 → False))) ∧ p5)) → (False ∨ (p3 → False))) → p4) ∨ (((p1 → (False → (p3 ∨ p1))) ∨ p3) ∨ p3)) ∨ p2) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- False on the left can always be used.
  apply False.elim h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_184420077066928080668323506583 : ((((p4 → (True → ((p5 ∧ p3) ∧ True))) → p4) ∧ (p2 ∧ p1)) ∨ (p4 → ((p3 ∧ (p2 ∧ p2)) → ((p5 ∨ (False ∧ (False ∧ p5))) ∨ p4)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
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
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_117140335713815234280909989073 : (((p5 → p4) → (((((True ∧ p4) → (False ∧ (p4 → True))) ∨ ((p1 → (True → p1)) ∧ ((p4 → False) ∨ p2))) ∨ p2) ∨ p5)) ∨ (False → p1)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_38166322981250759477889503832 : (((((((p4 ∧ p5) ∧ (True ∨ ((p4 → p5) → (p1 → p5)))) ∧ p5) ∨ (False ∨ ((p4 ∧ False) ∧ True))) ∨ (p4 → (False → p5))) ∧ p4) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_160685714086670107286490398836 : ((((p2 ∧ (False → False)) → ((p2 ∧ p3) ∧ False)) ∧ (True ∨ ((p5 → (p4 → (p1 ∧ p5))) ∨ p5))) → (((p2 ∨ False) ∧ (False → p1)) → p3)) := by
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
    -- Conjunctions on the left can always be decomposed.
    let h6 := h1.left
    let h7 := h1.right
    -- Disjunctions on the left can always be decomposed.
    cases h7
    case inl h8 =>
      -- We want to use the implication h6 based on <expert-advice>. So we show its premise.
      have h9 : (p2 ∧ (False → False)) := by
        -- Conjunctions on the right can always be decomposed.
        apply And.intro
        -- One of the premise coincides with the conclusion.
        exact h5
        -- Implications on the right can always be decomposed.
        intro h10
        -- False on the left can always be used.
        apply False.elim h10
      -- We have shown the premise of h6, we can now drive its conclusion.
      let h11 := h6 h9
      -- We need to get the left conjuct of h11 based on <expert-advice>.
      let h12 := h11.left
      -- We need to get the right conjuct of h12 based on <expert-advice>.
      let h13 := h12.right
      -- One of the premise coincides with the conclusion.
      exact h13
    case inr h14 =>
      -- Disjunctions on the left can always be decomposed.
      cases h14
      case inl h15 =>
        -- We want to use the implication h6 based on <expert-advice>. So we show its premise.
        have h16 : (p2 ∧ (False → False)) := by
          -- Conjunctions on the right can always be decomposed.
          apply And.intro
          -- One of the premise coincides with the conclusion.
          exact h5
          -- Implications on the right can always be decomposed.
          intro h17
          -- False on the left can always be used.
          apply False.elim h17
        -- We have shown the premise of h6, we can now drive its conclusion.
        let h18 := h6 h16
        -- We need to get the left conjuct of h18 based on <expert-advice>.
        let h19 := h18.left
        -- We need to get the right conjuct of h19 based on <expert-advice>.
        let h20 := h19.right
        -- One of the premise coincides with the conclusion.
        exact h20
      case inr h21 =>
        -- We want to use the implication h6 based on <expert-advice>. So we show its premise.
        have h22 : (p2 ∧ (False → False)) := by
          -- Conjunctions on the right can always be decomposed.
          apply And.intro
          -- One of the premise coincides with the conclusion.
          exact h5
          -- Implications on the right can always be decomposed.
          intro h23
          -- False on the left can always be used.
          apply False.elim h23
        -- We have shown the premise of h6, we can now drive its conclusion.
        let h24 := h6 h22
        -- We need to get the left conjuct of h24 based on <expert-advice>.
        let h25 := h24.left
        -- We need to get the right conjuct of h25 based on <expert-advice>.
        let h26 := h25.right
        -- One of the premise coincides with the conclusion.
        exact h26
  case inr h27 =>
    -- False on the left can always be used.
    apply False.elim h27



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_44943241864453614493041209140 : ((((True ∨ p3) ∧ ((((True → False) → (p2 → True)) ∧ p2) → ((p3 ∨ ((p5 → p1) → (((p3 → False) → False) → p3))) ∧ True))) → p5) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_192206071973191939066868335921 : ((((((p3 ∧ p2) → (p2 ∧ p2)) → p2) → p2) ∧ p4) → (((False ∨ p5) ∧ ((p3 ∧ (p4 → False)) ∨ (False → p3))) ∨ ((p1 ∨ p2) → True))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h4
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_180199474872395722993541972961 : (((((False ∨ p4) ∧ p3) → ((p5 → (False ∨ True)) ∧ (p4 ∨ True))) → p4) → ((True → p5) → ((p3 ∨ (p5 ∨ p3)) ∨ ((p5 ∧ p3) ∧ False)))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
  have h3 : True := by
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h2, we can now drive its conclusion.
  let h4 := h2 h3
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- One of the premise coincides with the conclusion.
  exact h4



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_179581706032852245172897845509 : ((p2 → (True → (((p5 ∨ True) → (False → (p2 ∨ (False ∧ True)))) → False))) ∨ ((p2 ∨ ((p2 ∨ ((p2 → p3) → (p4 ∨ p2))) ∨ False)) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_52743343510857058214351991063 : (((((True → True) ∧ (True ∧ (((p4 → p1) → False) → (False ∨ p1)))) ∨ p2) → ((p3 → p5) ∨ (((False ∧ p4) ∨ False) → (p5 ∨ p3)))) ∨ p2) := by
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
    -- Conjunctions on the left can always be decomposed.
    let h5 := h4.left
    let h6 := h4.right
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h7
    -- Disjunctions on the left can always be decomposed.
    cases h7
    case inl h8 =>
      -- Conjunctions on the left can always be decomposed.
      let h9 := h8.left
      let h10 := h8.right
      -- False on the left can always be used.
      apply False.elim h9
    case inr h11 =>
      -- False on the left can always be used.
      apply False.elim h11
  case inr h12 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h13
    -- Disjunctions on the left can always be decomposed.
    cases h13
    case inl h14 =>
      -- Conjunctions on the left can always be decomposed.
      let h15 := h14.left
      let h16 := h14.right
      -- False on the left can always be used.
      apply False.elim h15
    case inr h17 =>
      -- False on the left can always be used.
      apply False.elim h17



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_177836861799853788949020965410 : ((((((p3 ∨ (True ∨ (p5 ∨ p3))) ∧ False) ∨ (p3 → p1)) ∧ p4) ∨ p5) ∨ ((((p4 ∨ ((True ∧ True) ∧ False)) ∨ True) ∧ (p5 ∧ p5)) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_165824220734096536220843472811 : (((p3 ∨ (p2 → False)) ∧ (((p2 → ((p2 → True) → p1)) → p4) ∧ ((p5 ∨ p2) ∧ p5))) ∨ (p4 ∨ ((True ∧ False) → (p1 ∨ (p3 → p5))))) := by
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
  apply False.elim h3



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_66722434016371410428846544037 : ((True → ((p3 ∨ p1) ∨ (((p2 ∨ (False ∧ (((p5 → (True ∧ p2)) ∨ False) ∨ False))) ∨ True) ∧ ((p3 ∧ ((p5 ∧ False) → p4)) ∨ True)))) ∨ p5) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
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
theorem thm_5_vars_55969500820189142588783789578 : (((((p5 ∨ p5) ∨ p1) ∧ p5) ∨ ((p1 ∨ (p3 → ((p3 → ((p4 → p1) ∨ p3)) ∨ ((p3 ∨ False) → p5)))) ∧ (True ∧ (p3 → p3)))) ∨ p1) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
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
  -- One of the premise coincides with the conclusion.
  exact h2
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- Implications on the right can always be decomposed.
  intro h3
  -- One of the premise coincides with the conclusion.
  exact h3



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_114648562834578078740543803489 : ((((False ∨ (((p2 ∨ (p5 ∧ (False ∧ False))) ∨ True) ∨ p4)) ∧ (True ∨ (True → False))) ∨ ((p3 ∨ True) ∨ (p5 → (False → p1)))) ∨ (True ∨ p4)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_258449061586382923255794216917 : ((p5 ∨ p1) → (p1 → (((p4 → (False ∨ p2)) → ((p4 ∧ (p4 ∨ ((p1 ∧ True) ∧ ((p3 → p1) ∨ (p3 → p2))))) → (p2 ∧ p4))) ∨ p4))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h3 =>
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Implications on the right can always be decomposed.
    intro h4
    -- Implications on the right can always be decomposed.
    intro h5
    -- Conjunctions on the right can always be decomposed.
    apply And.intro
    -- Conjunctions on the left can always be decomposed.
    let h6 := h5.left
    let h7 := h5.right
    -- Disjunctions on the left can always be decomposed.
    cases h7
    case inl h8 =>
      -- We want to use the implication h4 based on <expert-advice>. So we show its premise.
      have h9 : p4 := by
        -- One of the premise coincides with the conclusion.
        exact h8
      -- We have shown the premise of h4, we can now drive its conclusion.
      let h10 := h4 h9
      -- Disjunctions on the left can always be decomposed.
      cases h10
      case inl h11 =>
        -- False on the left can always be used.
        apply False.elim h11
      case inr h12 =>
        -- One of the premise coincides with the conclusion.
        exact h12
    case inr h13 =>
      -- Conjunctions on the left can always be decomposed.
      let h14 := h13.left
      let h15 := h13.right
      -- Conjunctions on the left can always be decomposed.
      let h16 := h14.left
      let h17 := h14.right
      -- Disjunctions on the left can always be decomposed.
      cases h15
      case inl h18 =>
        -- We want to use the implication h4 based on <expert-advice>. So we show its premise.
        have h19 : p4 := by
          -- One of the premise coincides with the conclusion.
          exact h6
        -- We have shown the premise of h4, we can now drive its conclusion.
        let h20 := h4 h19
        -- Disjunctions on the left can always be decomposed.
        cases h20
        case inl h21 =>
          -- False on the left can always be used.
          apply False.elim h21
        case inr h22 =>
          -- One of the premise coincides with the conclusion.
          exact h22
      case inr h23 =>
        -- We want to use the implication h4 based on <expert-advice>. So we show its premise.
        have h24 : p4 := by
          -- One of the premise coincides with the conclusion.
          exact h6
        -- We have shown the premise of h4, we can now drive its conclusion.
        let h25 := h4 h24
        -- Disjunctions on the left can always be decomposed.
        cases h25
        case inl h26 =>
          -- False on the left can always be used.
          apply False.elim h26
        case inr h27 =>
          -- One of the premise coincides with the conclusion.
          exact h27
    -- Conjunctions on the left can always be decomposed.
    let h28 := h5.left
    let h29 := h5.right
    -- Disjunctions on the left can always be decomposed.
    cases h29
    case inl h30 =>
      -- One of the premise coincides with the conclusion.
      exact h30
    case inr h31 =>
      -- Conjunctions on the left can always be decomposed.
      let h32 := h31.left
      let h33 := h31.right
      -- Conjunctions on the left can always be decomposed.
      let h34 := h32.left
      let h35 := h32.right
      -- Disjunctions on the left can always be decomposed.
      cases h33
      case inl h36 =>
        -- One of the premise coincides with the conclusion.
        exact h28
      case inr h37 =>
        -- One of the premise coincides with the conclusion.
        exact h28
  case inr h38 =>
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Implications on the right can always be decomposed.
    intro h39
    -- Implications on the right can always be decomposed.
    intro h40
    -- Conjunctions on the right can always be decomposed.
    apply And.intro
    -- Conjunctions on the left can always be decomposed.
    let h41 := h40.left
    let h42 := h40.right
    -- Disjunctions on the left can always be decomposed.
    cases h42
    case inl h43 =>
      -- We want to use the implication h39 based on <expert-advice>. So we show its premise.
      have h44 : p4 := by
        -- One of the premise coincides with the conclusion.
        exact h43
      -- We have shown the premise of h39, we can now drive its conclusion.
      let h45 := h39 h44
      -- Disjunctions on the left can always be decomposed.
      cases h45
      case inl h46 =>
        -- False on the left can always be used.
        apply False.elim h46
      case inr h47 =>
        -- One of the premise coincides with the conclusion.
        exact h47
    case inr h48 =>
      -- Conjunctions on the left can always be decomposed.
      let h49 := h48.left
      let h50 := h48.right
      -- Conjunctions on the left can always be decomposed.
      let h51 := h49.left
      let h52 := h49.right
      -- Disjunctions on the left can always be decomposed.
      cases h50
      case inl h53 =>
        -- We want to use the implication h39 based on <expert-advice>. So we show its premise.
        have h54 : p4 := by
          -- One of the premise coincides with the conclusion.
          exact h41
        -- We have shown the premise of h39, we can now drive its conclusion.
        let h55 := h39 h54
        -- Disjunctions on the left can always be decomposed.
        cases h55
        case inl h56 =>
          -- False on the left can always be used.
          apply False.elim h56
        case inr h57 =>
          -- One of the premise coincides with the conclusion.
          exact h57
      case inr h58 =>
        -- We want to use the implication h39 based on <expert-advice>. So we show its premise.
        have h59 : p4 := by
          -- One of the premise coincides with the conclusion.
          exact h41
        -- We have shown the premise of h39, we can now drive its conclusion.
        let h60 := h39 h59
        -- Disjunctions on the left can always be decomposed.
        cases h60
        case inl h61 =>
          -- False on the left can always be used.
          apply False.elim h61
        case inr h62 =>
          -- One of the premise coincides with the conclusion.
          exact h62
    -- Conjunctions on the left can always be decomposed.
    let h63 := h40.left
    let h64 := h40.right
    -- Disjunctions on the left can always be decomposed.
    cases h64
    case inl h65 =>
      -- One of the premise coincides with the conclusion.
      exact h65
    case inr h66 =>
      -- Conjunctions on the left can always be decomposed.
      let h67 := h66.left
      let h68 := h66.right
      -- Conjunctions on the left can always be decomposed.
      let h69 := h67.left
      let h70 := h67.right
      -- Disjunctions on the left can always be decomposed.
      cases h68
      case inl h71 =>
        -- One of the premise coincides with the conclusion.
        exact h63
      case inr h72 =>
        -- One of the premise coincides with the conclusion.
        exact h63



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_205117878219447381505941559984 : ((((p4 ∨ p5) ∨ False) ∧ (False ∨ p3)) ∨ (((True ∨ False) ∧ (p4 ∨ True)) ∧ ((p5 → p5) → (p2 ∨ ((True ∧ (False ∧ (p1 ∧ False))) → p5))))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h2
  -- Conjunctions on the left can always be decomposed.
  let h3 := h2.left
  let h4 := h2.right
  -- Conjunctions on the left can always be decomposed.
  let h5 := h4.left
  let h6 := h4.right
  -- False on the left can always be used.
  apply False.elim h5



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_53987905149119333705512656828 : ((((((p2 → p2) → p4) → (p3 → (True ∨ p2))) ∨ p5) → ((True ∧ (p5 ∨ (p5 ∧ p2))) ∨ ((False → (True → (p3 ∧ p5))) → p3))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_165974498434183106941785146218 : (((p4 → False) ∧ (p5 ∨ ((((p3 → True) ∨ (True → p4)) ∨ ((True ∨ p3) ∧ p2)) → p4))) ∨ (((False ∧ (False ∨ p5)) → (False ∧ p4)) ∨ p2)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- False on the left can always be used.
  apply False.elim h2
  -- Conjunctions on the left can always be decomposed.
  let h4 := h1.left
  let h5 := h1.right
  -- False on the left can always be used.
  apply False.elim h4



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_37247896195879749853569103357 : ((((True ∧ (p4 → (((p5 ∧ ((True ∨ (False ∨ (p1 ∧ (p4 → True)))) ∨ (True ∨ p5))) ∧ (p4 ∧ p1)) ∨ (p3 ∧ False)))) ∧ p4) ∧ p4) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_894634901710451329876167029135 : ((((True → (False ∨ (((True ∧ p3) ∨ (False ∨ p2)) ∧ (((p1 → True) → (p2 ∧ ((p5 ∧ p4) ∧ True))) ∧ p3)))) ∧ (p4 ∨ (p1 → p3))) → p4) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- Disjunctions on the left can always be decomposed.
  cases h3
  case inl h4 =>
    -- One of the premise coincides with the conclusion.
    exact h4
  case inr h5 =>
    -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
    have h6 : True := by
      -- True on the right can always be proven directly.
      apply True.intro
    -- We have shown the premise of h2, we can now drive its conclusion.
    let h7 := h2 h6
    -- Disjunctions on the left can always be decomposed.
    cases h7
    case inl h8 =>
      -- False on the left can always be used.
      apply False.elim h8
    case inr h9 =>
      -- Conjunctions on the left can always be decomposed.
      let h10 := h9.left
      let h11 := h9.right
      -- Disjunctions on the left can always be decomposed.
      cases h10
      case inl h12 =>
        -- Conjunctions on the left can always be decomposed.
        let h13 := h12.left
        let h14 := h12.right
        -- Conjunctions on the left can always be decomposed.
        let h15 := h11.left
        let h16 := h11.right
        -- We want to use the implication h15 based on <expert-advice>. So we show its premise.
        have h17 : (p1 → True) := by
          -- Implications on the right can always be decomposed.
          intro h18
          -- True on the right can always be proven directly.
          apply True.intro
        -- We have shown the premise of h15, we can now drive its conclusion.
        let h19 := h15 h17
        -- We need to get the right conjuct of h19 based on <expert-advice>.
        let h20 := h19.right
        -- We need to get the left conjuct of h20 based on <expert-advice>.
        let h21 := h20.left
        -- We need to get the right conjuct of h21 based on <expert-advice>.
        let h22 := h21.right
        -- One of the premise coincides with the conclusion.
        exact h22
      case inr h23 =>
        -- Disjunctions on the left can always be decomposed.
        cases h23
        case inl h24 =>
          -- False on the left can always be used.
          apply False.elim h24
        case inr h25 =>
          -- Conjunctions on the left can always be decomposed.
          let h26 := h11.left
          let h27 := h11.right
          -- We want to use the implication h26 based on <expert-advice>. So we show its premise.
          have h28 : (p1 → True) := by
            -- Implications on the right can always be decomposed.
            intro h29
            -- True on the right can always be proven directly.
            apply True.intro
          -- We have shown the premise of h26, we can now drive its conclusion.
          let h30 := h26 h28
          -- We need to get the right conjuct of h30 based on <expert-advice>.
          let h31 := h30.right
          -- We need to get the left conjuct of h31 based on <expert-advice>.
          let h32 := h31.left
          -- We need to get the right conjuct of h32 based on <expert-advice>.
          let h33 := h32.right
          -- One of the premise coincides with the conclusion.
          exact h33
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_173414922659820397679035705987 : ((p5 → ((((p5 ∨ (True ∨ p3)) ∨ p1) → ((p5 ∨ p2) → p2)) ∨ (p1 ∧ p4))) ∨ ((p4 → (p2 → p1)) ∨ ((p5 ∧ False) → (p1 → p4)))) := by
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
  -- False on the left can always be used.
  apply False.elim h4



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_118508271238133318967859882001 : ((p3 ∨ (((p1 ∨ True) ∨ (p3 → (p3 → p4))) → (((p4 → True) → (p4 ∨ ((p4 → p2) ∨ ((p1 ∨ p4) → False)))) ∨ True))) ∨ (True ∧ False)) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
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



