variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_181272607881008877647826633465 : ((p4 ∧ (True ∧ (p1 ∧ (((True → p3) ∧ p5) → ((p4 ∧ p5) → p1))))) → (((p3 ∧ p5) ∨ ((p1 → p5) ∧ ((p2 → p1) ∨ False))) → p5)) := by
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
    -- Conjunctions on the left can always be decomposed.
    let h6 := h1.left
    let h7 := h1.right
    -- Conjunctions on the left can always be decomposed.
    let h8 := h7.left
    let h9 := h7.right
    -- Conjunctions on the left can always be decomposed.
    let h10 := h9.left
    let h11 := h9.right
    -- One of the premise coincides with the conclusion.
    exact h5
  case inr h12 =>
    -- Conjunctions on the left can always be decomposed.
    let h13 := h12.left
    let h14 := h12.right
    -- Disjunctions on the left can always be decomposed.
    cases h14
    case inl h15 =>
      -- Conjunctions on the left can always be decomposed.
      let h16 := h1.left
      let h17 := h1.right
      -- Conjunctions on the left can always be decomposed.
      let h18 := h17.left
      let h19 := h17.right
      -- Conjunctions on the left can always be decomposed.
      let h20 := h19.left
      let h21 := h19.right
      -- We want to use the implication h13 based on <expert-advice>. So we show its premise.
      have h22 : p1 := by
        -- One of the premise coincides with the conclusion.
        exact h20
      -- We have shown the premise of h13, we can now drive its conclusion.
      let h23 := h13 h22
      -- One of the premise coincides with the conclusion.
      exact h23
    case inr h24 =>
      -- False on the left can always be used.
      apply False.elim h24



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_117655558172001286803788141874 : ((p3 ∧ ((((((True → ((p2 ∨ True) ∧ True)) → p5) → ((True ∧ p4) ∨ (p3 ∨ (False ∨ p3)))) ∧ p2) → p3) → (p2 ∨ p2))) ∨ (True → True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_57489112707242357625388808310 : (((p1 → (p5 ∨ False)) ∨ ((((((p4 → (((p1 ∨ p5) ∧ p4) ∧ (p1 → p1))) ∨ (p1 → p1)) ∨ p2) ∧ p2) ∨ True) ∨ (True → p1))) ∨ False) := by
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
theorem thm_5_vars_669254383751294006399216992089 : (((((p4 ∨ ((p1 ∨ ((p1 ∧ (p1 → (False ∨ (False → (p4 ∧ (p1 ∨ p3)))))) ∨ p2)) ∨ (True ∨ p3))) → p1) ∨ ((p4 ∨ True) → p4)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_136525699819419959574222337492 : (((p5 ∨ (p4 ∨ False)) ∧ ((((p3 ∨ ((p5 ∨ (False ∧ True)) ∨ (((p3 ∨ False) ∨ p2) ∨ p3))) ∨ True) ∨ p5) ∧ p4)) ∨ (True ∨ (p4 → p4))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_138011803802267546626211823558 : ((True → ((False ∨ ((p5 ∨ (False ∨ ((False ∨ p4) ∨ ((p5 → (p2 → (p5 ∨ (p5 → p5)))) ∨ p1)))) ∨ True)) ∧ p1)) ∨ ((p3 ∧ False) → p2)) := by
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
theorem thm_5_vars_41421632585549020871208329877 : ((((p4 ∨ (False ∧ ((((p4 → p2) → p5) → (p5 ∧ p2)) ∧ (p3 → p5)))) ∨ (p3 ∨ (True → (((p3 ∨ p1) ∨ p1) ∨ True)))) ∨ p3) ∨ p3) := by
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
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_3014450927203481426881628970 : (((p5 ∧ p4) → True) → ((((p4 ∨ (p1 ∨ ((True ∧ (True ∧ (p3 ∧ (p1 ∨ p2)))) ∨ p3))) → (p2 → (p5 ∨ p2))) ∨ p4) ∨ p1)) := by
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
  -- Disjunctions on the left can always be decomposed.
  cases h2
  case inl h4 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h3
  case inr h5 =>
    -- Disjunctions on the left can always be decomposed.
    cases h5
    case inl h6 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- One of the premise coincides with the conclusion.
      exact h3
    case inr h7 =>
      -- Disjunctions on the left can always be decomposed.
      cases h7
      case inl h8 =>
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
        cases h14
        case inl h15 =>
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- One of the premise coincides with the conclusion.
          exact h3
        case inr h16 =>
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- One of the premise coincides with the conclusion.
          exact h16
      case inr h17 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- One of the premise coincides with the conclusion.
        exact h3



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_741208989678053712443322243983 : ((((p4 ∨ p2) ∨ (p1 ∨ (p5 ∧ (((p5 ∨ (((p1 → p3) ∨ False) → ((p1 → (False ∧ p4)) ∧ (False ∧ p1)))) → (True ∧ p4)) → p4)))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_737091644885132195704484391155 : ((((p3 → p3) ∧ (((p2 → p4) ∧ ((((p3 ∨ True) → p2) ∨ p1) ∨ (((True → (False ∨ (False ∧ False))) ∨ (p4 ∧ p4)) → p5))) → p2)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_324273291799109663379285777804 : (p5 ∨ ((p3 ∧ (p1 → ((p2 → (p1 → p1)) → False))) ∨ ((p3 ∧ p3) ∨ ((((((p2 → p4) ∨ p5) → True) ∨ (p2 → p1)) → False) → p5)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h2 : ((((p2 → p4) ∨ p5) → True) ∨ (p2 → p1)) := by
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Implications on the right can always be decomposed.
    intro h3
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h4 := h1 h2
  -- False on the left can always be used.
  apply False.elim h4



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_157250305490913702927691417153 : (((((p1 ∧ p4) ∨ (p3 → (True ∧ True))) ∨ (((True ∧ p4) ∧ ((p5 → False) ∧ p2)) ∨ p2)) → p1) ∨ (((True ∧ p2) ∨ True) ∨ (p4 ∧ False))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_729963949224751780733189819159 : (((((p5 ∧ False) → p1) → ((((False ∧ (True ∨ True)) → (p2 ∨ True)) → p5) ∨ ((p4 ∨ (True ∧ (p4 ∨ True))) ∨ ((p3 ∨ False) ∧ p5)))) ∨ p3) ∧ True) := by
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
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_228812350311080282664284594892 : ((p3 ∨ (p3 ∨ False)) ∨ ((((((p3 ∧ (p2 → (p4 ∨ p2))) ∧ (True ∨ False)) ∨ ((False ∨ p2) ∧ p1)) ∨ False) ∧ p1) ∨ ((p5 → True) → True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_668509405192710474837149293112 : (((((((((False → ((p3 → p3) ∧ p1)) ∨ (p2 ∧ p1)) ∨ p2) ∧ p5) → (((True ∨ p1) ∨ p2) ∧ False)) ∧ p4) ∨ ((p2 ∧ p4) → True)) ∨ p1) ∧ True) := by
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
theorem thm_5_vars_260848520630869353675158752073 : ((p4 → True) → ((False ∨ ((p5 ∨ (((p1 → ((p1 → p1) → True)) ∧ p1) → (p4 ∧ p4))) ∨ True)) ∨ ((((p4 ∧ p4) → True) → p1) ∧ False))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_113614849817162303606724181904 : (((p5 ∨ (((p5 → p2) ∧ ((p1 → True) → (((p4 ∨ (p5 → p2)) → p3) ∧ p3))) ∨ (False ∨ (True ∨ p2)))) ∨ (True ∨ p5)) ∨ (False ∨ p1)) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_867810822820656117830722319346 : (((((True → p2) ∨ ((p2 ∧ ((((((p3 ∨ p1) ∧ (p5 ∧ (p1 ∧ p1))) ∧ p1) ∨ p4) ∧ ((True ∧ p3) → p3)) → p3)) → p2)) → False) → p3) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h1
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h2 : ((True → p2) ∨ ((p2 ∧ ((((((p3 ∨ p1) ∧ (p5 ∧ (p1 ∧ p1))) ∧ p1) ∨ p4) ∧ ((True ∧ p3) → p3)) → p3)) → p2)) := by
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h3
    -- Conjunctions on the left can always be decomposed.
    let h4 := h3.left
    let h5 := h3.right
    -- One of the premise coincides with the conclusion.
    exact h4
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h6 := h1 h2
  -- False on the left can always be used.
  apply False.elim h6
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_244928839772591926220585707452 : ((p1 ∧ p3) ∨ ((((p1 ∨ ((False → ((p5 → ((((p5 ∧ p5) ∨ p3) → p4) ∨ (p1 ∧ p2))) ∧ True)) → False)) ∧ p5) ∨ p4) ∨ (False → p4))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_341755194296324909412947400412 : (p2 → ((False ∨ (((((True ∨ (p5 ∧ p3)) ∨ p2) ∨ p3) ∧ ((p4 ∨ p4) → p5)) → (p3 ∧ ((p1 ∧ p4) ∨ (p3 ∧ p3))))) ∨ (p2 ∧ p2))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- One of the premise coincides with the conclusion.
  exact h1
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_249595487587075492277189009116 : ((p5 ∨ p3) ∨ ((((p5 ∨ True) ∧ p3) ∨ ((((p1 → (p4 → p3)) → ((((p5 → p1) ∨ p4) ∨ True) → p5)) → (p2 ∨ p3)) ∨ False)) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_54800825837375206442819243971 : (((False ∨ ((p4 ∨ p1) → (p3 → (p5 ∨ False)))) → (((((False ∧ (((p2 ∧ p1) ∧ False) ∨ p5)) ∨ p1) → (p5 ∨ p3)) ∨ False) → p2)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_58151174442930814812872446071 : (((p2 ∧ p4) ∧ (p1 ∨ (p1 ∧ (p4 ∧ ((p1 ∨ p5) ∨ (((True ∨ p1) → ((False ∧ p2) ∨ p2)) ∨ (((p3 → p1) ∧ p5) → True))))))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_66010781746236912793748802507 : ((p5 ∨ (((((p4 ∧ (((p3 ∧ ((((p3 ∨ (p3 ∨ (p2 ∨ p1))) ∨ True) ∧ False) → False)) ∧ p3) ∨ p2)) ∧ p5) → False) ∨ p4) ∧ p1)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_342789373482162555518430574390 : (p2 → (((p1 → (True → p5)) ∧ ((p5 ∨ p4) → p3)) → (True ∧ ((((p2 → (p2 ∧ p1)) ∨ (p1 → (p5 → False))) → p4) → (p1 → p4))))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- Implications on the right can always be decomposed.
  intro h3
  -- Implications on the right can always be decomposed.
  intro h4
  -- Conjunctions on the left can always be decomposed.
  let h5 := h2.left
  let h6 := h2.right
  -- We want to use the implication h3 based on <expert-advice>. So we show its premise.
  have h7 : ((p2 → (p2 ∧ p1)) ∨ (p1 → (p5 → False))) := by
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Implications on the right can always be decomposed.
    intro h8
    -- Conjunctions on the right can always be decomposed.
    apply And.intro
    -- One of the premise coincides with the conclusion.
    exact h8
    -- One of the premise coincides with the conclusion.
    exact h4
  -- We have shown the premise of h3, we can now drive its conclusion.
  let h9 := h3 h7
  -- One of the premise coincides with the conclusion.
  exact h9



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_58942099138849174532015860205 : (((p1 ∧ p5) ∨ ((((p5 ∨ ((p4 ∧ p1) → p2)) → (p1 ∧ p4)) → p4) → ((((p2 ∧ False) ∧ p2) ∧ (p4 → p2)) ∧ (p1 → p5)))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_174270108713696529173357292091 : ((((p5 → (True → (p4 → (False ∨ True)))) → (p2 ∧ True)) ∧ (p3 → (p5 ∨ p1))) → (p2 → ((p1 → (p4 ∧ p5)) → (p3 → (p2 ∧ p5))))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Implications on the right can always be decomposed.
  intro h3
  -- Implications on the right can always be decomposed.
  intro h4
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Conjunctions on the left can always be decomposed.
  let h5 := h1.left
  let h6 := h1.right
  -- One of the premise coincides with the conclusion.
  exact h2
  -- Conjunctions on the left can always be decomposed.
  let h7 := h1.left
  let h8 := h1.right
  -- We want to use the implication h8 based on <expert-advice>. So we show its premise.
  have h9 : p3 := by
    -- One of the premise coincides with the conclusion.
    exact h4
  -- We have shown the premise of h8, we can now drive its conclusion.
  let h10 := h8 h9
  -- Disjunctions on the left can always be decomposed.
  cases h10
  case inl h11 =>
    -- One of the premise coincides with the conclusion.
    exact h11
  case inr h12 =>
    -- We want to use the implication h3 based on <expert-advice>. So we show its premise.
    have h13 : p1 := by
      -- One of the premise coincides with the conclusion.
      exact h12
    -- We have shown the premise of h3, we can now drive its conclusion.
    let h14 := h3 h13
    -- We need to get the right conjuct of h14 based on <expert-advice>.
    let h15 := h14.right
    -- One of the premise coincides with the conclusion.
    exact h15



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_205656773981259273375787311890 : (((False ∨ False) ∨ ((p3 ∨ False) ∧ p3)) ∨ ((p3 → ((((False ∨ p3) → p3) ∧ True) → ((((p5 → (p1 ∨ p3)) ∧ p3) ∨ p4) ∨ p3))) ∨ p4)) := by
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
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_263457706849837759944150640136 : (True ∧ ((((((((True ∧ p5) ∨ (p2 → p4)) ∧ ((p4 ∧ p3) ∧ p3)) → p4) ∨ False) → False) ∧ ((p1 ∧ False) → True)) → (p4 ∧ (p5 ∧ p3)))) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
  have h4 : (((((True ∧ p5) ∨ (p2 → p4)) ∧ ((p4 ∧ p3) ∧ p3)) → p4) ∨ False) := by
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Implications on the right can always be decomposed.
    intro h5
    -- Conjunctions on the left can always be decomposed.
    let h6 := h5.left
    let h7 := h5.right
    -- Disjunctions on the left can always be decomposed.
    cases h6
    case inl h8 =>
      -- Conjunctions on the left can always be decomposed.
      let h9 := h8.left
      let h10 := h8.right
      -- Conjunctions on the left can always be decomposed.
      let h11 := h7.left
      let h12 := h7.right
      -- Conjunctions on the left can always be decomposed.
      let h13 := h11.left
      let h14 := h11.right
      -- One of the premise coincides with the conclusion.
      exact h13
    case inr h15 =>
      -- Conjunctions on the left can always be decomposed.
      let h16 := h7.left
      let h17 := h7.right
      -- Conjunctions on the left can always be decomposed.
      let h18 := h16.left
      let h19 := h16.right
      -- One of the premise coincides with the conclusion.
      exact h18
  -- We have shown the premise of h2, we can now drive its conclusion.
  let h20 := h2 h4
  -- False on the left can always be used.
  apply False.elim h20
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Conjunctions on the left can always be decomposed.
  let h21 := h1.left
  let h22 := h1.right
  -- We want to use the implication h21 based on <expert-advice>. So we show its premise.
  have h23 : (((((True ∧ p5) ∨ (p2 → p4)) ∧ ((p4 ∧ p3) ∧ p3)) → p4) ∨ False) := by
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Implications on the right can always be decomposed.
    intro h24
    -- Conjunctions on the left can always be decomposed.
    let h25 := h24.left
    let h26 := h24.right
    -- Disjunctions on the left can always be decomposed.
    cases h25
    case inl h27 =>
      -- Conjunctions on the left can always be decomposed.
      let h28 := h27.left
      let h29 := h27.right
      -- Conjunctions on the left can always be decomposed.
      let h30 := h26.left
      let h31 := h26.right
      -- Conjunctions on the left can always be decomposed.
      let h32 := h30.left
      let h33 := h30.right
      -- One of the premise coincides with the conclusion.
      exact h32
    case inr h34 =>
      -- Conjunctions on the left can always be decomposed.
      let h35 := h26.left
      let h36 := h26.right
      -- Conjunctions on the left can always be decomposed.
      let h37 := h35.left
      let h38 := h35.right
      -- One of the premise coincides with the conclusion.
      exact h37
  -- We have shown the premise of h21, we can now drive its conclusion.
  let h39 := h21 h23
  -- False on the left can always be used.
  apply False.elim h39
  -- Conjunctions on the left can always be decomposed.
  let h40 := h1.left
  let h41 := h1.right
  -- We want to use the implication h40 based on <expert-advice>. So we show its premise.
  have h42 : (((((True ∧ p5) ∨ (p2 → p4)) ∧ ((p4 ∧ p3) ∧ p3)) → p4) ∨ False) := by
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Implications on the right can always be decomposed.
    intro h43
    -- Conjunctions on the left can always be decomposed.
    let h44 := h43.left
    let h45 := h43.right
    -- Disjunctions on the left can always be decomposed.
    cases h44
    case inl h46 =>
      -- Conjunctions on the left can always be decomposed.
      let h47 := h46.left
      let h48 := h46.right
      -- Conjunctions on the left can always be decomposed.
      let h49 := h45.left
      let h50 := h45.right
      -- Conjunctions on the left can always be decomposed.
      let h51 := h49.left
      let h52 := h49.right
      -- One of the premise coincides with the conclusion.
      exact h51
    case inr h53 =>
      -- Conjunctions on the left can always be decomposed.
      let h54 := h45.left
      let h55 := h45.right
      -- Conjunctions on the left can always be decomposed.
      let h56 := h54.left
      let h57 := h54.right
      -- One of the premise coincides with the conclusion.
      exact h56
  -- We have shown the premise of h40, we can now drive its conclusion.
  let h58 := h40 h42
  -- False on the left can always be used.
  apply False.elim h58



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_1523026019426847246907651953 : ((((p5 ∨ (p2 ∧ p4)) ∨ p2) ∨ ((p1 ∧ ((((((p1 ∧ p5) → p5) → p3) → p2) ∨ p5) ∨ (p3 → p1))) ∨ p3)) ∨ (False → p1)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_922703724973341103474449724075 : ((((p2 ∨ ((p5 ∧ ((True ∨ p3) → (((True ∨ p1) → p4) ∧ p3))) → p5)) → (((((p4 ∧ True) ∨ p5) ∧ p2) → (False → True)) ∧ p5)) → p5) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h1
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h2 : (p2 ∨ ((p5 ∧ ((True ∨ p3) → (((True ∨ p1) → p4) ∧ p3))) → p5)) := by
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h3
    -- Conjunctions on the left can always be decomposed.
    let h4 := h3.left
    let h5 := h3.right
    -- One of the premise coincides with the conclusion.
    exact h4
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h6 := h1 h2
  -- We need to get the right conjuct of h6 based on <expert-advice>.
  let h7 := h6.right
  -- One of the premise coincides with the conclusion.
  exact h7
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_353676450990192465507197703320 : (p4 → (p5 ∨ (((p2 ∧ (p5 ∧ (p5 ∧ p2))) ∧ (False ∨ ((p3 ∨ p1) ∧ False))) ∨ ((p3 ∨ False) ∨ ((p3 ∨ (False ∨ p1)) → (p3 ∨ p1)))))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h2
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
      -- False on the left can always be used.
      apply False.elim h5
    case inr h6 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- One of the premise coincides with the conclusion.
      exact h6



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_8120002689688190173896873549 : (((((True ∧ p4) ∨ ((False → ((p5 ∨ p4) ∨ p4)) → (p1 ∧ (p2 ∧ (((p3 ∧ p5) ∧ ((p3 ∧ p5) ∧ False)) ∨ p4))))) ∨ p3) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_58113647973173836579910673635 : (((p1 ∧ p5) ∧ ((p4 ∨ (p3 ∨ (p1 ∨ (p5 → ((True ∧ (False → True)) → ((False ∧ (True → p2)) ∧ ((True → p3) ∧ p3))))))) ∨ p5)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_675348434798002351763775697824 : ((((((False ∧ (((p4 → ((p2 ∨ (p5 → (p1 ∨ (p2 ∧ p4)))) ∨ False)) ∨ p4) ∧ True)) → p1) → p5) ∧ (((True ∨ p5) ∧ p3) → p2)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_111550419787318924530720735295 : (((((p3 → (p4 → ((False ∧ ((((p1 ∧ p4) ∨ p2) ∧ True) → p1)) ∨ (p2 ∨ (p4 ∨ p4))))) → (p5 ∧ False)) ∧ p3) ∨ True) ∨ (True → False)) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_59955174178999421171914846764 : (((True ∨ p3) → ((True ∧ p5) ∨ ((p1 → ((p4 ∧ (True → p5)) ∧ (True → p2))) → (((p1 ∨ p4) ∨ (p3 → p1)) → (p2 → p2))))) ∨ p2) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h2 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h3
    -- Implications on the right can always be decomposed.
    intro h4
    -- Implications on the right can always be decomposed.
    intro h5
    -- Disjunctions on the left can always be decomposed.
    cases h4
    case inl h6 =>
      -- Disjunctions on the left can always be decomposed.
      cases h6
      case inl h7 =>
        -- One of the premise coincides with the conclusion.
        exact h5
      case inr h8 =>
        -- One of the premise coincides with the conclusion.
        exact h5
    case inr h9 =>
      -- One of the premise coincides with the conclusion.
      exact h5
  case inr h10 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h11
    -- Implications on the right can always be decomposed.
    intro h12
    -- Implications on the right can always be decomposed.
    intro h13
    -- Disjunctions on the left can always be decomposed.
    cases h12
    case inl h14 =>
      -- Disjunctions on the left can always be decomposed.
      cases h14
      case inl h15 =>
        -- One of the premise coincides with the conclusion.
        exact h13
      case inr h16 =>
        -- One of the premise coincides with the conclusion.
        exact h13
    case inr h17 =>
      -- One of the premise coincides with the conclusion.
      exact h13



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_47179361719255332346277424726 : (((((False ∨ (False → ((p5 ∧ p3) ∧ True))) ∧ ((False ∨ (p2 ∨ p2)) → p1)) → ((p5 ∨ (p4 → (False → p3))) ∨ p4)) ∨ (p2 ∨ p1)) ∨ p1) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- Disjunctions on the left can always be decomposed.
  cases h2
  case inl h4 =>
    -- False on the left can always be used.
    apply False.elim h4
  case inr h5 =>
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h6
    -- Implications on the right can always be decomposed.
    intro h7
    -- False on the left can always be used.
    apply False.elim h7



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_721425008698865690856998011 : ((((((p2 → p1) ∧ p5) ∨ p2) ∧ p2) ∨ ((((p1 ∨ False) → (True ∧ ((((p2 ∨ p5) → True) → p4) → True))) ∧ p1) → False)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_664205235981349740169256088772 : ((((False ∨ (p2 → (p5 ∧ ((p4 ∨ (((p2 → (((p3 ∨ ((p1 ∨ p1) → p2)) ∨ p2) ∨ p5)) ∧ p2) ∨ p3)) → p2)))) → (False ∧ p4)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_116730781505596080451967499830 : (((p3 ∧ p2) ∨ (p4 → (p5 → ((p2 → ((((p1 → ((False → True) ∧ (p4 → p5))) ∧ True) → p1) ∧ True)) ∨ (p5 → p5))))) ∨ (p1 ∨ p3)) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h3
  -- One of the premise coincides with the conclusion.
  exact h3



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_587452334451672009759054744975 : ((((((((True → (p4 → p2)) ∨ (((((p4 ∧ True) → (p1 ∧ p1)) ∧ p1) → (p3 ∧ p4)) ∧ p1)) ∨ (p2 ∨ True)) ∨ p3) ∨ p2) ∧ p2) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_115295372865645844956272818954 : (((((p5 ∨ (p2 ∧ p3)) ∧ (p5 → (False → p3))) ∨ p3) → (((p4 ∧ p5) ∨ True) ∨ ((p3 ∨ ((p1 ∨ True) ∧ p2)) ∨ p4))) ∨ (False ∧ p1)) := by
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
    cases h3
    case inl h5 =>
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- True on the right can always be proven directly.
      apply True.intro
    case inr h6 =>
      -- Conjunctions on the left can always be decomposed.
      let h7 := h6.left
      let h8 := h6.right
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- True on the right can always be proven directly.
      apply True.intro
  case inr h9 =>
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_686129344883743024485606629279 : (((((p1 ∨ (p5 ∧ (p1 ∧ ((True ∨ True) ∧ (False → (False ∨ p5)))))) ∨ ((False → p3) ∧ True)) → (p4 ∧ (p3 ∧ ((p2 ∨ False) ∨ p1)))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_254866782135968573358966857410 : ((p3 ∧ p5) → (p2 → ((((False → (p2 → (((p3 → p3) → (p5 ∧ p5)) ∨ (p5 → (True → (p2 ∧ True)))))) ∧ (p4 → p4)) → p1) ∨ p3))) := by
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
theorem thm_5_vars_215467966667305004092650937433 : ((p3 ∧ (p4 ∨ (p3 ∨ True))) ∨ ((True → (p5 ∨ p4)) → (((p4 ∨ (p1 ∧ (((p2 → (False ∨ p4)) → p2) → (p1 ∨ p4)))) → p1) ∨ True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_111454214785489405054923121144 : (((True → (p5 ∧ (False ∨ ((p1 → (((p1 ∨ (False ∧ p3)) ∨ p5) ∧ ((p5 ∧ p2) ∧ (p3 ∨ (p5 ∧ False))))) ∧ p4)))) ∧ p1) ∨ (p4 ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_323785915345953415320911203774 : (p5 ∨ (((((False ∨ p4) → (False ∨ p5)) ∨ ((p1 ∧ (False ∧ True)) ∧ ((True → p4) ∧ p1))) → p4) ∨ ((False → (True ∨ False)) ∨ (p5 ∨ p4)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_149496538372117982164849403662 : ((p1 ∧ (((False ∨ (p1 ∨ p4)) → ((((p5 ∨ (p4 → (p5 → p3))) ∧ (True → True)) → p1) → p5)) → p5)) ∨ ((True ∧ (p5 ∧ False)) → p1)) := by
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
  -- False on the left can always be used.
  apply False.elim h5



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_111294068906094027085792207786 : (((True ∧ ((p2 → (False → (((p1 → p5) ∧ p5) ∨ (p4 → ((True → p5) ∧ (((p2 ∨ p1) → p2) ∧ p2)))))) → False)) ∧ p5) ∨ (p1 ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_321564709599058466831934325416 : (p4 ∨ (p2 → ((True → ((p3 ∨ p3) ∨ True)) → (((p1 → (((True → True) ∧ p2) ∨ p5)) ∨ (p2 → p5)) → ((False ∨ p2) ∧ (p3 ∨ True)))))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Implications on the right can always be decomposed.
  intro h3
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Disjunctions on the left can always be decomposed.
  cases h3
  case inl h4 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h1
  case inr h5 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h1
  -- Disjunctions on the left can always be decomposed.
  cases h3
  case inl h6 =>
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
theorem thm_5_vars_306581131985150836276681998969 : (p1 ∨ ((p4 ∨ p5) → ((p5 ∨ ((False ∧ p1) ∧ (((p2 ∨ False) ∨ p3) ∧ ((p3 → ((p1 → p4) → True)) ∧ ((p2 ∧ p3) ∧ False))))) ∨ True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
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
theorem thm_5_vars_314638326783530839766000826257 : (p3 ∨ (((((((p2 ∧ p2) → True) ∨ (True → p2)) → ((False ∨ p2) ∨ False)) ∨ False) ∧ p4) ∨ (((p4 ∧ ((p1 → p5) ∧ True)) → p2) → True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_125698086590013175033543465112 : (((False ∨ False) ∨ (((p3 → True) → ((True ∨ ((True → (False ∨ p2)) ∨ (p3 → True))) ∧ p2)) ∧ (((p1 ∨ p2) ∨ p5) → p4))) → (p1 → p2)) := by
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
      -- False on the left can always be used.
      apply False.elim h4
    case inr h5 =>
      -- False on the left can always be used.
      apply False.elim h5
  case inr h6 =>
    -- Conjunctions on the left can always be decomposed.
    let h7 := h6.left
    let h8 := h6.right
    -- We want to use the implication h7 based on <expert-advice>. So we show its premise.
    have h9 : (p3 → True) := by
      -- Implications on the right can always be decomposed.
      intro h10
      -- True on the right can always be proven directly.
      apply True.intro
    -- We have shown the premise of h7, we can now drive its conclusion.
    let h11 := h7 h9
    -- We need to get the right conjuct of h11 based on <expert-advice>.
    let h12 := h11.right
    -- One of the premise coincides with the conclusion.
    exact h12



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_148443409426504727164723080428 : (((p5 → ((((p1 ∧ p5) → p1) ∧ ((False ∧ p3) ∨ (p3 ∨ p5))) ∧ True)) → ((p3 → (p2 → False)) ∧ p3)) ∨ (((p1 → True) ∨ True) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_755550566744983978498991129445 : (((p1 ∧ ((((((p1 ∨ ((p5 ∧ p3) → (True → False))) ∨ (((False ∧ ((False ∨ p3) ∧ True)) → p3) → p3)) ∧ p5) ∧ p2) ∧ p5) ∨ p5)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_346298736236370464781750399932 : (p3 → ((((False → p1) → (((p4 ∧ p5) → p4) ∧ (((True ∧ p1) ∧ (False ∨ ((p2 → (p3 ∧ p1)) → p2))) ∧ p3))) ∨ p3) ∨ (p2 ∨ p5))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_668731668038604358332316928693 : ((((((p4 ∧ ((((p4 ∨ (False → p3)) ∧ (p5 ∨ (((p2 → p4) ∧ p2) ∧ p3))) ∧ True) → False)) ∨ p4) ∨ p3) ∨ (p1 → (p5 ∧ p3))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_67439471908382219892637451475 : ((p1 → ((((p2 ∨ p3) ∧ ((p4 ∨ False) ∨ (((p2 ∧ p1) ∧ (p4 → (p3 ∨ (p5 ∧ p5)))) → p1))) ∧ p4) ∨ (False → (p5 ∧ True)))) ∨ p1) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
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
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_41288099726711423419897710733 : (((((((p4 → (p1 ∧ (True → p5))) → p1) ∨ p5) → (p4 ∨ (p1 ∧ (p3 ∨ (p1 ∧ p3))))) → ((p5 → p1) ∨ (True ∨ True))) ∨ p2) ∨ p1) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_55443225413334701350432720108 : (((((p3 → (True ∨ False)) → False) → p2) → ((p2 ∨ (((False ∧ p1) ∨ p1) ∧ p1)) ∧ (p1 ∧ ((False ∨ (True ∨ True)) ∨ (True ∧ p5))))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_766694396650515621775796950354 : (((p4 ∧ (False ∨ ((p2 → p2) → ((p5 → p4) ∧ (p4 → (False ∨ (p3 ∧ (p1 → ((((p1 ∨ p5) → p4) → False) ∧ (p1 ∧ p3)))))))))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_165062046158826569757798581081 : (((p1 ∧ ((p5 → ((True ∧ (p2 ∨ (p1 → (p1 → p3)))) ∨ (p5 → True))) ∧ p3)) → p2) ∨ (((p4 ∨ (p1 ∨ p5)) ∧ (p2 ∨ p5)) → True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_259574537618343506758771347195 : ((p1 → True) → (((p1 ∧ p4) ∧ ((p1 ∨ (p1 ∧ (p2 ∨ (True ∧ False)))) ∧ (p5 ∨ p1))) ∨ (((p1 ∨ p4) ∧ (p2 ∧ (p5 ∧ p1))) → True))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h2
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_171302848853842986768387807327 : (((((p1 ∧ (True ∧ (True ∧ p3))) ∨ ((p2 → p5) ∧ (p2 → False))) ∧ p3) ∧ p4) ∨ ((((p3 ∨ p4) ∧ p2) → True) ∨ (p1 → (p1 ∧ True)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_615543886017456731459861840481 : ((((((p3 ∨ ((False ∨ p4) → p1)) → (((p3 ∧ False) ∧ p2) ∨ (p4 ∨ (p4 → p4)))) → (((p1 ∨ (p1 ∨ False)) ∧ p3) ∧ p3)) ∨ p4) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_682413822673076291898462135123 : (((((((p4 → ((True ∨ p2) ∨ True)) ∧ ((True ∧ p1) → p2)) ∨ p3) ∧ ((True → True) ∧ p3)) ∧ ((p1 → ((p5 → False) → p3)) → False)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_64911646476745661685868921815 : ((p2 ∨ (((((p4 ∨ (p2 → (p3 ∧ p3))) → (True ∨ p1)) ∧ (p5 ∧ p5)) → (True → (p3 → True))) → (p3 → ((p2 → True) ∧ p3)))) ∨ p4) := by
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
  -- Implications on the right can always be decomposed.
  intro h3
  -- True on the right can always be proven directly.
  apply True.intro
  -- One of the premise coincides with the conclusion.
  exact h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_179179722025666701404628275770 : ((p3 ∧ ((((p2 → p3) → p1) → ((p3 ∨ (p1 ∧ p4)) ∨ p5)) ∨ False)) ∨ (p1 ∨ (True ∧ ((True → (p1 ∨ (p5 → p5))) ∨ (p5 → False))))) := by
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
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h2
  -- One of the premise coincides with the conclusion.
  exact h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_665855565205575949215117131424 : ((((((p5 ∧ ((True ∧ (((p4 ∨ (True → p4)) → p3) → (True ∧ p4))) ∨ (p5 → p1))) → (False → False)) → p2) ∧ (p5 ∧ (True ∧ p4))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_147630332444102867945593219879 : ((((((p1 ∨ p4) → (((p4 ∨ ((True ∨ p3) ∨ p3)) ∨ True) ∧ True)) → (False ∧ (False ∨ p1))) → p2) → p2) ∨ (p3 → ((p4 → True) ∨ p1))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h2
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_137064306126638444686387954683 : (((p3 → p1) → ((((p5 ∧ (p1 ∧ ((p5 ∨ (p4 ∨ p3)) ∧ False))) ∨ (p4 → p1)) ∨ p5) ∨ (False ∧ (p5 ∧ p5)))) ∨ (p1 → (False → p4))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- False on the left can always be used.
  apply False.elim h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_655776935931837490528643155144 : ((((((p4 ∧ (False → (p5 ∧ p5))) → (((p2 → p5) ∧ ((False ∧ (p5 → False)) ∨ p2)) ∨ p4)) ∨ (p1 ∧ (p4 → True))) ∨ (p2 ∨ p1)) ∨ p5) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h2
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_243908190700703064649950707482 : ((True ∧ False) ∨ ((p5 → ((((p2 → p5) → p3) ∨ ((False ∧ p4) → p2)) ∨ False)) → (True ∧ (p2 → (((p5 → True) → p4) ∨ (p1 ∨ p2)))))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- Implications on the right can always be decomposed.
  intro h2
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_300133556759056703715737992210 : (False ∨ (((False → True) → ((((True ∧ False) ∨ (((p5 ∨ True) ∧ p4) ∧ p5)) ∧ p3) ∧ ((((p5 ∨ True) ∧ p2) → True) → p5))) ∨ (p1 ∨ True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_309348990244916347365973515392 : (p2 ∨ (((p3 ∧ ((p5 → (p3 → ((p1 ∨ (False ∨ (p5 ∨ False))) ∧ p2))) → p1)) ∨ ((p5 → True) → (p3 → (p3 ∧ p2)))) ∨ (True ∨ True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_343537328294236154182338341639 : (p2 → ((True ∨ p5) → ((((((((True ∧ (p2 ∨ p3)) ∧ ((p2 ∨ p4) ∨ False)) ∨ (p1 ∨ p2)) ∨ p1) ∧ (p2 ∧ True)) → p1) ∧ p4) ∨ True))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
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



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_135033189147766934872754262534 : ((((((p2 ∧ (p1 ∧ ((p2 ∨ ((p2 → True) → False)) ∨ p4))) ∧ (p5 → True)) ∧ (p3 ∧ p5)) ∧ p1) ∨ (p3 ∧ p3)) ∨ (p5 ∨ (p2 → p2))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_698200088213850553260282652005 : ((((((p1 → ((p3 ∨ p2) ∨ p2)) → (True → (p4 → p4))) → p3) ∨ (p5 → ((True ∧ (p4 ∨ (p1 ∨ ((False ∧ p4) ∨ True)))) ∧ p5))) ∨ p4) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- One of the premise coincides with the conclusion.
  exact h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_243787757990664799418113274902 : ((p5 → p5) ∧ (((p3 ∨ (((False → False) → p2) ∧ True)) ∨ (p4 → p1)) → (p2 → ((True ∧ (p1 ∨ (((p1 ∧ p3) → p2) ∧ p2))) ∨ p2)))) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h1
  -- One of the premise coincides with the conclusion.
  exact h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Implications on the right can always be decomposed.
  intro h3
  -- Disjunctions on the left can always be decomposed.
  cases h2
  case inl h4 =>
    -- Disjunctions on the left can always be decomposed.
    cases h4
    case inl h5 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- One of the premise coincides with the conclusion.
      exact h3
    case inr h6 =>
      -- Conjunctions on the left can always be decomposed.
      let h7 := h6.left
      let h8 := h6.right
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- One of the premise coincides with the conclusion.
      exact h3
  case inr h9 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h3



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_138390640904306001609289290118 : ((p4 → (p5 ∧ ((p5 → (p3 ∧ p5)) → ((p5 ∧ (((p5 ∨ True) ∨ p5) ∨ p2)) ∨ ((p2 ∨ (p5 → p3)) → p1))))) ∨ ((p4 ∧ False) → p5)) := by
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
theorem thm_5_vars_258426127336277517073931475414 : ((p5 ∨ p1) → ((p3 ∧ (False ∧ (p3 → (p2 ∧ p1)))) ∨ ((((p3 ∨ p4) → (p3 → False)) ∧ ((p4 ∨ (p3 ∧ False)) → (True → True))) → True))) := by
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
theorem thm_5_vars_61699274086347586868635219582 : ((p1 ∧ (p3 ∨ ((((((p2 ∨ p3) → (((p3 ∧ p5) ∨ p3) ∨ (p5 → p1))) ∧ True) ∧ (p2 ∧ p2)) ∧ (True → (p1 ∧ p4))) ∧ p4))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_778082965216508643933843758072 : (((p1 ∨ ((p1 → p1) ∧ (((p1 → p3) ∨ (((False → (p4 → (p2 → (False → p1)))) ∧ p5) → True)) → (((p3 → True) → p4) ∨ True)))) ∨ p4) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h1
  -- One of the premise coincides with the conclusion.
  exact h1
  -- Implications on the right can always be decomposed.
  intro h2
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
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_635679814695340067249669217418 : (((((p5 ∨ ((p2 ∨ ((p3 ∨ (((p1 → (p2 → p3)) ∧ p4) ∧ (p4 ∨ p1))) ∧ True)) ∧ p1)) ∨ (p3 ∧ ((p4 ∧ p4) ∨ p4))) → p2) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_262480400360507390459258973245 : (True ∧ ((p5 ∨ (((p3 ∨ p4) ∨ p4) → (((True ∧ ((p2 ∨ False) → p1)) → ((True → p4) ∧ ((True ∧ (False ∧ p5)) → p4))) → False))) ∨ True)) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_58610690950904969522777046496 : (((False → p2) ∧ (((p5 ∨ p3) → (p3 ∧ False)) ∧ (p4 → (((((p3 ∧ p1) ∨ (p4 → p1)) ∧ ((True ∨ p2) ∨ True)) → p1) ∨ p2)))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_706471362815182179861215572296 : ((((p3 ∨ (False → (True → (p2 ∨ (p2 → False))))) ∧ ((p4 ∨ p4) → ((((p4 ∨ p1) ∨ True) → p2) ∨ (p1 ∧ (p4 ∧ (p3 ∨ p5)))))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_53586440837968484223196459173 : (((((p2 ∨ (p1 → (p2 ∧ p4))) ∧ (p1 → p5)) → p3) ∧ (((p3 ∧ ((((p2 → True) → p4) → p1) → False)) ∨ (True ∨ p5)) → p3)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_354818737220272237530971754765 : (p5 → (((p3 → (True ∧ False)) ∧ ((((True ∧ (((p4 ∧ p1) ∧ p1) ∨ True)) ∨ (False → p3)) ∨ p1) ∧ (p2 ∨ ((p2 ∧ p5) ∧ p1)))) ∨ True)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_345734938299339175890343516928 : (p3 → ((p5 → ((p1 → False) ∨ (p5 ∧ ((p4 ∨ p1) ∨ ((((p4 ∧ p1) ∨ (True ∨ p5)) ∨ (((p4 ∧ True) → p5) ∨ p1)) → p4))))) ∨ p3)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_694514442684345442810797503469 : ((((False ∧ ((((p1 → (p2 → p1)) ∨ p5) ∧ ((p3 ∨ p3) → p5)) → p3)) ∨ (False → ((p2 ∨ (True ∧ (False ∨ (p1 ∨ p2)))) ∨ p5))) ∨ p1) ∧ True) := by
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
theorem thm_5_vars_118326083021386528977317457115 : ((p2 ∨ (((p1 ∨ ((False → (p4 → (((False ∨ False) → p1) ∨ (p4 ∨ p3)))) ∧ (((p3 → p5) → p5) ∨ p3))) ∨ p3) ∧ p2)) ∨ (True ∧ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_708793365310440426372579080221 : (((((p3 ∨ (p2 ∧ (p1 ∨ (p4 ∨ True)))) → p4) → ((p5 → p4) ∨ (((True ∨ (p1 → p3)) ∨ (((p3 → p1) ∧ p1) ∨ p4)) ∨ True))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_67908923539080838238425559872 : ((p2 → (((p4 ∧ (False ∨ (p5 ∨ p3))) → ((p2 ∨ False) ∨ ((True ∧ p5) → p2))) → (p5 ∧ (p5 ∧ (p4 ∧ (p3 → (p3 ∧ p1))))))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_187407589184577077339094244696 : ((p4 ∧ (False ∨ (((True ∧ (p3 ∨ p1)) ∨ p5) ∨ (p4 ∨ p2)))) → ((((((p2 → False) ∨ p4) → (False ∨ p4)) ∧ p2) ∨ p1) ∨ (True ∨ p4))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- Disjunctions on the left can always be decomposed.
  cases h3
  case inl h4 =>
    -- False on the left can always be used.
    apply False.elim h4
  case inr h5 =>
    -- Disjunctions on the left can always be decomposed.
    cases h5
    case inl h6 =>
      -- Disjunctions on the left can always be decomposed.
      cases h6
      case inl h7 =>
        -- Conjunctions on the left can always be decomposed.
        let h8 := h7.left
        let h9 := h7.right
        -- Disjunctions on the left can always be decomposed.
        cases h9
        case inl h10 =>
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- Show the left disjunct based on <expert-advice>.
          apply Or.inl
          -- True on the right can always be proven directly.
          apply True.intro
        case inr h11 =>
          -- Show the left disjunct based on <expert-advice>.
          apply Or.inl
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- One of the premise coincides with the conclusion.
          exact h11
      case inr h12 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- True on the right can always be proven directly.
        apply True.intro
    case inr h13 =>
      -- Disjunctions on the left can always be decomposed.
      cases h13
      case inl h14 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- True on the right can always be proven directly.
        apply True.intro
      case inr h15 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- True on the right can always be proven directly.
        apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_319049185186404962939961924419 : (p4 ∨ ((((p1 ∨ (False → p2)) → False) ∨ ((p2 ∧ (((p4 ∧ (p5 ∧ p4)) ∨ True) ∨ (p5 ∨ p4))) → p2)) ∨ ((p2 ∧ (p1 → False)) ∨ p1))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
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
    -- Disjunctions on the left can always be decomposed.
    cases h4
    case inl h5 =>
      -- Conjunctions on the left can always be decomposed.
      let h6 := h5.left
      let h7 := h5.right
      -- Conjunctions on the left can always be decomposed.
      let h8 := h7.left
      let h9 := h7.right
      -- One of the premise coincides with the conclusion.
      exact h2
    case inr h10 =>
      -- One of the premise coincides with the conclusion.
      exact h2
  case inr h11 =>
    -- Disjunctions on the left can always be decomposed.
    cases h11
    case inl h12 =>
      -- One of the premise coincides with the conclusion.
      exact h2
    case inr h13 =>
      -- One of the premise coincides with the conclusion.
      exact h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_161890042096941376690084434835 : ((False → (p2 ∧ (True ∧ (((p3 ∧ (((p1 ∨ (p2 ∨ (p3 ∨ p4))) → True) → p2)) ∨ False) → False)))) → (p4 → (p4 ∧ ((p2 ∨ p4) ∨ p5)))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- One of the premise coincides with the conclusion.
  exact h2
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_234137447134948076148915149503 : ((True → (p5 ∨ False)) → (((p3 ∨ ((p1 → ((((p2 ∧ p1) ∧ p5) → p1) → True)) → (True → (p3 → p4)))) → False) ∨ (p2 ∨ (p5 ∧ True)))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h2 : True := by
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h3 := h1 h2
  -- Disjunctions on the left can always be decomposed.
  cases h3
  case inl h4 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Conjunctions on the right can always be decomposed.
    apply And.intro
    -- One of the premise coincides with the conclusion.
    exact h4
    -- True on the right can always be proven directly.
    apply True.intro
  case inr h5 =>
    -- False on the left can always be used.
    apply False.elim h5



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_784696073416698157685144042253 : (((p3 ∨ (p4 ∨ ((p5 ∨ ((((((p4 → p3) ∨ (p5 ∧ p1)) ∧ p4) ∧ p3) → p1) ∧ p4)) ∨ (p1 ∨ (True ∨ (p3 ∧ (p1 ∧ p4))))))) ∨ False) ∧ True) := by
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
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



