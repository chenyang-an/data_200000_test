variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_138044260587495438959496575484 : ((True → ((((p5 ∧ p5) ∧ False) ∨ p3) ∨ ((True ∧ p1) ∨ ((((p2 ∨ (p3 → True)) → False) ∨ (p3 → True)) ∧ p1)))) ∨ ((p2 ∧ p1) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_208582377534583574912343777237 : (((False → p4) → (p2 ∧ (False ∨ False))) → ((False ∨ ((p5 ∨ True) ∨ p3)) → (((p3 ∧ True) ∨ (p1 ∨ (p5 ∨ False))) ∧ ((p3 ∧ p2) ∨ False)))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Disjunctions on the left can always be decomposed.
  cases h2
  case inl h3 =>
    -- False on the left can always be used.
    apply False.elim h3
  case inr h4 =>
    -- Disjunctions on the left can always be decomposed.
    cases h4
    case inl h5 =>
      -- Disjunctions on the left can always be decomposed.
      cases h5
      case inl h6 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- One of the premise coincides with the conclusion.
        exact h6
      case inr h7 =>
        -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
        have h8 : (False → p4) := by
          -- Implications on the right can always be decomposed.
          intro h9
          -- False on the left can always be used.
          apply False.elim h9
        -- We have shown the premise of h1, we can now drive its conclusion.
        let h10 := h1 h8
        -- We need to get the right conjuct of h10 based on <expert-advice>.
        let h11 := h10.right
        -- Disjunctions on the left can always be decomposed.
        cases h11
        case inl h12 =>
          -- False on the left can always be used.
          apply False.elim h12
        case inr h13 =>
          -- False on the left can always be used.
          apply False.elim h13
    case inr h14 =>
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- Conjunctions on the right can always be decomposed.
      apply And.intro
      -- One of the premise coincides with the conclusion.
      exact h14
      -- True on the right can always be proven directly.
      apply True.intro
  -- Disjunctions on the left can always be decomposed.
  cases h2
  case inl h15 =>
    -- False on the left can always be used.
    apply False.elim h15
  case inr h16 =>
    -- Disjunctions on the left can always be decomposed.
    cases h16
    case inl h17 =>
      -- Disjunctions on the left can always be decomposed.
      cases h17
      case inl h18 =>
        -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
        have h19 : (False → p4) := by
          -- Implications on the right can always be decomposed.
          intro h20
          -- False on the left can always be used.
          apply False.elim h20
        -- We have shown the premise of h1, we can now drive its conclusion.
        let h21 := h1 h19
        -- We need to get the right conjuct of h21 based on <expert-advice>.
        let h22 := h21.right
        -- Disjunctions on the left can always be decomposed.
        cases h22
        case inl h23 =>
          -- False on the left can always be used.
          apply False.elim h23
        case inr h24 =>
          -- False on the left can always be used.
          apply False.elim h24
      case inr h25 =>
        -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
        have h26 : (False → p4) := by
          -- Implications on the right can always be decomposed.
          intro h27
          -- False on the left can always be used.
          apply False.elim h27
        -- We have shown the premise of h1, we can now drive its conclusion.
        let h28 := h1 h26
        -- We need to get the right conjuct of h28 based on <expert-advice>.
        let h29 := h28.right
        -- Disjunctions on the left can always be decomposed.
        cases h29
        case inl h30 =>
          -- False on the left can always be used.
          apply False.elim h30
        case inr h31 =>
          -- False on the left can always be used.
          apply False.elim h31
    case inr h32 =>
      -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
      have h33 : (False → p4) := by
        -- Implications on the right can always be decomposed.
        intro h34
        -- False on the left can always be used.
        apply False.elim h34
      -- We have shown the premise of h1, we can now drive its conclusion.
      let h35 := h1 h33
      -- We need to get the right conjuct of h35 based on <expert-advice>.
      let h36 := h35.right
      -- Disjunctions on the left can always be decomposed.
      cases h36
      case inl h37 =>
        -- False on the left can always be used.
        apply False.elim h37
      case inr h38 =>
        -- False on the left can always be used.
        apply False.elim h38



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_773553877344322776766455274156 : (((False ∨ ((((False → (p4 → p2)) → (p5 ∨ True)) ∧ (p4 ∧ ((False ∨ ((p4 ∧ ((p5 ∨ (p1 ∧ False)) → p2)) ∨ p2)) → p2))) ∨ p2)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_654388191981786709254572160529 : (((((((p4 ∨ (p5 → (p1 ∨ p1))) → p1) ∧ ((True → (((p3 → p5) ∧ (True ∨ p2)) ∨ p3)) → (p1 ∧ p4))) ∨ False) ∨ (p4 → p4)) ∨ p2) ∧ True) := by
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
theorem thm_5_vars_248049985445896875107654428517 : ((p1 ∨ p5) ∨ ((p2 ∧ p1) → ((False ∨ ((p4 ∨ False) ∨ (True ∨ (((p3 → ((p5 ∧ False) → (p2 ∧ p5))) ∨ p3) → p1)))) ∨ (True → p1)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
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
theorem thm_5_vars_322508029241148589790590133975 : (p5 ∨ ((True ∧ (False ∨ (((((True ∧ ((p5 ∨ (True ∨ p1)) ∧ p2)) ∨ (((p2 ∨ True) ∨ (p1 → False)) → p3)) → p4) ∨ p3) ∨ True))) ∨ p3)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_165432012373531737614739425761 : (((p1 ∧ ((((False → p5) ∧ (False ∨ True)) → p2) ∨ (True → p3))) → ((p1 ∧ p4) ∨ p3)) ∨ (((((p5 ∨ True) → False) ∧ False) → True) ∧ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_245500388175978329012345616694 : ((p2 ∧ p5) ∨ ((p2 → p1) → (((((False ∨ True) ∨ p1) → (((p2 ∨ (False → p5)) → ((p1 ∧ True) → True)) → p3)) → p1) ∨ (True ∧ True)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
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
theorem thm_5_vars_358652880294955631118321276784 : (p5 → (p4 → (((p2 ∨ (((True ∧ False) ∧ (((p1 ∨ ((p4 → True) ∧ p3)) → (p1 ∧ False)) ∨ p5)) ∨ (p1 → p4))) ∨ p2) ∨ (p4 ∧ p3)))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h3
  -- One of the premise coincides with the conclusion.
  exact h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_349272643624768652714087975547 : (p3 → (p2 → (((p4 ∧ ((p2 ∧ (p5 ∧ ((p5 ∧ ((False → False) ∧ p3)) ∨ (p2 ∧ (((p1 → p4) → p4) ∧ p4))))) ∨ p1)) ∧ p1) ∨ True))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_56592140400614223824447579390 : (((p2 → (p1 → (False ∨ p4))) → (p4 ∨ ((((p2 ∨ (p1 → p1)) → p3) ∧ p1) ∧ (False ∨ (p2 ∨ (((False ∧ p5) → p1) ∨ False)))))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_178312038976995216266522586147 : (((((p3 → (False ∧ p3)) ∨ ((p1 → p3) → p1)) ∨ p1) ∨ (False → False)) ∨ ((p5 ∧ p4) → (((True ∧ ((p1 ∧ p2) ∨ p1)) ∨ p4) ∧ p4))) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_179417795527016926984070472621 : ((p4 ∨ ((False → ((p1 ∧ (False ∨ (False ∧ (p5 ∧ False)))) ∧ p2)) → p4)) ∨ (((((p3 ∨ p2) ∨ True) → (False ∨ p5)) ∨ (True → True)) ∨ p2)) := by
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
theorem thm_5_vars_156899131636066394047192213547 : ((((False ∨ ((((p5 → p3) ∨ (((p2 ∨ p4) ∨ p3) ∨ p3)) → p1) → (p4 ∨ p5))) ∨ False) ∨ p3) ∨ (p5 → (p5 ∨ (p2 ∨ (p5 ∧ p3))))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_184797855525097318401402823561 : (((p1 ∧ (p5 ∨ (p4 ∧ p2))) ∨ (p1 ∧ (p5 → (p1 ∨ True)))) ∨ ((p1 → (((False ∨ (False ∨ p5)) ∨ p1) ∨ p2)) ∨ (p1 → (p1 → p4)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_919267925008354928179855633483 : (((((True ∧ (True ∧ (True → p1))) ∧ (((p1 ∧ p1) ∧ (p1 ∧ p3)) ∧ p5)) ∧ ((p1 → (p3 → (p4 ∧ (False ∨ True)))) → (True → p1))) → p1) ∧ True) := by
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
  -- Conjunctions on the left can always be decomposed.
  let h14 := h12.left
  let h15 := h12.right
  -- Conjunctions on the left can always be decomposed.
  let h16 := h13.left
  let h17 := h13.right
  -- One of the premise coincides with the conclusion.
  exact h16
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_704060424928016706765231878764 : (((((False ∧ (p2 ∨ ((p1 → (p1 → False)) → p3))) → True) → (((p5 → False) ∧ (True → (((p2 ∨ p2) → True) ∨ p5))) → (p3 ∨ True))) ∨ False) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
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
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_131025405239745222493865614763 : ((((False ∧ ((p5 ∨ p1) ∧ (False ∧ p2))) ∨ (p1 ∧ p5)) ∨ ((p1 → (p4 ∨ ((p5 → False) ∨ (True ∨ False)))) ∨ p2)) ∧ ((p3 → p3) ∨ p5)) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
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
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h2
  -- One of the premise coincides with the conclusion.
  exact h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_184747812098689662415228406897 : ((((p4 → (p4 ∨ p3)) → p1) ∧ (((p4 ∧ p2) → False) → p4)) ∨ (((p5 → (p3 ∧ (p3 ∨ ((p1 ∧ p1) ∨ (True → True))))) ∨ p4) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_306009349381456881164696355286 : (p1 ∨ ((True ∧ (False ∨ (p5 ∧ p1))) ∨ ((p3 → (((p1 ∨ True) ∨ p2) ∨ p1)) ∧ (((((p3 ∨ p3) ∧ (False ∧ p1)) → p4) → p3) → True)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- Implications on the right can always be decomposed.
  intro h2
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_147687540095178917239168752464 : (((((False ∨ ((((p4 ∨ (True → p1)) ∧ (p5 → True)) ∧ p1) ∨ True)) → p5) → ((p3 ∨ p5) → p3)) → False) ∨ ((p5 ∧ p4) → (p4 → p5))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Conjunctions on the left can always be decomposed.
  let h3 := h1.left
  let h4 := h1.right
  -- One of the premise coincides with the conclusion.
  exact h3



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_134871096943835596042992154255 : (((p1 → (((p4 ∨ True) ∨ (p4 ∧ False)) → ((True → ((((p5 ∨ p4) → p5) ∧ p4) → True)) → (False → p3)))) → False) ∨ (True ∨ (p4 → p1))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_256123617860476129011130635848 : ((True ∨ p5) → ((p5 → (p3 ∧ p1)) → ((p3 ∧ ((False ∧ p3) → (p4 ∧ p2))) → (((p1 → p3) ∨ ((False ∨ (p1 ∨ p3)) → p4)) ∧ p3)))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Implications on the right can always be decomposed.
  intro h3
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Conjunctions on the left can always be decomposed.
  let h4 := h3.left
  let h5 := h3.right
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h6 =>
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Implications on the right can always be decomposed.
    intro h7
    -- One of the premise coincides with the conclusion.
    exact h4
  case inr h8 =>
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Implications on the right can always be decomposed.
    intro h9
    -- One of the premise coincides with the conclusion.
    exact h4
  -- Conjunctions on the left can always be decomposed.
  let h10 := h3.left
  let h11 := h3.right
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h12 =>
    -- One of the premise coincides with the conclusion.
    exact h10
  case inr h13 =>
    -- One of the premise coincides with the conclusion.
    exact h10



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_124604087720561821390418105538 : (((p1 ∧ (p1 ∧ (p3 ∨ (p1 ∨ p4)))) ∨ ((True ∨ (((((((p3 → True) ∨ True) → p2) → False) → p5) ∧ p3) ∧ p3)) ∧ p2)) → (False ∨ True)) := by
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
    -- Disjunctions on the left can always be decomposed.
    cases h6
    case inl h7 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- True on the right can always be proven directly.
      apply True.intro
    case inr h8 =>
      -- Disjunctions on the left can always be decomposed.
      cases h8
      case inl h9 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- True on the right can always be proven directly.
        apply True.intro
      case inr h10 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- True on the right can always be proven directly.
        apply True.intro
  case inr h11 =>
    -- Conjunctions on the left can always be decomposed.
    let h12 := h11.left
    let h13 := h11.right
    -- Disjunctions on the left can always be decomposed.
    cases h12
    case inl h14 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- True on the right can always be proven directly.
      apply True.intro
    case inr h15 =>
      -- Conjunctions on the left can always be decomposed.
      let h16 := h15.left
      let h17 := h15.right
      -- Conjunctions on the left can always be decomposed.
      let h18 := h16.left
      let h19 := h16.right
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- True on the right can always be proven directly.
      apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_51119996467479035140561912207 : ((((((p4 ∧ (p3 ∨ (False ∨ p4))) ∧ (p4 ∨ (p4 → False))) ∨ (p3 ∨ (False → p3))) ∨ p3) ∨ ((True → (p2 ∨ (False ∧ False))) ∧ p5)) ∨ False) := by
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
  -- Implications on the right can always be decomposed.
  intro h1
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_257625358309364681911463667472 : ((p3 ∨ p2) → ((((p3 ∧ (p2 → p3)) ∨ ((((p5 ∨ p3) ∧ p4) → p4) → (((p5 ∧ False) → False) → p4))) ∨ False) ∨ (p4 ∨ (p2 ∧ True)))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h2 =>
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Conjunctions on the right can always be decomposed.
    apply And.intro
    -- One of the premise coincides with the conclusion.
    exact h2
    -- Implications on the right can always be decomposed.
    intro h3
    -- One of the premise coincides with the conclusion.
    exact h2
  case inr h4 =>
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



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_806783656202390439647121022955 : (((p4 → ((((p3 ∧ (p2 ∨ (((p1 ∨ p1) ∧ (((False ∨ p2) ∧ (p3 ∨ p5)) → p4)) ∧ False))) → (True → True)) → p3) ∨ (p4 ∨ False))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_231129111835681709195217525390 : (((p1 ∨ p2) ∨ False) → ((((((p1 → ((p3 ∨ p1) ∧ p2)) → True) → p1) → p3) → (p5 → (p3 ∨ p1))) ∨ (p4 → (p5 → (p5 ∧ p4))))) := by
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
      -- Implications on the right can always be decomposed.
      intro h5
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- One of the premise coincides with the conclusion.
      exact h3
    case inr h6 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Implications on the right can always be decomposed.
      intro h7
      -- Implications on the right can always be decomposed.
      intro h8
      -- Conjunctions on the right can always be decomposed.
      apply And.intro
      -- One of the premise coincides with the conclusion.
      exact h8
      -- One of the premise coincides with the conclusion.
      exact h7
  case inr h9 =>
    -- False on the left can always be used.
    apply False.elim h9



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_60531159215027898173966608321 : ((True ∧ (((p2 ∧ ((((p2 → False) ∧ (p1 ∧ (((p4 → p4) ∨ p4) ∧ p1))) → ((p2 ∨ True) ∨ False)) → p2)) ∧ (False ∨ p2)) ∨ False)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_262152669909216897005793192680 : (True ∧ ((((((p5 ∧ p4) ∨ (p5 → p1)) ∧ (p1 ∧ (((p5 ∨ (p4 ∨ False)) ∨ p4) ∧ False))) ∨ (False → (False ∧ (p3 → p1)))) ∨ p3) ∨ False)) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- False on the left can always be used.
  apply False.elim h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_689005649913664250008342763395 : (((((((p4 ∨ p4) → ((True ∧ (p3 ∧ ((p3 → p4) → False))) ∨ True)) → p4) ∨ True) ∨ (p3 ∨ (p2 ∨ (((p1 ∧ p1) ∧ True) ∨ p5)))) ∨ p1) ∧ True) := by
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
theorem thm_5_vars_23728318114491728919421136309 : ((((False ∧ p1) ∧ (p3 ∨ False)) ∨ (((((((p2 ∧ (True ∨ True)) → p1) → p4) → (p4 ∨ ((p1 → p2) → p5))) ∧ p5) ∨ True) ∨ True)) ∧ True) := by
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



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_731164539315959801390862038739 : ((((p2 ∨ (p5 ∨ False)) → ((((False ∨ (p1 → (((False → p4) → False) ∧ (False ∨ (p3 ∨ ((p2 ∧ True) ∧ p2)))))) → p3) → False) ∨ True)) ∨ p2) ∧ True) := by
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
    -- True on the right can always be proven directly.
    apply True.intro
  case inr h3 =>
    -- Disjunctions on the left can always be decomposed.
    cases h3
    case inl h4 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- True on the right can always be proven directly.
      apply True.intro
    case inr h5 =>
      -- False on the left can always be used.
      apply False.elim h5
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_134858758653995774819150503056 : (((True → ((p5 ∨ (p3 ∨ False)) ∧ (True → ((False → p2) → (p3 → (True → (((p2 → False) → p1) → p4))))))) → False) ∨ (p2 → (p2 → p2))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_729903026965399775592987620325 : (((((p2 ∧ p4) → p4) → ((p2 ∧ (((p3 → ((p3 → p3) ∨ False)) → (True ∧ (p4 ∨ p5))) → p1)) ∨ ((False ∧ False) ∧ (p5 → p2)))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_175236843729604058638829411269 : ((p1 ∨ ((p5 → p2) ∨ (p1 → ((True ∧ ((p2 → p5) ∨ True)) ∧ (p2 ∨ True))))) → (((False ∧ p5) ∨ (p5 ∧ p1)) ∨ (False → (p3 → p2)))) := by
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
    -- False on the left can always be used.
    apply False.elim h3
  case inr h5 =>
    -- Disjunctions on the left can always be decomposed.
    cases h5
    case inl h6 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Implications on the right can always be decomposed.
      intro h7
      -- Implications on the right can always be decomposed.
      intro h8
      -- False on the left can always be used.
      apply False.elim h7
    case inr h9 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Implications on the right can always be decomposed.
      intro h10
      -- Implications on the right can always be decomposed.
      intro h11
      -- False on the left can always be used.
      apply False.elim h10



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_178425242997912233531698302290 : (((p3 → (((p5 ∨ p2) ∨ ((p5 ∧ p4) ∧ p3)) ∨ p3)) → (p4 ∧ False)) ∨ (((((True ∨ p4) ∨ p3) ∨ (p4 → p1)) → (p5 → True)) ∨ p1)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_773174244460403175391383064102 : (((False ∨ (((False ∧ (p1 ∨ (((True → True) ∨ p5) ∧ (((False ∨ p3) ∧ p3) ∧ (False ∨ (p2 ∨ (p2 → (True ∨ p3)))))))) ∨ True) ∧ True)) ∨ p3) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
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
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_708538855011477557061837532928 : ((((((p2 → (p2 → True)) ∧ (p2 ∨ p5)) ∨ True) → ((((p2 → ((p1 → (False ∧ True)) ∧ (False ∨ p5))) ∨ (p5 ∧ False)) ∧ True) ∧ p2)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_113186197613766789949504067354 : (((((False → (((p4 ∧ p2) → p5) → (p2 ∧ (False ∨ p2)))) → (((p2 ∨ p2) ∧ (False ∧ p1)) ∧ p5)) ∧ p1) ∧ (p3 → p4)) ∨ (p3 → p3)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_37148795071631295631336728950 : (((((p1 → (p2 → (((p5 ∨ (p5 ∨ ((p5 ∧ True) ∨ p3))) ∨ p4) ∨ ((p1 ∧ p3) ∧ p3)))) ∧ ((p5 → p4) → True)) ∧ p5) ∧ p2) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_767541898666095960304020671254 : (((p5 ∧ (((((p1 → True) ∨ (p3 ∧ p2)) ∧ (p1 ∨ (((p2 → (p5 ∨ True)) ∨ p2) ∧ (True → (p4 ∨ p2))))) ∨ (False → p5)) ∨ p5)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_62759706804018743933018971492 : ((p4 ∧ (((((False ∨ ((p3 ∧ p5) ∨ p3)) ∨ p2) ∨ p2) ∧ (((p5 → p1) → ((p5 → True) ∧ p4)) ∧ False)) ∧ (p5 → (p3 → True)))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_606710497477284141298663406240 : (((((((p5 ∨ (p3 ∧ (((p3 ∧ p4) ∨ (p3 → p2)) → ((p1 ∨ (False → (p3 ∨ p4))) ∨ True)))) ∧ True) ∨ (p1 → p2)) ∧ False) ∨ p4) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_184951735994038443512943548461 : ((((p2 ∨ p4) ∨ False) → (((p5 → p3) ∧ (True ∨ p4)) → False)) ∨ ((False ∧ True) → (p2 ∧ (((p4 ∧ p4) → (p5 ∧ True)) → (True → p3))))) := by
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
  apply False.elim h2
  -- Implications on the right can always be decomposed.
  intro h4
  -- Implications on the right can always be decomposed.
  intro h5
  -- Conjunctions on the left can always be decomposed.
  let h6 := h1.left
  let h7 := h1.right
  -- False on the left can always be used.
  apply False.elim h6



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_480254555559636696114167346434 : (((((((p4 ∧ False) → p3) → (p1 ∨ p2)) ∧ p2) ∨ (((p4 ∨ p1) ∨ ((False → (True → (p1 → (p4 ∨ True)))) ∧ (True → True))) ∨ p4)) ∧ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Implications on the right can always be decomposed.
  intro h3
  -- False on the left can always be used.
  apply False.elim h1
  -- Implications on the right can always be decomposed.
  intro h4
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_42371243402607894996181951979 : (((p4 ∧ ((p4 → ((p3 → (p1 → (p5 → (p2 ∨ p5)))) → ((p3 ∨ p5) → (p3 → ((p2 → False) ∨ (p4 → p4)))))) ∧ p1)) ∨ True) ∨ p1) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_45277774732751040275656201810 : (((p2 ∧ (((((True ∨ (((p2 → (False ∧ p1)) ∧ p1) ∧ False)) → ((p4 ∨ (p1 ∨ p2)) ∨ p2)) ∧ p5) ∧ p1) → (p1 ∨ p4))) → False) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_140639638714331224411085206764 : ((((((True ∧ False) → p4) ∧ (p1 → (p5 ∧ (p4 → (p1 ∨ p4))))) ∧ p5) ∧ (p1 ∨ (p5 ∧ ((p5 ∨ p5) → p4)))) → (p5 ∧ (p2 → True))) := by
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
  -- Conjunctions on the left can always be decomposed.
  let h6 := h4.left
  let h7 := h4.right
  -- Disjunctions on the left can always be decomposed.
  cases h3
  case inl h8 =>
    -- One of the premise coincides with the conclusion.
    exact h5
  case inr h9 =>
    -- Conjunctions on the left can always be decomposed.
    let h10 := h9.left
    let h11 := h9.right
    -- One of the premise coincides with the conclusion.
    exact h10
  -- Implications on the right can always be decomposed.
  intro h12
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_250688187036366363689161572473 : ((p1 → False) ∨ (((p4 ∨ (p5 → (False ∧ (p1 ∨ (p1 ∨ True))))) → (((p5 ∨ ((True ∧ False) → p4)) → p4) ∨ (True ∨ (p4 ∧ p4)))) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_44451018966839756216181119254 : (((((p2 ∨ (((p1 ∧ (p4 ∧ p4)) ∧ p5) → p5)) ∨ (p1 → False)) ∨ ((True ∧ p3) ∧ ((((False → p3) ∨ p1) ∧ p4) ∨ p4))) → p4) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_41402741975663954979950602030 : ((((((p3 ∨ (False ∨ (False ∧ ((True ∨ p2) → True)))) ∧ (p1 ∧ p5)) ∧ p4) ∨ (True ∧ (((p4 ∧ True) ∨ p4) → (p3 ∨ p1)))) ∨ True) ∨ p4) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_213173764939583933489311735685 : ((((True ∨ p5) ∨ False) ∧ p2) ∨ ((((p2 ∨ (False ∨ (False ∨ p5))) ∧ p5) ∨ False) ∨ (((p3 ∨ p5) ∨ True) ∨ ((p5 ∧ (p3 ∨ p5)) ∨ p4)))) := by
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
theorem thm_5_vars_678097720767264882772135425642 : (((((p3 → (((p2 ∧ p3) → (True ∧ ((p4 → (p1 → p3)) → p4))) ∧ False)) → (p1 ∨ (p2 ∨ p3))) ∨ (((p3 → p2) → False) → p3)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_147885141349369258859724094990 : (((((p3 ∨ ((True → ((True ∨ (p1 ∨ p2)) → (p4 ∧ False))) → p3)) ∨ (p3 → p4)) ∧ p1) ∧ (False ∨ p1)) ∨ ((p2 → False) ∨ (p1 ∨ True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_346979105325868915840210167779 : (p3 → (((p3 → (((((True → p1) ∧ p5) → (p1 ∨ p2)) → p5) ∨ p2)) → (False ∨ p3)) ∧ (((p3 ∧ ((p2 ∨ p4) ∨ p2)) ∧ False) ∨ True))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h2
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_720698834018948498523364405613 : ((((((p5 ∨ False) → True) → p5) → (((p4 ∧ (True ∧ (False ∧ ((((False → p3) → p1) ∧ True) ∨ (p5 ∨ (p2 ∧ p1)))))) ∧ p2) ∧ p1)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_51865138414955483730758095425 : (((((p2 ∨ ((((p4 → (p3 ∨ p4)) ∧ p2) ∧ p4) ∨ p1)) ∨ (p2 ∨ p1)) ∨ True) ∨ ((p2 → (p4 → (p5 ∧ (False ∧ p5)))) → False)) ∨ p2) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_134979360161345659466632432090 : (((((p4 ∨ p2) ∧ True) → ((False ∨ ((p2 ∨ (((p1 ∧ p2) ∧ p4) ∨ True)) ∨ (False → p1))) ∧ False)) ∧ (False ∨ p1)) ∨ (p3 → (p1 ∨ True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_159274247379743635095670650369 : ((p4 → ((p3 ∨ ((False ∨ False) → (p1 ∧ (p5 → (p3 ∧ ((p1 ∧ (False ∧ True)) → p4)))))) → False)) ∨ (((p3 ∨ (False ∨ True)) ∨ p5) ∨ p5)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_66820472737005504887520376948 : ((True → (True → ((((p4 ∨ False) ∨ p2) ∧ p5) ∨ (((True ∧ (((p3 → False) ∨ p1) ∧ (p3 ∧ (False ∧ p1)))) ∧ False) ∨ (True ∨ p3))))) ∨ False) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_226731632940104533642519702990 : (((p1 ∧ p4) → False) ∨ ((False ∨ (((p1 → (p4 ∧ p1)) ∧ p3) ∨ ((False ∧ ((((p4 ∨ p1) ∨ (p3 ∧ p3)) → True) → p3)) ∨ p2))) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_51432419376824630699639689444 : (((((p3 ∨ ((False ∧ p4) ∧ ((p2 ∧ p3) → p1))) ∨ (False ∨ (True ∨ p4))) ∨ (p4 → p4)) → (((p5 ∧ True) → True) → (p4 → p1))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_197972367855598777481917614080 : (((False ∨ p2) ∧ (p4 ∧ ((p1 → p2) → p4))) ∨ (True → ((((p4 → (((p1 → True) ∨ ((True ∧ True) ∧ p3)) ∧ p1)) ∧ False) → True) → True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_50310503050010436228390324503 : ((((((False → (p4 ∨ (True ∨ False))) → (p2 ∧ False)) ∨ (p2 ∨ p4)) ∨ (((True ∧ p5) ∧ p1) → p4)) ∨ (p4 ∧ (p5 ∧ (p2 → p4)))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_53516947985174956668152549398 : (((False → ((((p5 ∨ p1) → (p2 ∨ p5)) → p5) → (False ∧ p4))) → ((p4 ∧ ((((True ∨ p5) ∨ False) ∨ p2) ∨ p2)) ∧ (True ∨ p4))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_137518441256771406660184985408 : ((p5 ∧ ((p2 ∨ (p2 ∧ p1)) ∨ (((False ∨ (p3 ∧ True)) → ((True ∨ p2) ∨ True)) ∧ (p1 ∨ ((p1 → p4) ∨ p3))))) ∨ ((p5 ∧ False) → p2)) := by
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
theorem thm_5_vars_683612351221649723737226867504 : (((((((((p4 ∨ (p3 ∧ p2)) → ((True → True) → p1)) ∨ p5) ∨ p3) ∨ (p1 ∧ p1)) ∧ p1) ∨ (False ∨ (p4 ∧ (p3 ∨ (p3 ∧ True))))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_802632027813289022457497898061 : (((p2 → (True → ((((p2 → p1) → (p3 → p3)) ∧ (False ∧ False)) ∨ ((((p2 ∧ ((True ∨ p1) ∨ p5)) ∨ (p5 ∨ p2)) → p5) ∨ True)))) ∨ p4) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_134122897453887660862728577588 : ((((((True → p5) → (p3 ∧ p5)) ∧ (((p3 ∧ (p3 ∧ ((False → p4) → p2))) → p5) ∨ False)) ∨ (p3 → p2)) ∨ p1) ∨ ((False → p5) ∨ p5)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_171713901555391456498819513402 : (((((p1 ∧ (p2 ∨ (((False ∨ p1) ∧ p4) ∨ (p4 ∨ True)))) ∧ True) ∧ p1) → p2) ∨ ((False ∨ p5) ∨ ((p2 → (p2 ∨ False)) ∨ (p3 ∧ p1)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_230374017898512120707590104515 : (((p3 ∨ False) ∧ p5) → (((p3 ∨ False) ∧ (((p3 ∨ p4) ∨ p2) → ((p3 → (p4 → (p1 ∨ p5))) ∨ p3))) → ((p4 → False) → (p4 → p2)))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Implications on the right can always be decomposed.
  intro h3
  -- Implications on the right can always be decomposed.
  intro h4
  -- Conjunctions on the left can always be decomposed.
  let h5 := h2.left
  let h6 := h2.right
  -- Disjunctions on the left can always be decomposed.
  cases h5
  case inl h7 =>
    -- Conjunctions on the left can always be decomposed.
    let h8 := h1.left
    let h9 := h1.right
    -- Disjunctions on the left can always be decomposed.
    cases h8
    case inl h10 =>
      -- We want to use the implication h3 based on <expert-advice>. So we show its premise.
      have h11 : p4 := by
        -- One of the premise coincides with the conclusion.
        exact h4
      -- We have shown the premise of h3, we can now drive its conclusion.
      let h12 := h3 h11
      -- False on the left can always be used.
      apply False.elim h12
    case inr h13 =>
      -- False on the left can always be used.
      apply False.elim h13
  case inr h14 =>
    -- False on the left can always be used.
    apply False.elim h14



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_112125957575607930062982327250 : (((True ∧ (p2 ∧ (((True → p4) → ((True → (p4 ∨ p1)) ∧ (p3 ∧ (((p2 ∨ True) ∧ p5) ∨ (False ∧ p5))))) ∧ p5))) ∨ True) ∨ (p2 ∧ p5)) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_197037244893455890530150639605 : ((((p5 → (p3 ∨ p3)) → (p5 ∧ False)) ∨ True) ∨ ((p3 ∧ p2) → (False ∧ (((p4 → p5) ∧ p3) → ((((p4 ∧ p1) ∨ p5) → p5) → p5))))) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_44615749565948768066372157645 : ((((((True ∧ (p4 ∨ p3)) ∨ p5) ∧ p3) ∧ ((((False ∨ ((p4 ∧ True) → p3)) ∨ (p1 ∧ p1)) ∧ (False ∧ p2)) → (p4 ∧ p3))) → p4) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_672109322146146456470320356473 : (((((((p5 ∨ p4) ∨ True) → (((p5 → (p4 ∧ p2)) → ((p3 ∧ p5) → (p1 → (p3 ∨ p3)))) → p3)) ∨ p5) → ((p1 → p5) ∧ p2)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_56398917068518296609928661663 : ((((p4 ∧ (p4 ∧ True)) → False) → (((p2 ∧ (False ∨ (True ∧ ((((p3 → p3) → (p1 ∧ (p5 ∧ p3))) ∨ p5) ∧ p3)))) ∨ True) ∨ p2)) ∨ p4) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_228225156313865227120990199536 : ((p5 ∧ (p3 ∨ p4)) ∨ (((p3 ∧ p3) → ((p2 → p1) ∨ (p2 → (p4 ∨ ((False ∨ (False ∧ (p3 ∧ p1))) ∨ False))))) → ((p1 ∨ False) → p1))) := by
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
    exact h3
  case inr h4 =>
    -- False on the left can always be used.
    apply False.elim h4



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_27508680915096034012524828257 : (((p4 ∧ p2) → ((((p5 ∨ p3) → (p3 → p5)) → (p3 ∧ p1)) ∨ (p2 ∨ ((True → ((True ∨ p1) → (p2 ∧ (False → p5)))) ∨ False)))) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- One of the premise coincides with the conclusion.
  exact h3
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_352011534369587209269179979180 : (p4 → ((p3 ∧ (p3 ∨ (p5 ∧ (p5 ∧ (p1 → p3))))) ∨ (((p3 → ((p1 → (True ∨ p1)) ∨ p5)) ∧ p5) → (True ∨ (True ∧ (p1 ∨ p4)))))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h2
  -- Conjunctions on the left can always be decomposed.
  let h3 := h2.left
  let h4 := h2.right
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_63044294918258173706955054762 : ((p5 ∧ ((((((p2 ∨ p1) → p3) → (p1 ∨ p4)) → (False ∨ (((p5 ∧ p3) → (p4 ∧ True)) → (p2 ∨ False)))) → (p5 ∧ False)) ∧ False)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_652774352721631103757516584134 : ((((p2 ∨ (p4 ∧ (((p2 ∧ (p2 → ((p5 ∧ p5) ∧ p1))) → (p4 ∨ p2)) ∨ (True ∨ ((p3 ∨ (p1 ∨ p3)) → False))))) ∧ (p5 → False)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_53140664309693921132824992127 : ((((p5 ∧ (p3 ∧ (p1 ∧ (p2 → ((p2 ∨ p3) → p3))))) ∧ p1) ∨ (((p5 → False) → (p5 ∨ True)) ∧ (((True → False) → p4) ∨ True))) ∨ p3) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_259111298137072183204608755580 : ((True → p5) → (False ∨ (p1 → (p3 ∨ (((p3 ∨ False) ∧ p2) ∨ (((((p5 → p4) ∧ True) → (True ∧ p1)) → p1) ∨ ((p3 ∨ p5) ∨ p2))))))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h2
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h3
  -- One of the premise coincides with the conclusion.
  exact h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_618346001303676577886953303228 : (((((p5 ∧ (False ∨ (False ∧ p5))) ∨ (p5 ∧ ((False → False) → (p3 → (((p1 ∧ p1) → (p3 ∧ p2)) ∨ (p1 ∨ (False ∨ p2))))))) ∨ True) ∨ False) ∧ True) := by
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
theorem thm_5_vars_49528914108832228978905065565 : ((((((False ∨ (p5 ∨ False)) ∨ p4) ∨ (p3 → (((p4 → p2) → (p3 ∧ p2)) ∨ (p3 → False)))) ∨ (p3 → p1)) → ((True ∧ False) ∨ False)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_311157741080391412112276705173 : (p2 ∨ ((p3 ∧ p3) → ((((p2 ∧ p4) → p5) → ((p1 → p3) → (((p3 → (True ∧ p4)) ∨ (p4 ∨ p4)) ∨ True))) ∧ ((p5 ∧ p5) → True)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h2
  -- Implications on the right can always be decomposed.
  intro h3
  -- Conjunctions on the left can always be decomposed.
  let h4 := h1.left
  let h5 := h1.right
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- Implications on the right can always be decomposed.
  intro h6
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_680980776814435929469747609535 : (((((p4 ∨ p3) ∨ ((p4 ∨ (((p2 ∧ p3) → False) → p2)) ∧ ((((True → p3) ∨ False) ∨ p3) ∧ False))) → (p4 ∧ (False ∨ (p5 ∨ p5)))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_184062229712504277366499007169 : ((((((p2 ∧ p1) ∧ p3) ∧ (True ∨ p3)) → (p4 ∨ p4)) ∨ False) ∨ (p2 ∨ ((p2 → False) → (((p2 → (p3 → (p1 ∨ p2))) ∨ p5) ∨ p1)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
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
  exact h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_266242214219121884525806998987 : (True ∧ (p5 → (((p5 ∧ ((p3 ∧ ((p4 → ((p2 ∨ p3) ∨ p5)) ∨ False)) ∨ p5)) ∧ (((p4 ∨ (p3 ∧ p3)) ∧ p3) → (p2 ∧ p1))) ∨ p5))) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_337634159072355956605222884065 : (p1 → (((p2 ∧ True) → ((((p3 ∨ (p3 ∧ (False ∨ ((p2 ∧ p5) ∨ p5)))) → False) ∨ True) ∨ True)) ∧ (False ∨ ((p2 ∧ p1) ∨ (False → False))))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h2
  -- Conjunctions on the left can always be decomposed.
  let h3 := h2.left
  let h4 := h2.right
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h5
  -- False on the left can always be used.
  apply False.elim h5



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_307325509229553521941672453348 : (p1 ∨ (p3 ∨ ((True ∨ ((((p4 ∧ False) ∨ p1) ∧ False) ∨ (False ∧ p4))) ∧ ((((False ∨ p4) ∨ True) ∧ p2) → (((False ∧ p3) ∨ True) ∨ p3))))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro
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
      -- False on the left can always be used.
      apply False.elim h5
    case inr h6 =>
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- True on the right can always be proven directly.
      apply True.intro
  case inr h7 =>
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_316672471156436179156708647801 : (p3 ∨ (p5 ∨ ((p4 ∧ (p4 ∨ (((p5 ∧ p4) ∨ (p3 → (p4 → p4))) ∧ (((False → (p5 ∧ (False ∧ False))) ∧ (False ∨ True)) ∧ True)))) ∨ True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_56196897061313208145482294759 : (((p5 ∧ (p3 → (p4 ∨ p5))) ∨ (p2 → ((p3 ∧ (((p1 ∨ p2) ∧ p1) ∧ (p3 → ((p4 → (p4 ∨ (p4 → p1))) ∨ False)))) ∨ p2))) ∨ False) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_57969344829071493598257484440 : (((p3 → (p3 ∧ False)) → (((p1 ∨ (True ∨ (True ∧ True))) → p1) → ((p3 ∧ p4) → (((p4 → (p2 ∨ True)) ∧ p1) ∧ (p4 ∧ p5))))) ∨ p5) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Implications on the right can always be decomposed.
  intro h3
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h4
  -- Conjunctions on the left can always be decomposed.
  let h5 := h3.left
  let h6 := h3.right
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- Conjunctions on the left can always be decomposed.
  let h7 := h3.left
  let h8 := h3.right
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h9 : p3 := by
    -- One of the premise coincides with the conclusion.
    exact h7
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h10 := h1 h9
  -- We need to get the right conjuct of h10 based on <expert-advice>.
  let h11 := h10.right
  -- False on the left can always be used.
  apply False.elim h11
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Conjunctions on the left can always be decomposed.
  let h12 := h3.left
  let h13 := h3.right
  -- One of the premise coincides with the conclusion.
  exact h13
  -- Conjunctions on the left can always be decomposed.
  let h14 := h3.left
  let h15 := h3.right
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h16 : p3 := by
    -- One of the premise coincides with the conclusion.
    exact h14
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h17 := h1 h16
  -- We need to get the right conjuct of h17 based on <expert-advice>.
  let h18 := h17.right
  -- False on the left can always be used.
  apply False.elim h18



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_158323540704206331930120402432 : (((p3 → (p2 ∧ p4)) → ((p1 → (True ∨ (p2 ∧ ((False ∨ p5) → p3)))) → ((p5 ∧ False) ∧ p2))) ∨ (p3 ∨ ((p2 ∧ (p4 ∧ True)) → p2))) := by
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
  -- One of the premise coincides with the conclusion.
  exact h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_197382775124436206401295835417 : (((p2 ∨ ((True ∨ p3) ∧ (p4 → False))) → p1) ∨ (((p4 ∨ (p3 ∨ False)) ∧ p5) → ((p1 → p4) ∨ ((False ∧ True) ∨ ((p4 ∨ p5) ∨ p4))))) := by
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
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h4
  case inr h5 =>
    -- Disjunctions on the left can always be decomposed.
    cases h5
    case inl h6 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- One of the premise coincides with the conclusion.
      exact h3
    case inr h7 =>
      -- False on the left can always be used.
      apply False.elim h7



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_193454867868416227508815795928 : (((p5 → p1) ∧ (p1 ∧ ((p2 → p4) → (p4 → p5)))) → ((p5 ∧ (((p1 → (p3 ∧ ((p3 → False) ∨ p5))) → (p2 ∨ p1)) ∨ p4)) → p1)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Conjunctions on the left can always be decomposed.
  let h3 := h2.left
  let h4 := h2.right
  -- Disjunctions on the left can always be decomposed.
  cases h4
  case inl h5 =>
    -- Conjunctions on the left can always be decomposed.
    let h6 := h1.left
    let h7 := h1.right
    -- Conjunctions on the left can always be decomposed.
    let h8 := h7.left
    let h9 := h7.right
    -- One of the premise coincides with the conclusion.
    exact h8
  case inr h10 =>
    -- Conjunctions on the left can always be decomposed.
    let h11 := h1.left
    let h12 := h1.right
    -- Conjunctions on the left can always be decomposed.
    let h13 := h12.left
    let h14 := h12.right
    -- One of the premise coincides with the conclusion.
    exact h13



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_134475697228638269445876842579 : ((((True → (False ∨ (((p1 ∧ (((p2 ∧ p4) ∨ False) ∨ p5)) ∧ (p1 ∧ (p5 ∧ (p5 → p5)))) → p4))) ∧ True) → p4) ∨ ((p2 → p1) → True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_111703725724579801281253459099 : (((((((False ∧ (True → p4)) ∨ (p3 → (p1 ∨ True))) → (p2 ∧ ((True → (True → p5)) ∨ False))) → (p3 ∧ False)) → False) ∨ True) ∨ (p1 → p4)) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



