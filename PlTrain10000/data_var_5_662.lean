variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_114801041531725999455507896793 : ((((p4 ∨ (((p4 → p3) → p3) ∧ p5)) ∧ (p5 → ((p2 ∨ p5) ∨ p4))) ∧ (p2 ∧ ((True ∨ True) → ((True ∧ p5) ∧ p1)))) ∨ (p5 → True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_309334790759363411308938820596 : (p2 ∨ (((p5 → ((False → p1) → ((((p2 ∧ p4) ∧ False) → p1) → ((((p5 → True) ∧ False) ∧ True) ∧ p4)))) ∨ (p2 ∨ True)) ∨ (p4 ∧ True))) := by
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



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_174721083536307141432517543504 : ((((p5 ∧ p5) ∧ p2) → (((p2 ∧ p1) ∨ True) ∧ (((p3 ∧ p2) ∧ p5) ∨ False))) → ((p1 → True) ∧ ((True → (False ∧ (p3 ∨ p4))) → p4))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h2
  -- True on the right can always be proven directly.
  apply True.intro
  -- Implications on the right can always be decomposed.
  intro h3
  -- We want to use the implication h3 based on <expert-advice>. So we show its premise.
  have h4 : True := by
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h3, we can now drive its conclusion.
  let h5 := h3 h4
  -- We need to get the left conjuct of h5 based on <expert-advice>.
  let h6 := h5.left
  -- False on the left can always be used.
  apply False.elim h6



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_77827741265059078813463716062 : (((False ∨ ((((((((p3 ∨ ((p3 ∨ p1) → p5)) ∧ ((p3 → False) → False)) ∧ True) → p3) ∧ p2) → True) → (p1 → p3)) ∨ True)) → p2) → p2) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h2 : (False ∨ ((((((((p3 ∨ ((p3 ∨ p1) → p5)) ∧ ((p3 → False) → False)) ∧ True) → p3) ∧ p2) → True) → (p1 → p3)) ∨ True)) := by
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h3 := h1 h2
  -- One of the premise coincides with the conclusion.
  exact h3



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_598988843335016534769541496912 : (((((p2 ∨ p5) ∧ ((((p4 → (False ∧ (p3 ∧ (p4 → p5)))) ∧ (p5 ∧ (p5 ∧ (True → ((True → p2) → p4))))) ∨ p3) → p1)) ∧ p5) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_185528491740039443454897805489 : ((p3 ∨ (((p2 ∨ (p4 ∨ p2)) ∨ p2) ∧ ((p5 ∧ p4) ∨ p2))) ∨ ((((((p4 ∨ (p4 ∨ True)) ∧ p3) ∨ p2) ∧ p5) ∧ p2) → (False → p2))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- False on the left can always be used.
  apply False.elim h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_666803710121836729426808249181 : (((((p1 ∧ (p4 ∧ ((p3 → p1) ∧ (p3 ∨ p4)))) ∨ (p5 → (((p5 ∨ (p1 ∧ p3)) ∧ False) → (p5 → p5)))) ∧ ((p1 ∧ False) ∨ p4)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_180626971176974818298547495812 : (((p1 → (p5 ∧ (p4 ∧ (p3 ∧ p1)))) ∧ (((p1 ∨ p2) ∨ True) ∨ p5)) → (((False → p2) ∨ False) → (p1 → ((p3 → (False → p4)) ∧ p4)))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Implications on the right can always be decomposed.
  intro h3
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h4
  -- Implications on the right can always be decomposed.
  intro h5
  -- False on the left can always be used.
  apply False.elim h5
  -- Disjunctions on the left can always be decomposed.
  cases h2
  case inl h6 =>
    -- Conjunctions on the left can always be decomposed.
    let h7 := h1.left
    let h8 := h1.right
    -- Disjunctions on the left can always be decomposed.
    cases h8
    case inl h9 =>
      -- Disjunctions on the left can always be decomposed.
      cases h9
      case inl h10 =>
        -- Disjunctions on the left can always be decomposed.
        cases h10
        case inl h11 =>
          -- We want to use the implication h7 based on <expert-advice>. So we show its premise.
          have h12 : p1 := by
            -- One of the premise coincides with the conclusion.
            exact h11
          -- We have shown the premise of h7, we can now drive its conclusion.
          let h13 := h7 h12
          -- We need to get the right conjuct of h13 based on <expert-advice>.
          let h14 := h13.right
          -- We need to get the left conjuct of h14 based on <expert-advice>.
          let h15 := h14.left
          -- One of the premise coincides with the conclusion.
          exact h15
        case inr h16 =>
          -- We want to use the implication h7 based on <expert-advice>. So we show its premise.
          have h17 : p1 := by
            -- One of the premise coincides with the conclusion.
            exact h3
          -- We have shown the premise of h7, we can now drive its conclusion.
          let h18 := h7 h17
          -- We need to get the right conjuct of h18 based on <expert-advice>.
          let h19 := h18.right
          -- We need to get the left conjuct of h19 based on <expert-advice>.
          let h20 := h19.left
          -- One of the premise coincides with the conclusion.
          exact h20
      case inr h21 =>
        -- We want to use the implication h7 based on <expert-advice>. So we show its premise.
        have h22 : p1 := by
          -- One of the premise coincides with the conclusion.
          exact h3
        -- We have shown the premise of h7, we can now drive its conclusion.
        let h23 := h7 h22
        -- We need to get the right conjuct of h23 based on <expert-advice>.
        let h24 := h23.right
        -- We need to get the left conjuct of h24 based on <expert-advice>.
        let h25 := h24.left
        -- One of the premise coincides with the conclusion.
        exact h25
    case inr h26 =>
      -- We want to use the implication h7 based on <expert-advice>. So we show its premise.
      have h27 : p1 := by
        -- One of the premise coincides with the conclusion.
        exact h3
      -- We have shown the premise of h7, we can now drive its conclusion.
      let h28 := h7 h27
      -- We need to get the right conjuct of h28 based on <expert-advice>.
      let h29 := h28.right
      -- We need to get the left conjuct of h29 based on <expert-advice>.
      let h30 := h29.left
      -- One of the premise coincides with the conclusion.
      exact h30
  case inr h31 =>
    -- False on the left can always be used.
    apply False.elim h31



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_172510470403844952919898579627 : ((((False → p4) ∨ p5) ∧ ((p3 ∧ (True → (p3 ∨ (p3 → p2)))) ∨ (p5 ∧ p3))) ∨ (((False ∧ True) ∨ p1) ∨ ((p1 ∧ True) ∨ (p1 → True)))) := by
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
theorem thm_5_vars_78152752788383431332994146808 : (((p1 → (((True → ((p3 ∧ (False ∧ True)) ∧ p2)) → (((p3 ∨ p4) ∧ (p5 ∨ (p4 ∨ False))) → p5)) ∨ (p5 ∨ (False → p1)))) → p4) → p4) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h2 : (p1 → (((True → ((p3 ∧ (False ∧ True)) ∧ p2)) → (((p3 ∨ p4) ∧ (p5 ∨ (p4 ∨ False))) → p5)) ∨ (p5 ∨ (False → p1)))) := by
    -- Implications on the right can always be decomposed.
    intro h3
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h4
    -- False on the left can always be used.
    apply False.elim h4
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h5 := h1 h2
  -- One of the premise coincides with the conclusion.
  exact h5



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_726201831563500193510461657000 : (((((p5 ∧ p5) ∨ p1) ∨ ((p3 ∨ (((True ∨ (((False ∧ (p2 ∧ p2)) → (False ∧ p4)) → p2)) ∧ (p1 ∧ (p3 → p1))) ∨ p5)) ∨ True)) ∨ False) ∧ True) := by
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
theorem thm_5_vars_624152212118661998366033808257 : ((((p2 ∨ (p2 ∨ ((p2 ∧ False) ∨ (((p2 → (p4 ∧ ((p2 ∧ False) ∧ p4))) → p3) ∨ ((((p1 ∧ p4) ∧ p4) ∨ p3) ∨ p1))))) ∨ True) ∨ p3) ∧ True) := by
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
theorem thm_5_vars_790884936727935869687876611393 : (((p5 ∨ (p3 → ((((p1 ∨ False) ∨ (p5 ∨ p3)) ∧ (((p4 ∧ p5) → True) ∨ p3)) → ((p3 ∧ (((True ∨ p1) ∨ p4) → False)) → p4)))) ∨ p3) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
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
  let h6 := h2.left
  let h7 := h2.right
  -- Disjunctions on the left can always be decomposed.
  cases h6
  case inl h8 =>
    -- Disjunctions on the left can always be decomposed.
    cases h8
    case inl h9 =>
      -- Disjunctions on the left can always be decomposed.
      cases h7
      case inl h10 =>
        -- We want to use the implication h5 based on <expert-advice>. So we show its premise.
        have h11 : ((True ∨ p1) ∨ p4) := by
          -- Show the left disjunct based on <expert-advice>.
          apply Or.inl
          -- Show the left disjunct based on <expert-advice>.
          apply Or.inl
          -- True on the right can always be proven directly.
          apply True.intro
        -- We have shown the premise of h5, we can now drive its conclusion.
        let h12 := h5 h11
        -- False on the left can always be used.
        apply False.elim h12
      case inr h13 =>
        -- We want to use the implication h5 based on <expert-advice>. So we show its premise.
        have h14 : ((True ∨ p1) ∨ p4) := by
          -- Show the left disjunct based on <expert-advice>.
          apply Or.inl
          -- Show the left disjunct based on <expert-advice>.
          apply Or.inl
          -- True on the right can always be proven directly.
          apply True.intro
        -- We have shown the premise of h5, we can now drive its conclusion.
        let h15 := h5 h14
        -- False on the left can always be used.
        apply False.elim h15
    case inr h16 =>
      -- False on the left can always be used.
      apply False.elim h16
  case inr h17 =>
    -- Disjunctions on the left can always be decomposed.
    cases h17
    case inl h18 =>
      -- Disjunctions on the left can always be decomposed.
      cases h7
      case inl h19 =>
        -- We want to use the implication h5 based on <expert-advice>. So we show its premise.
        have h20 : ((True ∨ p1) ∨ p4) := by
          -- Show the left disjunct based on <expert-advice>.
          apply Or.inl
          -- Show the left disjunct based on <expert-advice>.
          apply Or.inl
          -- True on the right can always be proven directly.
          apply True.intro
        -- We have shown the premise of h5, we can now drive its conclusion.
        let h21 := h5 h20
        -- False on the left can always be used.
        apply False.elim h21
      case inr h22 =>
        -- We want to use the implication h5 based on <expert-advice>. So we show its premise.
        have h23 : ((True ∨ p1) ∨ p4) := by
          -- Show the left disjunct based on <expert-advice>.
          apply Or.inl
          -- Show the left disjunct based on <expert-advice>.
          apply Or.inl
          -- True on the right can always be proven directly.
          apply True.intro
        -- We have shown the premise of h5, we can now drive its conclusion.
        let h24 := h5 h23
        -- False on the left can always be used.
        apply False.elim h24
    case inr h25 =>
      -- Disjunctions on the left can always be decomposed.
      cases h7
      case inl h26 =>
        -- We want to use the implication h5 based on <expert-advice>. So we show its premise.
        have h27 : ((True ∨ p1) ∨ p4) := by
          -- Show the left disjunct based on <expert-advice>.
          apply Or.inl
          -- Show the left disjunct based on <expert-advice>.
          apply Or.inl
          -- True on the right can always be proven directly.
          apply True.intro
        -- We have shown the premise of h5, we can now drive its conclusion.
        let h28 := h5 h27
        -- False on the left can always be used.
        apply False.elim h28
      case inr h29 =>
        -- We want to use the implication h5 based on <expert-advice>. So we show its premise.
        have h30 : ((True ∨ p1) ∨ p4) := by
          -- Show the left disjunct based on <expert-advice>.
          apply Or.inl
          -- Show the left disjunct based on <expert-advice>.
          apply Or.inl
          -- True on the right can always be proven directly.
          apply True.intro
        -- We have shown the premise of h5, we can now drive its conclusion.
        let h31 := h5 h30
        -- False on the left can always be used.
        apply False.elim h31
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_148890778363184557598411449706 : ((((p1 ∧ p1) → (p4 ∨ p3)) ∨ (p1 ∧ (((p4 ∧ (((p1 ∧ p1) ∧ (False ∨ p4)) → p3)) ∧ True) ∨ False))) ∨ (((p3 ∨ p4) ∨ True) → True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_171975164709252802612514667987 : (((p1 ∨ (p2 → (((True ∧ p5) ∨ ((p4 ∨ False) ∧ False)) ∧ p2))) ∧ (p5 → p5)) ∨ (((True ∧ True) → ((p5 ∨ (p1 ∧ p5)) ∨ True)) → True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_55140446952850295682040958073 : (((((False ∧ (p4 ∧ p2)) ∧ p1) ∨ False) ∨ (((((False → (False ∨ p5)) ∨ False) ∨ (p3 → (True → False))) ∧ p1) ∨ ((p3 ∧ p3) ∨ p2))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_215876215948840342398235931700 : ((p2 ∨ (p4 → (p2 → False))) ∨ ((False ∨ True) ∧ (((((p4 ∧ False) → p1) → ((p3 → (p1 → False)) ∧ (False ∨ True))) ∧ p3) ∨ (False → p4)))) := by
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
  -- Implications on the right can always be decomposed.
  intro h1
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_318590182157426510028957118769 : (p4 ∨ ((((p4 → False) ∧ ((((p5 ∨ ((p1 ∨ p4) ∨ True)) ∨ (p4 ∨ p4)) → False) ∧ p3)) ∧ (p1 ∨ ((True → p2) ∨ p2))) ∨ (p4 → True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_65410823315984444881234683451 : ((p3 ∨ ((p5 ∨ (True ∨ (p2 ∧ False))) → (p5 ∧ (((p5 ∧ ((p3 → p4) ∧ True)) → p4) ∨ (True ∧ ((p5 → (p2 ∨ p4)) ∧ p5)))))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_153755833548789646881270770038 : ((p4 → (((((p1 ∧ (p4 ∧ p4)) ∨ ((p2 → ((False ∨ p1) → p5)) ∧ (p5 → False))) → p2) ∨ p4) ∨ p5)) → (((p5 → p3) ∨ True) ∧ True)) := by
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
theorem thm_5_vars_253626705861583189749646600923 : ((p1 ∧ True) → ((((p2 ∨ (p4 → p2)) ∧ (p2 ∧ False)) ∧ p3) ∨ ((((p5 ∨ p3) ∨ (True ∧ p2)) ∧ p1) ∨ ((p1 ∨ p5) → (p1 ∨ p4))))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h4
  -- Disjunctions on the left can always be decomposed.
  cases h4
  case inl h5 =>
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- One of the premise coincides with the conclusion.
    exact h5
  case inr h6 =>
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- One of the premise coincides with the conclusion.
    exact h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_326900918244011809403154045625 : (True → ((((p2 ∧ ((False ∧ (p5 ∨ ((((p5 ∨ (((p2 ∧ p1) ∧ p4) ∨ True)) ∨ p3) → p3) ∧ (p5 ∨ False)))) → p2)) ∧ p4) → p1) ∨ True)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_663321638363024164245549614738 : (((((False → p2) ∨ ((((p1 ∨ (p3 → p2)) ∨ p5) ∧ p4) ∧ ((p4 → True) ∧ ((p2 ∨ True) ∨ (True ∧ (p1 → True)))))) → (p3 → False)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_41351913069550811073882778011 : ((((p5 ∨ (p3 ∧ ((((p3 ∧ ((p1 ∨ False) → False)) → (p3 ∨ False)) → p5) ∨ p2))) ∨ (p1 → (p2 ∨ (True → (True ∧ p1))))) ∨ True) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_181180202660627851577710635297 : ((p1 ∧ ((True ∨ (p3 → p4)) ∧ (((p4 → (p2 ∧ p4)) ∨ p4) ∨ p3))) → (((p2 ∧ p2) ∨ True) ∧ (True ∨ ((True → False) ∧ (p3 ∨ True))))) := by
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
    -- Disjunctions on the left can always be decomposed.
    cases h5
    case inl h7 =>
      -- Disjunctions on the left can always be decomposed.
      cases h7
      case inl h8 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- True on the right can always be proven directly.
        apply True.intro
      case inr h9 =>
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
    -- Disjunctions on the left can always be decomposed.
    cases h5
    case inl h12 =>
      -- Disjunctions on the left can always be decomposed.
      cases h12
      case inl h13 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- True on the right can always be proven directly.
        apply True.intro
      case inr h14 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- True on the right can always be proven directly.
        apply True.intro
    case inr h15 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- True on the right can always be proven directly.
      apply True.intro
  -- Conjunctions on the left can always be decomposed.
  let h16 := h1.left
  let h17 := h1.right
  -- Conjunctions on the left can always be decomposed.
  let h18 := h17.left
  let h19 := h17.right
  -- Disjunctions on the left can always be decomposed.
  cases h18
  case inl h20 =>
    -- Disjunctions on the left can always be decomposed.
    cases h19
    case inl h21 =>
      -- Disjunctions on the left can always be decomposed.
      cases h21
      case inl h22 =>
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- True on the right can always be proven directly.
        apply True.intro
      case inr h23 =>
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- True on the right can always be proven directly.
        apply True.intro
    case inr h24 =>
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- True on the right can always be proven directly.
      apply True.intro
  case inr h25 =>
    -- Disjunctions on the left can always be decomposed.
    cases h19
    case inl h26 =>
      -- Disjunctions on the left can always be decomposed.
      cases h26
      case inl h27 =>
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- True on the right can always be proven directly.
        apply True.intro
      case inr h28 =>
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- True on the right can always be proven directly.
        apply True.intro
    case inr h29 =>
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- True on the right can always be proven directly.
      apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_52261115975207812605627817224 : (((p4 ∨ (((p5 ∨ (((p3 ∧ False) → (p4 ∨ p1)) → (False ∧ p5))) → p2) ∨ p5)) → ((p1 ∨ False) ∨ ((p4 → (p2 ∨ p5)) → True))) ∨ p3) := by
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
    -- True on the right can always be proven directly.
    apply True.intro
  case inr h4 =>
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
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Implications on the right can always be decomposed.
      intro h8
      -- True on the right can always be proven directly.
      apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_233319469653841687568927141674 : ((True ∨ (True → p4)) → (((p1 → ((((((((p4 ∧ (p4 ∨ p3)) ∨ (p4 ∧ p2)) ∧ p2) ∨ p4) → True) → p4) ∧ p5) ∧ True)) ∨ p5) ∨ True)) := by
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
theorem thm_5_vars_125884475277299996557687969540 : (((p3 ∧ True) → (p5 ∧ ((((((((p2 → p1) → False) → p3) ∧ p4) ∧ (p4 → (p4 ∧ (p4 → p3)))) ∨ True) → p5) ∨ p4))) → (p1 ∨ True)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_610488733610857255535195905188 : ((((((p3 ∨ ((((((True ∧ (((True ∧ p3) ∧ True) ∨ p1)) → (p3 ∨ False)) → p1) ∨ (p2 → p4)) ∧ p5) ∨ p3)) → p5) → p1) ∨ p3) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_226277894016451989389981838413 : (((p4 ∨ False) ∨ p2) ∨ ((p3 ∨ (((((False → ((p5 → (p4 ∨ True)) ∨ False)) → (True → p3)) ∧ p4) ∨ True) ∧ (p4 → p3))) ∨ (p3 → p3))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_61583538715132261994759765669 : ((p1 ∧ (((p1 ∨ p5) → (p1 → True)) → (p1 ∨ ((p2 → ((p2 ∧ (((p5 → False) → p1) → True)) → ((p4 → p4) ∧ True))) → p3)))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_184447468936013305322223924427 : (((p3 ∧ (p1 ∧ (p3 ∧ (p1 ∧ (p1 ∨ p3))))) ∧ (True → True)) ∨ ((((False → (p2 → p1)) → False) → p3) → ((p3 ∨ (False ∧ p4)) → True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_111898185248829382117975807996 : ((((p2 → ((False → (p5 → (((p2 → p1) ∨ p5) → (False ∧ p4)))) → False)) ∨ (False → ((p5 → p1) ∧ (p5 → False)))) ∨ True) ∨ (False ∨ False)) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_700384032331857051015062859018 : ((((p4 ∧ (p3 → (True → (p5 ∨ ((False ∧ (p3 ∧ p1)) ∨ False))))) → (((p3 ∨ ((True → p3) ∨ True)) ∧ (p5 ∨ (p5 ∨ True))) ∨ p3)) ∨ p2) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
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
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_136851945467516954473099965918 : (((p4 ∧ False) ∨ (p2 ∧ (((p3 ∨ ((((p2 → (p1 ∧ (p1 ∧ p2))) ∨ (True ∧ False)) → p1) → p4)) ∧ p1) → p2))) ∨ (p5 → (False → p1))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- False on the left can always be used.
  apply False.elim h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_22940251281098148637427667453 : (((p4 ∧ (p1 → ((True ∧ p4) ∨ p3))) ∨ (p1 ∨ (p2 → (((p4 ∨ ((((p2 ∧ p5) ∧ False) ∨ p2) → False)) ∨ (p2 ∨ p2)) ∨ False)))) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- One of the premise coincides with the conclusion.
  exact h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_764072749832895119864915630305 : (((p3 ∧ (p2 → ((True → p2) → ((p3 ∨ (p5 → p2)) ∧ ((False ∨ p1) ∧ ((p3 ∧ ((False → p3) → p5)) ∨ ((True → False) → True))))))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_113433529843781001862694717720 : (((((((p4 ∨ ((p1 ∨ ((True → p1) → p5)) ∨ (False → p5))) ∨ ((p4 ∧ p2) ∧ True)) → p2) → p5) ∨ p2) ∨ (p1 → p4)) ∨ (p3 → p3)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_42362497418181798504981523770 : (((p3 ∧ (p3 ∨ (((((((p4 ∧ (p4 → (p5 ∨ p4))) ∧ ((False ∨ p5) ∨ False)) → (p3 ∧ True)) → True) ∨ True) ∨ True) → p4))) ∨ p1) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_319232714166010455417265161686 : (p4 ∨ (((((p1 ∧ (((p1 ∨ True) ∨ (True ∨ False)) ∨ p3)) → p4) ∨ (p1 ∧ p2)) ∨ True) ∧ ((((False ∧ False) ∧ p4) → p3) ∨ (False → False)))) := by
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
  -- Implications on the right can always be decomposed.
  intro h1
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_682102492094154149997612024552 : (((((((p5 ∨ (((p3 ∧ False) ∨ p1) → p4)) → ((p5 → p1) ∧ (p3 → p3))) ∨ p3) → p3) ∧ ((True ∨ ((False ∨ True) ∧ p2)) → p5)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_351423496510443240142582631273 : (p4 → ((p1 ∨ (((((True ∨ p4) → p2) ∨ p4) ∧ ((p2 ∧ ((False → p3) ∧ True)) → p1)) ∧ (p1 ∧ p5))) ∨ (True ∨ (p1 ∨ (p1 → True))))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_115000800453408596935245231488 : (((((p5 ∧ p2) → (True ∧ True)) ∧ ((p3 → (p3 ∧ p3)) ∨ False)) ∧ (p4 ∨ ((p2 ∧ ((p5 ∨ False) ∨ p3)) ∧ (p4 ∧ p1)))) ∨ (p5 ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_52248226128220738403017992566 : (((False ∨ ((p5 ∧ ((p1 → p5) → (True ∨ (((False → p5) → p1) → p3)))) ∧ p1)) → ((p2 → False) ∨ (True ∧ (p1 ∧ (p1 → True))))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_713339753598648383828952606625 : ((((True → ((True ∨ True) ∧ (p5 ∧ p4))) ∨ (p4 ∧ (p3 ∧ ((True ∨ p2) → ((p1 ∨ p3) → (p4 ∧ (p2 → ((p5 ∨ False) ∨ False)))))))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_603448023511891491294820589480 : ((((p3 ∨ ((((True → p1) → (p5 ∨ (p1 ∧ (p4 ∨ p3)))) → ((p1 ∧ ((True ∧ (True ∧ p1)) → p4)) → p3)) ∨ (p4 → p3))) ∧ p4) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_118219830271211721726661047522 : ((p1 ∨ ((((False ∧ (p5 → p4)) → (p4 ∧ ((((p4 → False) ∨ p3) ∧ p1) ∨ ((p1 ∧ p3) ∨ (p4 ∨ p4))))) → False) ∨ p2)) ∨ (p5 → True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_155475657852412394067448484355 : (((True ∨ (p4 ∧ False)) ∧ ((p5 ∨ (p2 ∨ (p2 ∨ ((p1 ∨ (p5 → (True ∨ False))) ∨ p5)))) ∧ True)) ∧ ((p3 ∧ p3) ∨ ((p3 ∧ p3) → True))) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
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
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h2
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_135981160073310044039299110356 : (((((p3 → p5) ∨ ((False ∧ (p5 ∨ p1)) ∨ p3)) → p3) ∨ ((p3 ∨ (True → (((p2 ∨ True) ∨ p3) → p4))) → p2)) ∨ (p4 → (p3 ∨ p4))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_148098249718879216024527464843 : ((((p4 ∨ (((False ∧ p4) ∧ (True ∨ (p4 ∨ (p4 ∧ (p1 ∧ False))))) → p3)) ∧ (p5 → True)) → (p3 → p3)) ∨ ((p2 ∨ (p4 → p4)) ∨ False)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_193278317188652871614219800104 : ((((p4 ∨ True) ∧ True) ∨ (p4 ∨ ((p5 ∧ p2) → False))) → (False ∨ ((p2 ∧ p4) ∨ (((p3 ∧ (True ∧ True)) → ((p3 → True) ∨ p3)) ∨ False)))) := by
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
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- Implications on the right can always be decomposed.
      intro h6
      -- Conjunctions on the left can always be decomposed.
      let h7 := h6.left
      let h8 := h6.right
      -- Conjunctions on the left can always be decomposed.
      let h9 := h8.left
      let h10 := h8.right
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- One of the premise coincides with the conclusion.
      exact h7
    case inr h11 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- Implications on the right can always be decomposed.
      intro h12
      -- Conjunctions on the left can always be decomposed.
      let h13 := h12.left
      let h14 := h12.right
      -- Conjunctions on the left can always be decomposed.
      let h15 := h14.left
      let h16 := h14.right
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- One of the premise coincides with the conclusion.
      exact h13
  case inr h17 =>
    -- Disjunctions on the left can always be decomposed.
    cases h17
    case inl h18 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- Implications on the right can always be decomposed.
      intro h19
      -- Conjunctions on the left can always be decomposed.
      let h20 := h19.left
      let h21 := h19.right
      -- Conjunctions on the left can always be decomposed.
      let h22 := h21.left
      let h23 := h21.right
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- One of the premise coincides with the conclusion.
      exact h20
    case inr h24 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- Implications on the right can always be decomposed.
      intro h25
      -- Conjunctions on the left can always be decomposed.
      let h26 := h25.left
      let h27 := h25.right
      -- Conjunctions on the left can always be decomposed.
      let h28 := h27.left
      let h29 := h27.right
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- One of the premise coincides with the conclusion.
      exact h26



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_231941009738555231013935092054 : (((p1 ∨ True) → p3) → (((p5 → (p1 ∨ ((False ∨ True) → ((True → ((p4 ∨ ((p4 ∧ p3) ∨ p3)) ∨ (p2 ∨ True))) ∧ p2)))) → p3) ∨ p3)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h2 : (p1 ∨ True) := by
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h3 := h1 h2
  -- One of the premise coincides with the conclusion.
  exact h3



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_147344068019806339722705447702 : (((((p5 → ((True → (p4 ∨ p1)) ∧ True)) → ((False ∨ (p4 ∨ True)) ∧ (p4 → p1))) → (True ∧ False)) ∨ p3) ∨ (False → (p1 ∨ (p2 → p2)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_43120298496428089199612147823 : (((((p5 → ((((True ∨ (p5 ∨ p3)) ∧ (True ∧ (True ∧ p2))) ∨ p2) ∧ p3)) ∧ ((((True ∨ True) ∨ p2) → p5) ∨ p5)) ∧ p5) → p3) ∨ p2) := by
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
  -- Disjunctions on the left can always be decomposed.
  cases h5
  case inl h6 =>
    -- We want to use the implication h4 based on <expert-advice>. So we show its premise.
    have h7 : p5 := by
      -- One of the premise coincides with the conclusion.
      exact h3
    -- We have shown the premise of h4, we can now drive its conclusion.
    let h8 := h4 h7
    -- We need to get the right conjuct of h8 based on <expert-advice>.
    let h9 := h8.right
    -- One of the premise coincides with the conclusion.
    exact h9
  case inr h10 =>
    -- We want to use the implication h4 based on <expert-advice>. So we show its premise.
    have h11 : p5 := by
      -- One of the premise coincides with the conclusion.
      exact h3
    -- We have shown the premise of h4, we can now drive its conclusion.
    let h12 := h4 h11
    -- We need to get the right conjuct of h12 based on <expert-advice>.
    let h13 := h12.right
    -- One of the premise coincides with the conclusion.
    exact h13



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_153260802713526901587763495076 : ((False ∨ (((p4 → True) ∨ (((p1 ∧ True) ∨ p3) ∨ p4)) → ((p4 ∧ (p4 ∧ (p5 ∧ False))) ∨ (p3 ∧ p2)))) → (p4 ∨ ((p4 ∨ p3) ∨ p2))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h2 =>
    -- False on the left can always be used.
    apply False.elim h2
  case inr h3 =>
    -- We want to use the implication h3 based on <expert-advice>. So we show its premise.
    have h4 : ((p4 → True) ∨ (((p1 ∧ True) ∨ p3) ∨ p4)) := by
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- Implications on the right can always be decomposed.
      intro h5
      -- True on the right can always be proven directly.
      apply True.intro
    -- We have shown the premise of h3, we can now drive its conclusion.
    let h6 := h3 h4
    -- Disjunctions on the left can always be decomposed.
    cases h6
    case inl h7 =>
      -- Conjunctions on the left can always be decomposed.
      let h8 := h7.left
      let h9 := h7.right
      -- Conjunctions on the left can always be decomposed.
      let h10 := h9.left
      let h11 := h9.right
      -- Conjunctions on the left can always be decomposed.
      let h12 := h11.left
      let h13 := h11.right
      -- False on the left can always be used.
      apply False.elim h13
    case inr h14 =>
      -- Conjunctions on the left can always be decomposed.
      let h15 := h14.left
      let h16 := h14.right
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- One of the premise coincides with the conclusion.
      exact h16



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_256171378644932936776034709447 : ((False ∨ True) → ((p3 → (True → (True ∨ ((False → ((True → p2) → ((p3 ∨ (True ∧ p1)) ∨ p1))) ∨ p4)))) → (((p3 ∨ False) → p1) ∨ True))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h3 =>
    -- False on the left can always be used.
    apply False.elim h3
  case inr h4 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_193119430417302629794056059611 : (((((p1 ∧ p3) ∨ p2) ∨ True) ∨ ((p4 → p3) ∨ False)) → ((p5 ∨ ((True → (p4 → (True ∨ (True ∧ p2)))) → True)) → (p1 ∨ (True ∨ p4)))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Disjunctions on the left can always be decomposed.
  cases h2
  case inl h3 =>
    -- Disjunctions on the left can always be decomposed.
    cases h1
    case inl h4 =>
      -- Disjunctions on the left can always be decomposed.
      cases h4
      case inl h5 =>
        -- Disjunctions on the left can always be decomposed.
        cases h5
        case inl h6 =>
          -- Conjunctions on the left can always be decomposed.
          let h7 := h6.left
          let h8 := h6.right
          -- Show the left disjunct based on <expert-advice>.
          apply Or.inl
          -- One of the premise coincides with the conclusion.
          exact h7
        case inr h9 =>
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- Show the left disjunct based on <expert-advice>.
          apply Or.inl
          -- True on the right can always be proven directly.
          apply True.intro
      case inr h10 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- True on the right can always be proven directly.
        apply True.intro
    case inr h11 =>
      -- Disjunctions on the left can always be decomposed.
      cases h11
      case inl h12 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- True on the right can always be proven directly.
        apply True.intro
      case inr h13 =>
        -- False on the left can always be used.
        apply False.elim h13
  case inr h14 =>
    -- Disjunctions on the left can always be decomposed.
    cases h1
    case inl h15 =>
      -- Disjunctions on the left can always be decomposed.
      cases h15
      case inl h16 =>
        -- Disjunctions on the left can always be decomposed.
        cases h16
        case inl h17 =>
          -- Conjunctions on the left can always be decomposed.
          let h18 := h17.left
          let h19 := h17.right
          -- Show the left disjunct based on <expert-advice>.
          apply Or.inl
          -- One of the premise coincides with the conclusion.
          exact h18
        case inr h20 =>
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- Show the left disjunct based on <expert-advice>.
          apply Or.inl
          -- True on the right can always be proven directly.
          apply True.intro
      case inr h21 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- True on the right can always be proven directly.
        apply True.intro
    case inr h22 =>
      -- Disjunctions on the left can always be decomposed.
      cases h22
      case inl h23 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- True on the right can always be proven directly.
        apply True.intro
      case inr h24 =>
        -- False on the left can always be used.
        apply False.elim h24



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_186555499244727871984710037195 : ((((False ∨ p2) → (((p3 → p5) ∨ p4) → p4)) ∨ (p5 ∨ p2)) → (((p3 ∨ p4) ∨ (p2 → ((p4 → True) ∨ ((p3 ∨ p4) → True)))) ∨ p1)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h2 =>
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h3
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Implications on the right can always be decomposed.
    intro h4
    -- True on the right can always be proven directly.
    apply True.intro
  case inr h5 =>
    -- Disjunctions on the left can always be decomposed.
    cases h5
    case inl h6 =>
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Implications on the right can always be decomposed.
      intro h7
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- Implications on the right can always be decomposed.
      intro h8
      -- True on the right can always be proven directly.
      apply True.intro
    case inr h9 =>
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Implications on the right can always be decomposed.
      intro h10
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- Implications on the right can always be decomposed.
      intro h11
      -- True on the right can always be proven directly.
      apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_774074781548847543061374645323 : (((False ∨ (((((p4 ∧ p2) ∨ (False → p4)) → p1) ∨ (p5 → (((((p1 ∨ (p1 ∨ p5)) → p5) ∧ p3) → False) → False))) ∨ (p3 → p3))) ∨ p2) ∧ True) := by
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
theorem thm_5_vars_684638379214336615378785250104 : ((((((p2 ∧ p1) ∧ p1) ∨ ((((p2 ∨ p5) ∨ p4) → (p4 → p2)) → (p2 ∧ (p4 → p4)))) ∨ ((((True ∨ p1) ∨ p1) ∧ p4) → True)) ∨ False) ∧ True) := by
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
theorem thm_5_vars_45299485607897052638793667050 : (((p2 ∧ (p4 ∨ ((p3 ∨ (False → (((False → (p4 → (True → ((True → p5) → (p4 → True))))) ∧ p2) ∧ p2))) ∨ (p5 ∧ p1)))) → p5) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_49201546519978149682086798747 : ((((p2 ∨ (False ∨ p4)) ∨ (p1 → (p3 → (((True → True) ∧ ((((False ∧ p1) ∨ p4) ∨ p4) ∨ False)) ∨ p5)))) ∨ (p1 → (p5 → True))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_147773799694049560517874643297 : ((((True ∨ p3) ∨ ((((True ∧ p1) ∧ False) → (p5 ∨ (p4 ∨ (p3 → p3)))) → (p3 ∨ (p2 ∧ p2)))) → p4) ∨ ((True ∨ (True ∧ p2)) ∧ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_149087347699045401154260376705 : (((p1 ∧ (p3 ∨ p2)) → (p3 ∧ (((False ∧ (p3 ∧ (p4 → p3))) ∧ ((p4 ∧ True) → p2)) ∨ (p2 ∨ p1)))) ∨ ((p4 ∧ (True → False)) → p2)) := by
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
theorem thm_5_vars_348487700809480870616267506420 : (p3 → (p3 ∧ ((p4 ∨ (((((((p4 → (p1 ∧ (p3 ∨ ((p1 ∧ p2) ∨ p3)))) ∨ p2) ∨ (p4 ∧ False)) ∨ p5) ∧ p3) ∨ p1) ∨ p2)) ∨ True))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- One of the premise coincides with the conclusion.
  exact h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_116267703612864894110100573243 : (((p3 ∧ (p1 → p4)) ∨ (p4 → ((p5 ∨ p3) ∨ (True → (p1 ∨ ((((p1 ∨ p5) ∧ p2) ∨ ((p1 → p3) ∨ p3)) ∧ p5)))))) ∨ (False → p1)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_53481449548413068970416660451 : (((p2 ∧ ((False ∨ (p1 → p2)) → ((p5 → p3) ∧ (p3 ∨ p1)))) → (p3 → ((True → p1) ∨ (True ∨ ((False ∨ p4) ∧ (p2 → True)))))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_147267075921763654173533841628 : ((((((p1 → True) ∨ ((((p1 ∨ False) ∨ ((True ∨ p1) → (p3 → True))) → p5) ∧ p2)) → p4) ∨ False) ∨ True) ∨ ((True → (p2 ∧ p2)) ∨ p2)) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_14981414096208608184431000804 : ((((p4 ∨ p4) ∧ (((p5 → ((((((False ∧ True) ∨ (p2 → p2)) ∧ p5) → p4) ∨ p4) → p1)) ∧ (p4 ∧ False)) ∨ p3)) ∨ (p1 → True)) ∧ True) := by
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



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_3045623683255981768502160478 : ((False → (True ∧ p4)) → (((((p1 ∨ p3) → p5) ∧ p4) ∨ False) ∨ ((((p4 ∨ p5) ∨ (False ∨ ((False ∨ False) → p2))) ∧ False) → p4))) := by
  -- Implications on the right can always be decomposed.
  intro h1
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
      apply False.elim h4
    case inr h7 =>
      -- False on the left can always be used.
      apply False.elim h4
  case inr h8 =>
    -- Disjunctions on the left can always be decomposed.
    cases h8
    case inl h9 =>
      -- False on the left can always be used.
      apply False.elim h9
    case inr h10 =>
      -- False on the left can always be used.
      apply False.elim h4



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_712337595027236080163357958785 : (((((p5 ∨ (True → (p4 → p4))) → p4) ∨ ((p4 ∨ (p5 → (p3 → (False ∧ False)))) ∧ (p1 ∨ (((p5 → (p2 → p2)) ∧ p4) → True)))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_56734637315221849451989833095 : ((((p4 ∨ p2) ∨ p3) ∧ ((False → (((p3 → (False ∧ (((((p2 ∨ p4) ∨ (p5 → p3)) ∨ p1) ∧ p4) ∧ p1))) → p3) ∨ p1)) → p3)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_255822646116520473987943638993 : ((True ∨ False) → ((True → p2) ∨ (((((p4 → p5) ∨ (((p4 → (((p4 ∧ True) ∨ True) ∧ p2)) → False) ∧ False)) → p3) ∨ p5) → (p3 ∨ True)))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h2 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h3
    -- Disjunctions on the left can always be decomposed.
    cases h3
    case inl h4 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- True on the right can always be proven directly.
      apply True.intro
    case inr h5 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- True on the right can always be proven directly.
      apply True.intro
  case inr h6 =>
    -- False on the left can always be used.
    apply False.elim h6



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_42605580955061891577700832780 : (((p3 ∨ (((True → ((False ∨ False) ∨ ((p3 ∨ (True ∨ p4)) ∨ p2))) ∧ ((False ∧ p1) ∧ (((p1 → p3) ∨ True) ∨ p5))) ∧ True)) ∨ True) ∨ p4) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_135267299889007153996615287878 : (((True ∨ ((p5 → (p2 ∨ p1)) → ((((((False ∧ True) → p4) ∨ False) → True) ∨ (True ∧ True)) → p2))) → (p1 ∨ p3)) ∨ (True ∨ (p1 → True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_253127733590635015578408949564 : ((True ∧ p5) → ((((((False ∨ ((p4 ∨ p4) ∧ p1)) ∨ (True ∧ p2)) ∨ (p2 ∨ p1)) ∨ ((True → p2) → p2)) → (p3 ∨ p2)) ∨ (p4 → p4))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h4
  -- One of the premise coincides with the conclusion.
  exact h4



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_68798340732686785803282362633 : ((p4 → ((p2 ∨ (p2 → (p2 ∧ (p4 ∨ p3)))) → ((p3 ∧ ((p5 ∨ (p1 ∧ False)) → (False ∧ ((p3 → (True ∧ p4)) → p3)))) ∨ p4))) ∨ p4) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
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
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_114698426705774381457380206296 : (((((p3 ∨ (p4 ∨ True)) ∧ (p1 ∧ (True → (True ∨ (p5 ∨ (p3 ∨ p3)))))) ∧ p1) → (p2 ∧ (p4 ∧ (False → (p5 ∨ p1))))) ∨ (True → True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_245729233161060906451094913669 : ((p3 ∧ p2) ∨ ((((p2 ∨ ((p1 ∧ True) → ((p3 → True) → p1))) ∧ p4) ∧ False) ∨ ((False → False) ∨ ((False ∧ p3) ∨ ((p5 ∧ p4) ∨ p5))))) := by
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
theorem thm_5_vars_737205854060383620167524896032 : ((((p4 → True) ∧ (((p2 → (p3 → True)) ∧ ((p5 ∧ (p2 ∨ (True ∨ ((p5 ∨ p3) ∨ True)))) ∧ (((p1 → p4) ∧ p1) ∨ p2))) ∨ True)) ∨ p1) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_38575530713630475282655410375 : ((((p5 → (((((p2 → p5) → p1) ∨ p3) → p4) ∨ p2)) ∨ (((((p2 ∨ p4) → p5) ∧ p4) ∨ (False ∨ (p4 ∨ False))) ∧ True)) ∧ p3) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_39571022935504627535838141279 : (((p1 ∨ ((False ∧ (False ∨ ((p4 → p2) ∨ p4))) ∨ ((False ∨ p5) → (p4 ∧ (False ∨ ((p2 → ((p1 ∧ p2) ∨ True)) ∧ True)))))) ∧ p2) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_165446577255586406247888375773 : (((((p3 → (((p5 ∨ p5) ∨ False) ∧ False)) ∧ p1) ∨ p4) ∧ ((p2 ∨ (p3 → True)) ∧ p2)) ∨ (False → (((p3 ∨ p1) ∨ (p4 → p5)) → p5))) := by
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
      -- False on the left can always be used.
      apply False.elim h1
    case inr h5 =>
      -- False on the left can always be used.
      apply False.elim h1
  case inr h6 =>
    -- False on the left can always be used.
    apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_228591475597993561691504176429 : ((p1 ∨ (p5 ∨ p5)) ∨ (((p1 ∨ ((p2 ∨ (p1 ∨ (p2 ∧ (p1 → (p2 ∧ False))))) ∧ (p1 ∨ p3))) ∧ p1) ∨ (((p5 ∧ p3) → p1) → True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_63970420200834383177644093608 : ((False ∨ (((p2 → (((True ∧ (p1 ∨ (((p5 → True) → p2) ∨ (p5 ∨ p2)))) ∧ p3) → ((p2 → False) ∨ (p3 ∧ p3)))) → False) → p4)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_51931622383880131356945794422 : (((((((False ∧ (True ∧ True)) ∧ p3) ∧ p5) → (p1 ∧ p2)) → ((p4 → p2) ∧ p2)) ∨ ((False ∧ ((False → (p1 ∧ p2)) → p2)) → True)) ∨ p3) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_356146980379166600598676268773 : (p5 → ((((((False ∨ ((p2 → True) ∧ p1)) ∨ p4) → p1) → (p2 → ((False ∨ p1) → p1))) → p2) ∨ (((p4 ∧ p2) ∨ (False → p2)) ∨ p2))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h2
  -- False on the left can always be used.
  apply False.elim h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_596823561337283884959517074304 : ((((((p2 ∨ (p4 ∧ (p1 → p1))) ∨ p1) ∨ (((p4 ∨ (((p2 ∧ p1) ∧ p3) ∧ ((p1 ∧ (p1 ∨ p5)) ∨ p3))) ∧ p5) ∧ p1)) ∧ True) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_233068351602992179174522057282 : ((p4 ∧ (p4 ∨ True)) → ((p1 → (((False ∧ ((p1 → True) ∨ p2)) ∧ p4) ∧ p2)) ∨ (((p4 ∧ (p2 → (p1 ∧ (True ∧ True)))) ∧ p5) ∨ True))) := by
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
    -- True on the right can always be proven directly.
    apply True.intro
  case inr h5 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_258729733043565105251566529321 : ((True → True) → (((p4 → False) → ((p5 → p1) → p5)) ∨ (p1 → (p1 ∨ (p2 ∨ (p3 ∧ (((p2 → (p4 ∧ p3)) → p1) ∨ (p1 ∧ p1)))))))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h2
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- One of the premise coincides with the conclusion.
  exact h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_133959723506251676844756260089 : (((p3 → (p5 ∨ ((((p4 ∧ ((True → p2) → (p5 → p3))) ∨ (((p5 → True) ∧ p3) → True)) ∧ p4) ∧ p3))) ∧ p1) ∨ ((p4 → True) ∨ p4)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_215788520402098374059292215034 : ((p1 ∨ (p5 ∧ (p1 ∧ p2))) ∨ (p5 → ((((p4 ∨ False) ∧ (((True → (p4 → p2)) ∨ (p4 ∧ (p3 ∧ True))) → p4)) → p2) → (False ∨ p5)))) := by
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
theorem thm_5_vars_991451886601893047386330378418 : (((p4 ∧ ((((p2 ∨ p5) ∨ p5) ∨ (((False ∧ p3) ∨ (((True ∨ p4) ∨ (True ∧ (p1 ∧ p5))) ∧ (p3 → p3))) ∨ (p3 → p4))) → p3)) → p3) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- We want to use the implication h3 based on <expert-advice>. So we show its premise.
  have h4 : (((p2 ∨ p5) ∨ p5) ∨ (((False ∧ p3) ∨ (((True ∨ p4) ∨ (True ∧ (p1 ∧ p5))) ∧ (p3 → p3))) ∨ (p3 → p4))) := by
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h5
    -- One of the premise coincides with the conclusion.
    exact h2
  -- We have shown the premise of h3, we can now drive its conclusion.
  let h6 := h3 h4
  -- One of the premise coincides with the conclusion.
  exact h6
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_172276240934845878906862822306 : ((((p5 ∨ p3) ∧ ((False ∧ p4) ∧ (p3 ∨ p2))) ∨ (((False ∧ True) → p1) ∨ p2)) ∨ ((((True ∧ ((p3 → False) ∨ p5)) ∧ p1) ∨ p3) → p4)) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- False on the left can always be used.
  apply False.elim h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_39271375473089411562492281350 : (((False ∧ (p1 → ((True → (((((p4 ∨ p2) ∨ False) ∨ (False ∧ p4)) ∨ p2) → ((True ∨ p5) → False))) ∧ ((p1 ∨ p1) ∨ p5)))) ∧ p3) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_188420826518900976968371665877 : (((((p3 ∧ True) ∧ p5) ∧ (True → (p5 ∧ True))) → p5) ∧ (((p2 → p5) ∧ ((p3 → ((False → (p1 ∨ (True ∨ p5))) → False)) ∨ False)) ∨ True)) := by
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
  -- One of the premise coincides with the conclusion.
  exact h5
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_792019112203099519539743528467 : (((True → (((p1 ∨ p5) → ((((((((p4 ∧ p1) → (p3 ∨ False)) ∧ p2) ∧ p2) ∨ (p2 ∨ p4)) → False) ∧ p3) → p4)) → (p3 ∧ p1))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_203540313170741228594082454823 : ((False ∨ (p5 → ((p5 → p1) ∨ p5))) ∧ ((p3 ∧ (((p3 ∧ (((p2 ∨ (p4 ∨ p1)) ∨ p4) ∨ (p2 ∧ p5))) ∧ (True ∨ p2)) → p5)) ∨ True)) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
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
theorem thm_5_vars_136463626907232090725346829230 : (((p5 → ((p4 → p1) → True)) → (p2 → (((((p4 ∨ True) ∨ ((p2 ∧ p1) → p5)) → (True → p5)) ∨ p2) ∨ p3))) ∨ ((True → p5) → p5)) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_254607456128888409392004701172 : ((p3 ∧ p1) → ((p5 ∧ p2) ∨ ((p1 ∧ p2) ∨ (((True ∨ p5) → p2) ∨ ((p5 ∧ (p5 → False)) → (False → ((True ∧ True) ∨ (True ∨ False)))))))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h4
  -- Implications on the right can always be decomposed.
  intro h5
  -- False on the left can always be used.
  apply False.elim h5



