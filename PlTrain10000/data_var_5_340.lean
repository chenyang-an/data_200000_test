variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_112219293249959633676517261229 : (((p1 ∨ (((p2 ∧ ((p4 → False) ∨ (((p4 ∧ (False ∨ (False ∨ p2))) → p2) → p4))) → ((p5 → p1) ∨ p1)) → p5)) ∨ p5) ∨ (False → False)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_696909692109486091532465324064 : ((((((True → (True ∨ p2)) ∧ ((p3 → p3) ∨ p2)) ∨ (True → p3)) ∧ ((p5 → (p4 ∨ ((False ∧ True) ∨ (p1 ∨ p1)))) → (p4 ∨ p4))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_319673841169532294750928975207 : (p4 ∨ (((p3 ∧ (p5 ∨ p2)) ∧ ((False ∧ False) ∨ p1)) → (((p4 ∨ (p4 ∧ p3)) ∧ (p1 ∧ (p5 ∧ (True ∧ ((p1 ∧ True) ∨ p3))))) ∨ p1))) := by
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
    cases h3
    case inl h7 =>
      -- Conjunctions on the left can always be decomposed.
      let h8 := h7.left
      let h9 := h7.right
      -- False on the left can always be used.
      apply False.elim h8
    case inr h10 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- One of the premise coincides with the conclusion.
      exact h10
  case inr h11 =>
    -- Disjunctions on the left can always be decomposed.
    cases h3
    case inl h12 =>
      -- Conjunctions on the left can always be decomposed.
      let h13 := h12.left
      let h14 := h12.right
      -- False on the left can always be used.
      apply False.elim h13
    case inr h15 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- One of the premise coincides with the conclusion.
      exact h15



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_118446358946440959656099380244 : ((p3 ∨ ((((False ∨ (p5 ∨ p4)) ∧ (((((p3 ∧ p2) ∧ p5) ∨ p3) ∧ p1) → (p3 ∧ p1))) ∧ ((False ∨ p3) → p1)) ∧ p4)) ∨ (p4 → True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_249166770546025609662743829779 : ((p4 ∨ p3) ∨ ((p3 → (p3 ∧ (False ∨ ((((p5 → (False ∨ p3)) ∧ (True ∧ ((((p3 ∨ False) → p5) ∧ p4) → p1))) ∧ p4) ∨ p3)))) ∧ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- One of the premise coincides with the conclusion.
  exact h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_206119166598322354795896308422 : ((p4 ∧ ((p1 → (False ∧ p2)) → False)) ∨ (((p1 ∧ False) ∧ p3) ∨ (True ∨ (False ∧ (p3 → (p2 ∧ (p4 ∧ ((True ∨ (p4 ∧ True)) → p3)))))))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_168451259452690725827527331735 : (((False → p3) → ((p2 → ((p2 → (p3 ∧ (p5 ∧ p4))) ∨ (p4 ∨ p4))) ∧ (p1 ∨ p4))) → ((False ∨ (p2 → p4)) → ((p3 ∧ p5) → p5))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Implications on the right can always be decomposed.
  intro h3
  -- Conjunctions on the left can always be decomposed.
  let h4 := h3.left
  let h5 := h3.right
  -- Disjunctions on the left can always be decomposed.
  cases h2
  case inl h6 =>
    -- False on the left can always be used.
    apply False.elim h6
  case inr h7 =>
    -- One of the premise coincides with the conclusion.
    exact h5



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_201014840114444187028975557682 : ((p3 ∨ (p1 → (((p1 ∧ p4) → p2) ∧ p1))) → ((p5 → (False ∧ p5)) ∨ ((False ∨ (((p3 ∨ p3) ∧ (p2 → (p1 ∨ p5))) ∨ p5)) → True))) := by
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
theorem thm_5_vars_320424885669159595442343196307 : (p4 ∨ ((False ∨ p1) → ((p1 → ((p4 ∨ True) ∨ p1)) ∧ ((p1 ∨ True) ∧ (((p3 ∨ p3) → (((p2 ∨ (p3 ∧ p5)) ∨ True) ∨ True)) ∨ True))))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
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
    -- One of the premise coincides with the conclusion.
    exact h4
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h5 =>
    -- False on the left can always be used.
    apply False.elim h5
  case inr h6 =>
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- One of the premise coincides with the conclusion.
    exact h6
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h7 =>
    -- False on the left can always be used.
    apply False.elim h7
  case inr h8 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_709564836277763783651964684306 : ((((False ∨ ((p2 → (p2 ∧ False)) ∨ (p2 ∧ True))) → (((((((p1 ∨ p1) → (p2 ∨ (p4 → p2))) → p4) ∧ p3) ∨ True) → p1) → p1)) ∨ p5) ∧ True) := by
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
    -- False on the left can always be used.
    apply False.elim h3
  case inr h4 =>
    -- Disjunctions on the left can always be decomposed.
    cases h4
    case inl h5 =>
      -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
      have h6 : (((((p1 ∨ p1) → (p2 ∨ (p4 → p2))) → p4) ∧ p3) ∨ True) := by
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- True on the right can always be proven directly.
        apply True.intro
      -- We have shown the premise of h2, we can now drive its conclusion.
      let h7 := h2 h6
      -- One of the premise coincides with the conclusion.
      exact h7
    case inr h8 =>
      -- Conjunctions on the left can always be decomposed.
      let h9 := h8.left
      let h10 := h8.right
      -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
      have h11 : (((((p1 ∨ p1) → (p2 ∨ (p4 → p2))) → p4) ∧ p3) ∨ True) := by
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- True on the right can always be proven directly.
        apply True.intro
      -- We have shown the premise of h2, we can now drive its conclusion.
      let h12 := h2 h11
      -- One of the premise coincides with the conclusion.
      exact h12
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_617768675587940638938920587557 : (((((p5 ∨ (((p3 ∧ False) ∨ p1) ∧ p1)) ∨ (p2 ∨ ((((p2 → p5) → ((p2 ∧ (p3 → p2)) ∨ False)) ∨ True) → (True ∨ True)))) ∨ False) ∨ p5) ∧ True) := by
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
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h2 =>
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- True on the right can always be proven directly.
    apply True.intro
  case inr h3 =>
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- True on the right can always be proven directly.
    apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_252996580080966307667964481389 : ((True ∧ p3) → (((p1 ∨ p4) ∧ (False ∨ ((p1 ∨ p3) → (((((p3 → p5) → p2) ∨ (False ∧ (p3 ∨ p2))) ∨ True) → (p3 ∧ False))))) ∨ True)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_709903549460921596005546040741 : ((((((p2 ∨ (p3 ∨ p1)) ∧ p1) ∧ p2) ∧ ((p1 → (p2 ∨ p2)) → ((((p4 → p1) ∨ (False ∨ (p5 ∧ p4))) → (p1 ∨ p4)) ∨ False))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_56833372664841997141626160872 : ((((p3 → p1) → p4) ∧ ((p4 → (p1 ∧ ((p2 → ((p1 ∧ (p2 → (p2 → True))) ∧ (p5 ∨ p1))) ∧ ((p5 → p1) ∨ True)))) ∨ False)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_818771834715153355024239672484 : ((((((p4 ∧ (True → (p3 ∨ (p2 ∧ (p2 ∧ (False → (p5 ∨ (p2 ∧ (False ∨ (p1 → (p1 → p2))))))))))) ∨ p1) → (p1 ∧ False)) ∧ p1) → p3) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
  have h4 : ((p4 ∧ (True → (p3 ∨ (p2 ∧ (p2 ∧ (False → (p5 ∨ (p2 ∧ (False ∨ (p1 → (p1 → p2))))))))))) ∨ p1) := by
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h3
  -- We have shown the premise of h2, we can now drive its conclusion.
  let h5 := h2 h4
  -- We need to get the right conjuct of h5 based on <expert-advice>.
  let h6 := h5.right
  -- False on the left can always be used.
  apply False.elim h6
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_214639435031269280304977975991 : (((p1 → p3) ∧ (p5 ∧ p1)) ∨ (((p2 ∧ (False → (p5 → p4))) ∧ ((True ∨ ((False ∧ ((p4 ∨ p4) ∧ p4)) ∧ p4)) ∧ (False ∧ False))) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_231853474682613841892534363455 : (((p5 ∧ p5) → True) → (((p3 ∧ (p1 → True)) ∨ (((False ∧ (False ∧ (p3 ∧ p1))) ∨ (p4 ∨ p3)) ∨ ((True ∧ (True ∧ True)) ∨ p1))) ∨ False)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_174804446273433007366060274328 : (((False → p3) ∧ (((((p4 → (p5 ∧ (p1 ∧ p1))) ∧ p3) ∨ p5) ∧ p2) ∧ True)) → (p1 → (False ∨ (((p3 ∨ False) → p1) ∨ (p1 ∧ p2))))) := by
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
  -- Conjunctions on the left can always be decomposed.
  let h7 := h5.left
  let h8 := h5.right
  -- Disjunctions on the left can always be decomposed.
  cases h7
  case inl h9 =>
    -- Conjunctions on the left can always be decomposed.
    let h10 := h9.left
    let h11 := h9.right
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Conjunctions on the right can always be decomposed.
    apply And.intro
    -- One of the premise coincides with the conclusion.
    exact h2
    -- One of the premise coincides with the conclusion.
    exact h8
  case inr h12 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Conjunctions on the right can always be decomposed.
    apply And.intro
    -- One of the premise coincides with the conclusion.
    exact h2
    -- One of the premise coincides with the conclusion.
    exact h8



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_340843093437767872431326419268 : (p2 → ((((((p4 ∧ p1) ∧ p4) ∧ p4) ∧ (((((True ∧ True) ∧ (p4 → True)) ∨ True) → (False ∧ True)) → p1)) ∧ (p3 ∨ (False ∧ p2))) ∨ p2)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_148003136670951198362086843169 : ((((((p5 → (p4 ∧ (p1 → (True → True)))) ∨ (True ∨ (p5 ∨ p5))) → p2) ∧ (False ∧ p4)) ∨ (p3 → p2)) ∨ ((p3 ∨ True) ∨ (False ∨ p1))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_152141095797921981680015371187 : (((((p5 ∨ p5) ∧ (False ∨ (p1 ∧ p3))) ∧ p1) ∨ ((p5 ∧ ((p3 ∨ p5) → True)) ∨ (True ∨ (p1 ∨ p3)))) → ((p4 ∧ (p4 ∨ p3)) ∨ True)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h2 =>
    -- Conjunctions on the left can always be decomposed.
    let h3 := h2.left
    let h4 := h2.right
    -- Conjunctions on the left can always be decomposed.
    let h5 := h3.left
    let h6 := h3.right
    -- Disjunctions on the left can always be decomposed.
    cases h5
    case inl h7 =>
      -- Disjunctions on the left can always be decomposed.
      cases h6
      case inl h8 =>
        -- False on the left can always be used.
        apply False.elim h8
      case inr h9 =>
        -- Conjunctions on the left can always be decomposed.
        let h10 := h9.left
        let h11 := h9.right
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- True on the right can always be proven directly.
        apply True.intro
    case inr h12 =>
      -- Disjunctions on the left can always be decomposed.
      cases h6
      case inl h13 =>
        -- False on the left can always be used.
        apply False.elim h13
      case inr h14 =>
        -- Conjunctions on the left can always be decomposed.
        let h15 := h14.left
        let h16 := h14.right
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- True on the right can always be proven directly.
        apply True.intro
  case inr h17 =>
    -- Disjunctions on the left can always be decomposed.
    cases h17
    case inl h18 =>
      -- Conjunctions on the left can always be decomposed.
      let h19 := h18.left
      let h20 := h18.right
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- True on the right can always be proven directly.
      apply True.intro
    case inr h21 =>
      -- Disjunctions on the left can always be decomposed.
      cases h21
      case inl h22 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- True on the right can always be proven directly.
        apply True.intro
      case inr h23 =>
        -- Disjunctions on the left can always be decomposed.
        cases h23
        case inl h24 =>
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- True on the right can always be proven directly.
          apply True.intro
        case inr h25 =>
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- True on the right can always be proven directly.
          apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_166162970141531213020857561241 : ((False ∧ ((p2 → (((False ∧ p4) → True) ∧ False)) → (True → ((False → p1) ∧ (p3 ∨ p2))))) ∨ ((False ∨ (((False → p2) → p5) ∧ p2)) → p2)) := by
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
    -- Conjunctions on the left can always be decomposed.
    let h4 := h3.left
    let h5 := h3.right
    -- One of the premise coincides with the conclusion.
    exact h5



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_118189109652341536703230726530 : ((False ∨ (p2 ∨ (((((p1 → ((p3 ∧ True) ∧ p4)) ∨ (((True ∧ p2) ∨ True) ∧ p5)) ∨ (p5 ∧ p1)) ∨ (p3 ∨ False)) → p3))) ∨ (True → True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_330988634807687195740955094936 : (True → (p5 → ((p2 ∨ (((p5 → True) ∧ (p1 ∨ p5)) ∨ p3)) ∧ ((((True → p1) ∧ (p2 → True)) ∨ ((False ∨ False) ∨ (p5 ∨ p3))) ∨ p2)))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h3
  -- True on the right can always be proven directly.
  apply True.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h2
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- One of the premise coincides with the conclusion.
  exact h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_354872041286612484041223900993 : (p5 → ((False ∧ ((p1 → (p1 → (p4 ∧ ((p3 → (False ∨ (((False ∨ False) ∧ p4) ∧ ((p2 ∧ False) ∨ p3)))) ∨ p3)))) ∧ (p3 → p4))) ∨ True)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_45758521016188003848512388988 : (((False → (((((False → p1) → p3) → False) ∨ p1) ∨ ((((((p5 ∨ p1) ∧ p2) ∧ p3) ∧ p5) → (p1 → p5)) ∨ (p1 → True)))) → p4) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_760040813824396558943902042161 : (((p2 ∧ (((p1 ∨ p1) ∧ p4) ∧ (p5 ∨ (True → (True → ((((p5 → (p5 → ((p5 → p4) ∧ p3))) ∧ p1) → (p4 ∧ False)) ∨ p1)))))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_345406064276673491413938709524 : (p3 → ((((False ∧ ((p4 ∨ ((True ∧ p2) ∧ (p4 ∧ ((p5 ∧ True) → (False ∧ (p3 ∧ p2)))))) ∨ True)) → ((p1 ∨ p3) ∨ p5)) → p5) ∨ p3)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_139881643338030150392287210516 : ((((p4 ∨ ((p4 ∧ (True ∧ (p5 → (p1 ∧ ((p2 ∧ False) → (p3 → (p5 → p5))))))) ∨ p3)) ∨ p1) ∧ (True → False)) → (p5 ∧ (p5 ∨ p1))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
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
      -- Disjunctions on the left can always be decomposed.
      cases h8
      case inl h9 =>
        -- Conjunctions on the left can always be decomposed.
        let h10 := h9.left
        let h11 := h9.right
        -- Conjunctions on the left can always be decomposed.
        let h12 := h11.left
        let h13 := h11.right
        -- We want to use the implication h3 based on <expert-advice>. So we show its premise.
        have h14 : True := by
          -- True on the right can always be proven directly.
          apply True.intro
        -- We have shown the premise of h3, we can now drive its conclusion.
        let h15 := h3 h14
        -- False on the left can always be used.
        apply False.elim h15
      case inr h16 =>
        -- We want to use the implication h3 based on <expert-advice>. So we show its premise.
        have h17 : True := by
          -- True on the right can always be proven directly.
          apply True.intro
        -- We have shown the premise of h3, we can now drive its conclusion.
        let h18 := h3 h17
        -- False on the left can always be used.
        apply False.elim h18
  case inr h19 =>
    -- We want to use the implication h3 based on <expert-advice>. So we show its premise.
    have h20 : True := by
      -- True on the right can always be proven directly.
      apply True.intro
    -- We have shown the premise of h3, we can now drive its conclusion.
    let h21 := h3 h20
    -- False on the left can always be used.
    apply False.elim h21
  -- Conjunctions on the left can always be decomposed.
  let h22 := h1.left
  let h23 := h1.right
  -- Disjunctions on the left can always be decomposed.
  cases h22
  case inl h24 =>
    -- Disjunctions on the left can always be decomposed.
    cases h24
    case inl h25 =>
      -- We want to use the implication h23 based on <expert-advice>. So we show its premise.
      have h26 : True := by
        -- True on the right can always be proven directly.
        apply True.intro
      -- We have shown the premise of h23, we can now drive its conclusion.
      let h27 := h23 h26
      -- False on the left can always be used.
      apply False.elim h27
    case inr h28 =>
      -- Disjunctions on the left can always be decomposed.
      cases h28
      case inl h29 =>
        -- Conjunctions on the left can always be decomposed.
        let h30 := h29.left
        let h31 := h29.right
        -- Conjunctions on the left can always be decomposed.
        let h32 := h31.left
        let h33 := h31.right
        -- We want to use the implication h23 based on <expert-advice>. So we show its premise.
        have h34 : True := by
          -- True on the right can always be proven directly.
          apply True.intro
        -- We have shown the premise of h23, we can now drive its conclusion.
        let h35 := h23 h34
        -- False on the left can always be used.
        apply False.elim h35
      case inr h36 =>
        -- We want to use the implication h23 based on <expert-advice>. So we show its premise.
        have h37 : True := by
          -- True on the right can always be proven directly.
          apply True.intro
        -- We have shown the premise of h23, we can now drive its conclusion.
        let h38 := h23 h37
        -- False on the left can always be used.
        apply False.elim h38
  case inr h39 =>
    -- We want to use the implication h23 based on <expert-advice>. So we show its premise.
    have h40 : True := by
      -- True on the right can always be proven directly.
      apply True.intro
    -- We have shown the premise of h23, we can now drive its conclusion.
    let h41 := h23 h40
    -- False on the left can always be used.
    apply False.elim h41



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_167013150142385222553861942207 : (((p3 → (((p1 → p3) ∧ (((p2 → p2) ∧ ((False → True) → p4)) ∨ p4)) ∧ False)) ∧ p3) → ((p4 ∧ (p1 ∧ p2)) ∧ (p1 ∧ (True ∨ p3)))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
  have h4 : p3 := by
    -- One of the premise coincides with the conclusion.
    exact h3
  -- We have shown the premise of h2, we can now drive its conclusion.
  let h5 := h2 h4
  -- We need to get the right conjuct of h5 based on <expert-advice>.
  let h6 := h5.right
  -- False on the left can always be used.
  apply False.elim h6
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Conjunctions on the left can always be decomposed.
  let h7 := h1.left
  let h8 := h1.right
  -- We want to use the implication h7 based on <expert-advice>. So we show its premise.
  have h9 : p3 := by
    -- One of the premise coincides with the conclusion.
    exact h8
  -- We have shown the premise of h7, we can now drive its conclusion.
  let h10 := h7 h9
  -- We need to get the right conjuct of h10 based on <expert-advice>.
  let h11 := h10.right
  -- False on the left can always be used.
  apply False.elim h11
  -- Conjunctions on the left can always be decomposed.
  let h12 := h1.left
  let h13 := h1.right
  -- We want to use the implication h12 based on <expert-advice>. So we show its premise.
  have h14 : p3 := by
    -- One of the premise coincides with the conclusion.
    exact h13
  -- We have shown the premise of h12, we can now drive its conclusion.
  let h15 := h12 h14
  -- We need to get the right conjuct of h15 based on <expert-advice>.
  let h16 := h15.right
  -- False on the left can always be used.
  apply False.elim h16
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Conjunctions on the left can always be decomposed.
  let h17 := h1.left
  let h18 := h1.right
  -- We want to use the implication h17 based on <expert-advice>. So we show its premise.
  have h19 : p3 := by
    -- One of the premise coincides with the conclusion.
    exact h18
  -- We have shown the premise of h17, we can now drive its conclusion.
  let h20 := h17 h19
  -- We need to get the right conjuct of h20 based on <expert-advice>.
  let h21 := h20.right
  -- False on the left can always be used.
  apply False.elim h21
  -- Conjunctions on the left can always be decomposed.
  let h22 := h1.left
  let h23 := h1.right
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_184232492720716938136567209666 : (((((((p3 ∧ (p5 ∧ p3)) ∧ True) ∧ True) ∧ p4) → False) → p4) ∨ (p5 ∨ ((p3 → p3) → (((p1 ∧ p4) ∨ ((p3 → p2) → p4)) → True)))) := by
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



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_732999841762397298415126391997 : ((((p2 ∧ p4) ∧ (((p5 ∧ ((p4 ∧ p5) ∧ p4)) ∧ ((True → p2) → (((True ∨ (p5 → (p5 ∧ True))) ∧ p4) ∧ p1))) ∧ (p2 ∧ p4))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_137133933609977502360604048755 : ((True ∧ (p5 ∧ (((((((p2 ∧ p4) ∨ p3) ∨ (p3 → p1)) ∨ (True ∧ (True → p5))) → p5) → p3) ∨ (False ∧ p5)))) ∨ (p1 → (True ∨ False))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_181223807717893386716866850158 : ((p3 ∧ ((((False ∨ True) ∨ (p2 ∨ (p4 → p1))) ∧ (p1 ∧ p2)) ∧ p3)) → ((((True → p1) ∧ p5) ∨ (False ∨ (p5 ∧ True))) ∨ (p4 → p1))) := by
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
  -- Disjunctions on the left can always be decomposed.
  cases h6
  case inl h8 =>
    -- Disjunctions on the left can always be decomposed.
    cases h8
    case inl h9 =>
      -- False on the left can always be used.
      apply False.elim h9
    case inr h10 =>
      -- Conjunctions on the left can always be decomposed.
      let h11 := h7.left
      let h12 := h7.right
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Implications on the right can always be decomposed.
      intro h13
      -- One of the premise coincides with the conclusion.
      exact h11
  case inr h14 =>
    -- Disjunctions on the left can always be decomposed.
    cases h14
    case inl h15 =>
      -- Conjunctions on the left can always be decomposed.
      let h16 := h7.left
      let h17 := h7.right
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Implications on the right can always be decomposed.
      intro h18
      -- One of the premise coincides with the conclusion.
      exact h16
    case inr h19 =>
      -- Conjunctions on the left can always be decomposed.
      let h20 := h7.left
      let h21 := h7.right
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Implications on the right can always be decomposed.
      intro h22
      -- One of the premise coincides with the conclusion.
      exact h20



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_249065562676641151537748351523 : ((p4 ∨ p1) ∨ (((p1 ∨ (p1 → (((p2 ∧ p2) ∨ ((p1 → (False ∧ p4)) ∨ (p4 ∧ p3))) → True))) → False) → ((p2 ∨ (p5 ∧ p5)) → p4))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Disjunctions on the left can always be decomposed.
  cases h2
  case inl h3 =>
    -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
    have h4 : (p1 ∨ (p1 → (((p2 ∧ p2) ∨ ((p1 → (False ∧ p4)) ∨ (p4 ∧ p3))) → True))) := by
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Implications on the right can always be decomposed.
      intro h5
      -- Implications on the right can always be decomposed.
      intro h6
      -- True on the right can always be proven directly.
      apply True.intro
    -- We have shown the premise of h1, we can now drive its conclusion.
    let h7 := h1 h4
    -- False on the left can always be used.
    apply False.elim h7
  case inr h8 =>
    -- Conjunctions on the left can always be decomposed.
    let h9 := h8.left
    let h10 := h8.right
    -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
    have h11 : (p1 ∨ (p1 → (((p2 ∧ p2) ∨ ((p1 → (False ∧ p4)) ∨ (p4 ∧ p3))) → True))) := by
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Implications on the right can always be decomposed.
      intro h12
      -- Implications on the right can always be decomposed.
      intro h13
      -- True on the right can always be proven directly.
      apply True.intro
    -- We have shown the premise of h1, we can now drive its conclusion.
    let h14 := h1 h11
    -- False on the left can always be used.
    apply False.elim h14



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_702791798398094860968034254019 : (((((p3 → (p1 → (p2 ∧ (True ∨ True)))) → (False ∨ p5)) ∨ ((((p5 ∧ (p1 → p5)) ∧ (((p5 ∨ p2) → True) → p3)) ∨ p1) ∨ p1)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_242986098258009648790167232376 : ((p4 → True) ∧ ((((p2 ∨ p4) → ((((p3 ∨ p4) ∧ p2) ∧ True) ∨ p5)) ∨ ((p2 → ((False ∧ (p5 → p1)) ∨ p1)) ∧ True)) ∨ (p2 ∨ True))) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
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
theorem thm_5_vars_209237583827413207140856696513 : ((p5 ∨ (((p3 → True) → True) → p3)) → ((((False ∧ True) ∨ (p1 ∨ p5)) ∨ (p1 → (((p3 ∧ (p4 → p2)) → p3) ∧ True))) ∨ (p4 ∧ p3))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h2 =>
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h2
  case inr h3 =>
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h4
    -- Conjunctions on the right can always be decomposed.
    apply And.intro
    -- Implications on the right can always be decomposed.
    intro h5
    -- Conjunctions on the left can always be decomposed.
    let h6 := h5.left
    let h7 := h5.right
    -- One of the premise coincides with the conclusion.
    exact h6
    -- True on the right can always be proven directly.
    apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_233231911643192187358020233821 : ((p5 ∧ (p5 → False)) → (((((((p1 → p3) ∨ ((p4 ∨ p1) ∨ (p2 ∧ p4))) ∧ (((True ∨ p4) ∧ p2) ∧ p4)) → p1) → p4) → p2) ∨ p2)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- We want to use the implication h3 based on <expert-advice>. So we show its premise.
  have h4 : p5 := by
    -- One of the premise coincides with the conclusion.
    exact h2
  -- We have shown the premise of h3, we can now drive its conclusion.
  let h5 := h3 h4
  -- False on the left can always be used.
  apply False.elim h5



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_737452039183447734839431725308 : ((((p4 → p5) ∧ ((p5 → ((((p2 ∧ p1) → (True ∧ ((p1 ∧ p1) → p2))) ∧ ((p3 ∨ True) ∧ p2)) ∧ p3)) → ((p5 ∨ True) ∨ p2))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_17759237984860293809498519048 : (((p2 ∨ ((p3 ∨ ((p5 ∧ p3) ∨ ((False ∧ True) ∨ ((False → ((p5 → False) ∧ p4)) ∨ p3)))) ∨ True)) ∧ ((p4 ∧ (p4 → p2)) ∨ True)) ∧ True) := by
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
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_666737710491501518241776086396 : ((((((p1 ∨ (True ∧ ((True ∧ p2) ∨ p3))) → (True ∨ False)) → (p5 → ((p5 ∧ (p4 → p5)) ∧ (p4 ∨ p2)))) ∧ ((False ∧ p4) ∨ p2)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_336264084198963247588317868248 : (p1 → ((((((p1 ∧ p3) ∨ p1) ∨ (False ∨ (p4 ∨ p5))) → (False ∧ (False ∧ False))) ∨ (((p4 ∨ False) ∧ ((p3 → False) ∧ False)) → True)) ∨ p2)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h2
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_114861803883190031795754472678 : ((((((p1 → False) ∨ (p1 → (p2 → False))) → (True ∨ True)) → (p5 ∧ p2)) ∨ ((p5 ∨ ((True ∨ (p2 ∨ p3)) ∧ p1)) ∨ p2)) ∨ (False → True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_342864483643880694467858688327 : (p2 → (((p3 ∧ p5) ∨ ((p4 → p5) ∨ p4)) ∨ ((p2 → p5) → (((p2 ∧ ((p5 ∨ p5) ∧ p4)) ∨ False) ∨ (p3 ∨ ((False ∧ p5) → False)))))) := by
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
  -- Implications on the right can always be decomposed.
  intro h3
  -- Conjunctions on the left can always be decomposed.
  let h4 := h3.left
  let h5 := h3.right
  -- False on the left can always be used.
  apply False.elim h4



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_710689945725946202132314697429 : (((((p3 ∨ (p3 ∧ p4)) ∨ (False → p1)) ∧ ((False ∧ (p1 → (p1 → ((((p1 → p2) → ((False → True) ∧ p1)) ∧ p5) ∨ False)))) ∨ True)) ∨ False) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
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
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_43832886328754131942740559789 : (((((((((p1 ∨ (p4 ∨ ((p3 ∧ (p1 ∧ p1)) ∧ p3))) ∨ (p2 → p2)) → p4) ∧ (False ∧ p4)) → p3) ∨ p4) ∧ (p2 ∨ p4)) → p5) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_387836770615129705043885344697 : (((((p2 ∧ (p2 ∨ (p1 ∨ (p2 ∨ (p4 → ((p2 → p5) → (((p5 ∧ p3) ∧ p3) ∧ (p5 → p4)))))))) → (p4 ∨ (True ∧ False))) ∨ True) ∧ True) ∧ True) := by
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
theorem thm_5_vars_175515491697779542766205347081 : ((p3 → (p2 → (True → ((((p5 ∨ p4) → (p4 → (p1 ∧ False))) ∧ p2) ∧ False)))) → ((((p1 ∨ (True → False)) ∧ p2) → False) ∨ (p1 → True))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h2
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_590946994208698985818089460009 : (((((p1 → ((p1 ∨ (((False ∨ (False → p3)) ∧ ((p3 → (((p2 ∧ p1) ∨ (True ∨ p4)) ∨ p2)) ∨ p3)) ∧ p3)) ∨ p4)) → p5) ∧ p4) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_45702611814753878939098069387 : (((True → ((((((p1 → (p4 ∨ p1)) → True) ∧ p2) ∧ ((True → (((p5 ∨ p5) ∧ p1) → p1)) ∧ p2)) → (p3 → p3)) ∨ False)) → False) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_52055565735579409297224132349 : (((p3 → (p1 → (((p1 ∨ p5) → False) ∧ (p2 → (((p4 → p1) ∨ p5) ∨ p3))))) ∨ ((p1 ∧ False) ∨ ((False ∧ (p1 ∨ p2)) ∧ p5))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_204327608653416522522052168806 : (((p3 ∧ (p4 ∨ (False ∧ False))) ∧ p5) ∨ ((p5 ∨ False) → ((((p4 ∧ ((False ∨ p5) → (False → False))) ∨ False) ∧ p3) → (False → (p3 ∧ False))))) := by
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
  -- False on the left can always be used.
  apply False.elim h3
  -- False on the left can always be used.
  apply False.elim h3



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_111891763862490775103551023229 : (((((False ∨ (p2 → ((((p3 → True) ∧ (p1 ∧ p3)) → p2) ∧ p3))) ∧ p4) ∨ ((p2 → p4) ∨ (True ∧ (p2 ∧ p4)))) ∨ False) ∨ (True ∨ p4)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_202200644431255344728888942068 : ((((p2 → True) → (True → p1)) → p1) ∧ ((((((p2 ∧ p5) ∨ p4) → ((p3 ∧ (False ∧ p2)) ∨ p3)) ∨ (p4 ∨ (p4 ∨ p4))) → False) ∨ True)) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h1
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h2 : (p2 → True) := by
    -- Implications on the right can always be decomposed.
    intro h3
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h4 := h1 h2
  -- We want to use the implication h4 based on <expert-advice>. So we show its premise.
  have h5 : True := by
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h4, we can now drive its conclusion.
  let h6 := h4 h5
  -- One of the premise coincides with the conclusion.
  exact h6
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_171500451521028046610190463928 : (((p5 → (((p5 ∧ ((True ∨ (p3 ∧ p5)) ∨ False)) ∨ p3) → (False ∨ p1))) ∧ p1) ∨ ((p2 ∧ (p2 ∨ ((p4 ∨ p1) → (p5 ∨ p5)))) → True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_112254752524885163327333439947 : (((p4 ∨ ((((p1 ∧ (p3 ∧ (p2 ∧ (p4 ∨ (True → p4))))) ∨ p2) ∧ True) ∧ ((True ∨ ((p3 ∧ p2) ∨ p5)) ∧ p4))) ∨ p3) ∨ (p4 → True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_208484222548093628488893883031 : (((True ∧ True) → ((True → p4) ∨ p4)) → ((p3 ∨ ((((p1 → p4) ∨ p4) → (p5 ∧ p3)) ∧ (False → ((p1 ∧ p2) ∧ (p2 ∨ p4))))) → p3)) := by
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
    -- Conjunctions on the left can always be decomposed.
    let h5 := h4.left
    let h6 := h4.right
    -- We want to use the implication h5 based on <expert-advice>. So we show its premise.
    have h7 : ((p1 → p4) ∨ p4) := by
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
      have h8 : (True ∧ True) := by
        -- Conjunctions on the right can always be decomposed.
        apply And.intro
        -- True on the right can always be proven directly.
        apply True.intro
        -- True on the right can always be proven directly.
        apply True.intro
      -- We have shown the premise of h1, we can now drive its conclusion.
      let h9 := h1 h8
      -- Disjunctions on the left can always be decomposed.
      cases h9
      case inl h10 =>
        -- We want to use the implication h10 based on <expert-advice>. So we show its premise.
        have h11 : True := by
          -- True on the right can always be proven directly.
          apply True.intro
        -- We have shown the premise of h10, we can now drive its conclusion.
        let h12 := h10 h11
        -- One of the premise coincides with the conclusion.
        exact h12
      case inr h13 =>
        -- One of the premise coincides with the conclusion.
        exact h13
    -- We have shown the premise of h5, we can now drive its conclusion.
    let h14 := h5 h7
    -- We need to get the right conjuct of h14 based on <expert-advice>.
    let h15 := h14.right
    -- One of the premise coincides with the conclusion.
    exact h15



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_179246055408175000368685144157 : ((p5 ∧ (((((True ∨ True) ∨ p4) ∨ p1) ∧ p5) ∨ (p2 ∨ (p2 ∨ p2)))) ∨ ((False ∨ (False → False)) ∨ ((((p1 ∨ p4) ∧ True) ∧ False) ∨ False))) := by
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
theorem thm_5_vars_302873062407998755259069198380 : (False ∨ (True → ((((((p5 ∨ True) ∧ (p5 → p4)) ∨ p2) → ((p2 → p1) → (p3 ∧ p1))) ∨ (p1 → ((p1 → p3) → p3))) ∨ (p3 → True)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h2
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_637383438025700167665213470078 : ((((((((p2 → p2) ∨ p3) ∧ ((False → p1) → p1)) ∨ False) ∧ (p2 ∧ (((p4 ∧ True) → (True ∧ True)) ∨ ((p2 → False) ∧ p5)))) → p1) ∨ p1) ∧ True) := by
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
  cases h2
  case inl h4 =>
    -- Conjunctions on the left can always be decomposed.
    let h5 := h4.left
    let h6 := h4.right
    -- Disjunctions on the left can always be decomposed.
    cases h5
    case inl h7 =>
      -- Conjunctions on the left can always be decomposed.
      let h8 := h3.left
      let h9 := h3.right
      -- Disjunctions on the left can always be decomposed.
      cases h9
      case inl h10 =>
        -- We want to use the implication h6 based on <expert-advice>. So we show its premise.
        have h11 : (False → p1) := by
          -- Implications on the right can always be decomposed.
          intro h12
          -- False on the left can always be used.
          apply False.elim h12
        -- We have shown the premise of h6, we can now drive its conclusion.
        let h13 := h6 h11
        -- One of the premise coincides with the conclusion.
        exact h13
      case inr h14 =>
        -- Conjunctions on the left can always be decomposed.
        let h15 := h14.left
        let h16 := h14.right
        -- We want to use the implication h15 based on <expert-advice>. So we show its premise.
        have h17 : p2 := by
          -- One of the premise coincides with the conclusion.
          exact h8
        -- We have shown the premise of h15, we can now drive its conclusion.
        let h18 := h15 h17
        -- False on the left can always be used.
        apply False.elim h18
    case inr h19 =>
      -- Conjunctions on the left can always be decomposed.
      let h20 := h3.left
      let h21 := h3.right
      -- Disjunctions on the left can always be decomposed.
      cases h21
      case inl h22 =>
        -- We want to use the implication h6 based on <expert-advice>. So we show its premise.
        have h23 : (False → p1) := by
          -- Implications on the right can always be decomposed.
          intro h24
          -- False on the left can always be used.
          apply False.elim h24
        -- We have shown the premise of h6, we can now drive its conclusion.
        let h25 := h6 h23
        -- One of the premise coincides with the conclusion.
        exact h25
      case inr h26 =>
        -- Conjunctions on the left can always be decomposed.
        let h27 := h26.left
        let h28 := h26.right
        -- We want to use the implication h27 based on <expert-advice>. So we show its premise.
        have h29 : p2 := by
          -- One of the premise coincides with the conclusion.
          exact h20
        -- We have shown the premise of h27, we can now drive its conclusion.
        let h30 := h27 h29
        -- False on the left can always be used.
        apply False.elim h30
  case inr h31 =>
    -- False on the left can always be used.
    apply False.elim h31
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_54898047508003624801265282978 : ((((p3 ∧ (p4 ∧ (p5 ∨ p5))) ∨ p2) ∧ (p1 → (p4 ∨ (p5 → ((p3 ∧ (p3 ∨ (p4 → ((p3 ∨ False) → (p2 ∨ p5))))) ∧ p5))))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_42816482482647460189977544422 : (((p1 → ((True → ((False ∧ (p4 ∧ (True ∨ (p1 → (False ∨ ((p1 ∧ (p5 → True)) → p2)))))) → p3)) → (p5 ∨ (p3 ∧ p3)))) ∨ p5) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_2200242021718808777720939169 : ((p5 ∧ (p2 ∧ (p5 → (p1 ∨ (p4 ∨ (p4 ∨ ((False ∨ (p5 ∧ True)) ∧ p5))))))) ∨ (False → ((p1 → (p2 ∧ False)) ∧ (True → p2)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h2
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- False on the left can always be used.
  apply False.elim h1
  -- False on the left can always be used.
  apply False.elim h1
  -- Implications on the right can always be decomposed.
  intro h3
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_693449930405301231125108001010 : ((((p5 → ((p4 ∧ (p3 ∨ p2)) ∨ ((True ∨ p5) → (p1 ∨ (False → False))))) ∧ (((False ∨ p4) ∧ p4) → ((p3 → False) → (p5 ∨ True)))) ∨ p1) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
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
  -- Implications on the right can always be decomposed.
  intro h7
  -- Implications on the right can always be decomposed.
  intro h8
  -- Conjunctions on the left can always be decomposed.
  let h9 := h7.left
  let h10 := h7.right
  -- Disjunctions on the left can always be decomposed.
  cases h9
  case inl h11 =>
    -- False on the left can always be used.
    apply False.elim h11
  case inr h12 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_52292795548421347707846954021 : ((((((False → p5) ∧ ((p1 ∨ ((p4 ∧ p3) ∧ True)) ∨ p5)) ∨ p5) ∧ p3) ∧ (p3 ∧ ((p4 ∨ p2) → (((p3 ∨ p2) ∨ p3) ∨ p1)))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_114867523274493895208155986957 : (((((True → True) ∧ ((p2 ∧ p4) ∧ p3)) ∧ (((p1 ∨ p4) ∨ True) → p3)) ∨ (True → ((False → (p3 ∧ p1)) → (p4 ∨ True)))) ∨ (p2 ∧ p4)) := by
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
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_41405880218703216992340417566 : (((((p2 ∧ (((p3 → p2) ∧ p5) → ((p2 ∧ (p4 ∧ p5)) → False))) ∨ p5) ∨ (((p2 ∨ (p3 → (True ∨ True))) ∧ p3) ∨ p1)) ∨ p2) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_233232110836699630165067077928 : ((p5 ∧ (p5 → False)) → ((((((True ∧ (((p3 → (p1 ∨ p2)) ∧ p1) → (True → True))) ∨ p1) → p3) ∨ p5) ∨ p3) ∧ (True → (p4 ∧ p1)))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h2
  -- Implications on the right can always be decomposed.
  intro h4
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Conjunctions on the left can always be decomposed.
  let h5 := h1.left
  let h6 := h1.right
  -- We want to use the implication h6 based on <expert-advice>. So we show its premise.
  have h7 : p5 := by
    -- One of the premise coincides with the conclusion.
    exact h5
  -- We have shown the premise of h6, we can now drive its conclusion.
  let h8 := h6 h7
  -- False on the left can always be used.
  apply False.elim h8
  -- Conjunctions on the left can always be decomposed.
  let h9 := h1.left
  let h10 := h1.right
  -- We want to use the implication h10 based on <expert-advice>. So we show its premise.
  have h11 : p5 := by
    -- One of the premise coincides with the conclusion.
    exact h9
  -- We have shown the premise of h10, we can now drive its conclusion.
  let h12 := h10 h11
  -- False on the left can always be used.
  apply False.elim h12



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_683958981433767996733175 : (False ∨ (p1 ∨ ((True → (((((p5 ∨ (p3 ∧ p2)) → p3) ∨ p5) → p4) ∧ (True ∨ True))) ∨ ((p5 ∧ p3) ∨ True)))) := by
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
theorem thm_5_vars_232177548754836441555218930387 : (((False → True) → p3) → (((p2 ∨ (p3 ∧ p1)) → False) ∨ (((True ∧ True) ∨ ((((True → p3) ∨ (p3 ∨ p1)) ∨ p2) → (False ∨ p4))) ∨ p2))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_246367444208912610115977101539 : ((p4 ∧ p5) ∨ (p5 → ((p1 ∨ (p3 ∧ p1)) ∨ (((True ∨ ((False → (False → False)) ∨ ((True → p4) → (p4 ∧ (False ∨ p5))))) ∨ p5) ∨ False)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_593939360353122978129160716253 : (((((((p2 ∨ ((False → p5) ∨ p4)) ∧ p2) → (False ∧ (((p2 ∧ p5) ∧ p1) → (True ∧ p4)))) ∨ (p2 ∨ (p5 ∨ (p1 ∧ p1)))) ∧ p4) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_655965467523605250476741879589 : (((((((((True ∧ ((((p5 ∨ False) ∨ p1) ∨ p3) ∨ p4)) ∧ p2) → p1) ∨ True) ∧ p5) ∨ (p1 ∧ (p2 ∧ (p2 ∨ False)))) ∨ (p4 → False)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_227039468593960981975744123186 : (((p2 ∨ p2) → p5) ∨ (((p1 ∨ (p3 → p2)) → ((p5 ∨ (p2 ∧ p2)) → ((p5 ∧ ((p3 → p3) → False)) → p5))) ∨ ((True → p3) ∧ True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Implications on the right can always be decomposed.
  intro h3
  -- Conjunctions on the left can always be decomposed.
  let h4 := h3.left
  let h5 := h3.right
  -- Disjunctions on the left can always be decomposed.
  cases h2
  case inl h6 =>
    -- Disjunctions on the left can always be decomposed.
    cases h1
    case inl h7 =>
      -- One of the premise coincides with the conclusion.
      exact h6
    case inr h8 =>
      -- One of the premise coincides with the conclusion.
      exact h6
  case inr h9 =>
    -- Conjunctions on the left can always be decomposed.
    let h10 := h9.left
    let h11 := h9.right
    -- Disjunctions on the left can always be decomposed.
    cases h1
    case inl h12 =>
      -- One of the premise coincides with the conclusion.
      exact h4
    case inr h13 =>
      -- One of the premise coincides with the conclusion.
      exact h4



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_301628576933790747437311639722 : (False ∨ ((True ∨ (False → False)) → (p2 → ((True ∨ True) → ((p5 ∨ p2) ∨ (p3 → (True ∧ (((True ∧ (True ∨ (p4 → p2))) ∨ False) ∧ p2)))))))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
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
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- One of the premise coincides with the conclusion.
      exact h2
    case inr h6 =>
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- One of the premise coincides with the conclusion.
      exact h2
  case inr h7 =>
    -- Disjunctions on the left can always be decomposed.
    cases h1
    case inl h8 =>
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- One of the premise coincides with the conclusion.
      exact h2
    case inr h9 =>
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- One of the premise coincides with the conclusion.
      exact h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_451943663581656845099717948151 : (((((p1 ∨ (False ∨ (p4 ∧ p2))) → ((p2 → True) → ((((p4 ∧ p1) ∨ p4) ∨ (p5 ∧ p2)) ∨ True))) ∨ ((True → (p3 ∨ p2)) ∧ True)) ∧ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
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
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro
  case inr h4 =>
    -- Disjunctions on the left can always be decomposed.
    cases h4
    case inl h5 =>
      -- False on the left can always be used.
      apply False.elim h5
    case inr h6 =>
      -- Conjunctions on the left can always be decomposed.
      let h7 := h6.left
      let h8 := h6.right
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- True on the right can always be proven directly.
      apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_113842626491947110672655838927 : (((p4 ∨ (((False ∨ (((((True → ((p3 ∧ p5) ∨ p2)) ∨ False) → p2) ∨ p4) ∨ (True → p5))) → p1) → p4)) → (p3 ∨ p3)) ∨ (False → p3)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_893310137676448692958450589757 : (((((False → (True ∧ ((p4 → (False ∧ p4)) ∨ False))) ∧ ((p2 ∧ True) ∨ ((p4 ∨ p5) → (True ∧ (p5 ∧ False))))) ∧ ((p5 ∨ False) ∨ p5)) → p2) ∧ True) := by
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
    -- Conjunctions on the left can always be decomposed.
    let h7 := h6.left
    let h8 := h6.right
    -- Disjunctions on the left can always be decomposed.
    cases h3
    case inl h9 =>
      -- Disjunctions on the left can always be decomposed.
      cases h9
      case inl h10 =>
        -- One of the premise coincides with the conclusion.
        exact h7
      case inr h11 =>
        -- False on the left can always be used.
        apply False.elim h11
    case inr h12 =>
      -- One of the premise coincides with the conclusion.
      exact h7
  case inr h13 =>
    -- Disjunctions on the left can always be decomposed.
    cases h3
    case inl h14 =>
      -- Disjunctions on the left can always be decomposed.
      cases h14
      case inl h15 =>
        -- We want to use the implication h13 based on <expert-advice>. So we show its premise.
        have h16 : (p4 ∨ p5) := by
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- One of the premise coincides with the conclusion.
          exact h15
        -- We have shown the premise of h13, we can now drive its conclusion.
        let h17 := h13 h16
        -- We need to get the right conjuct of h17 based on <expert-advice>.
        let h18 := h17.right
        -- We need to get the right conjuct of h18 based on <expert-advice>.
        let h19 := h18.right
        -- False on the left can always be used.
        apply False.elim h19
      case inr h20 =>
        -- False on the left can always be used.
        apply False.elim h20
    case inr h21 =>
      -- We want to use the implication h13 based on <expert-advice>. So we show its premise.
      have h22 : (p4 ∨ p5) := by
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- One of the premise coincides with the conclusion.
        exact h21
      -- We have shown the premise of h13, we can now drive its conclusion.
      let h23 := h13 h22
      -- We need to get the right conjuct of h23 based on <expert-advice>.
      let h24 := h23.right
      -- We need to get the right conjuct of h24 based on <expert-advice>.
      let h25 := h24.right
      -- False on the left can always be used.
      apply False.elim h25
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_330989524472389743061056376025 : (True → (p5 → ((True ∨ (((False → p2) ∨ p3) → (p4 → False))) → ((p2 ∧ (p5 ∨ (p2 ∨ (p2 ∨ p3)))) → ((p4 → (p1 → p5)) → p2))))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Implications on the right can always be decomposed.
  intro h3
  -- Implications on the right can always be decomposed.
  intro h4
  -- Implications on the right can always be decomposed.
  intro h5
  -- Conjunctions on the left can always be decomposed.
  let h6 := h4.left
  let h7 := h4.right
  -- Disjunctions on the left can always be decomposed.
  cases h7
  case inl h8 =>
    -- Disjunctions on the left can always be decomposed.
    cases h3
    case inl h9 =>
      -- One of the premise coincides with the conclusion.
      exact h6
    case inr h10 =>
      -- One of the premise coincides with the conclusion.
      exact h6
  case inr h11 =>
    -- Disjunctions on the left can always be decomposed.
    cases h11
    case inl h12 =>
      -- Disjunctions on the left can always be decomposed.
      cases h3
      case inl h13 =>
        -- One of the premise coincides with the conclusion.
        exact h12
      case inr h14 =>
        -- One of the premise coincides with the conclusion.
        exact h12
    case inr h15 =>
      -- Disjunctions on the left can always be decomposed.
      cases h15
      case inl h16 =>
        -- Disjunctions on the left can always be decomposed.
        cases h3
        case inl h17 =>
          -- One of the premise coincides with the conclusion.
          exact h16
        case inr h18 =>
          -- One of the premise coincides with the conclusion.
          exact h16
      case inr h19 =>
        -- Disjunctions on the left can always be decomposed.
        cases h3
        case inl h20 =>
          -- One of the premise coincides with the conclusion.
          exact h6
        case inr h21 =>
          -- One of the premise coincides with the conclusion.
          exact h6



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_46833270214684019383146424300 : ((((((True → ((p4 → (p2 ∨ (p4 ∧ (p2 ∨ (p3 ∧ p2))))) ∧ p4)) ∧ p1) → (((p5 ∧ p2) → False) ∧ p3)) ∧ p3) ∨ (p3 → True)) ∨ p5) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_115252808699167185815143588163 : (((((p3 → (True ∧ p4)) ∨ p2) → (p5 ∧ (True ∧ p5))) ∨ (True ∨ ((((p1 → p3) → p4) ∨ p1) ∧ ((p2 ∧ p5) ∨ p4)))) ∨ (p2 ∨ p5)) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_135733201050723417849551012631 : (((((p3 ∨ ((True ∧ (p4 → p3)) → p5)) → (p2 ∨ (p1 ∨ p3))) → p2) ∨ (False → (p1 → ((p2 ∧ True) ∨ p3)))) ∨ (p5 → (False ∨ True))) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_797071504494744337923877400 : ((True ∧ ((p1 ∧ (p3 → True)) ∧ (((False ∧ p4) → p4) → ((False ∧ (((False ∨ p1) ∧ p2) ∧ (p4 ∨ (p2 ∧ p3)))) ∨ p5)))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_432197295520375612654344434615 : ((((p4 ∨ (p1 → (p5 ∧ ((True ∨ p3) ∧ ((True → (((p5 ∨ p1) ∧ ((p2 ∧ p3) ∨ (True ∧ p1))) ∨ p3)) → False))))) ∨ (False → False)) ∧ True) ∧ True) := by
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
theorem thm_5_vars_67388382899771720292685993114 : ((p1 → (((p5 ∨ True) → ((((p5 ∧ p5) → ((((p5 ∧ p2) ∧ p3) → p4) → (p5 ∧ ((True ∨ p3) ∨ p2)))) ∨ p2) ∨ p5)) → False)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_63282463977460032296351499734 : ((p5 ∧ (((False ∨ (True ∨ p2)) ∨ p4) → (p4 ∧ ((p5 ∧ True) ∨ (((((p4 ∨ p5) ∧ p2) → (p4 ∧ (False → p3))) ∧ False) ∧ p1))))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_56493181547885600293192251814 : (((p1 ∧ ((True ∧ p3) ∧ p3)) → ((p1 ∨ p4) → (True ∧ ((((p5 → p1) ∨ (p5 → False)) → False) ∨ (p4 ∨ ((p5 → p2) ∨ p3)))))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_192453148146866840350219379511 : (((((p1 → (p3 ∨ True)) ∨ True) ∧ (p3 → False)) ∨ False) → (((False ∨ (False → (p3 ∧ ((p4 ∨ p3) ∨ (p3 ∧ p5))))) → p3) → (True → p2))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Implications on the right can always be decomposed.
  intro h3
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h4 =>
    -- Conjunctions on the left can always be decomposed.
    let h5 := h4.left
    let h6 := h4.right
    -- Disjunctions on the left can always be decomposed.
    cases h5
    case inl h7 =>
      -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
      have h8 : (False ∨ (False → (p3 ∧ ((p4 ∨ p3) ∨ (p3 ∧ p5))))) := by
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- Implications on the right can always be decomposed.
        intro h9
        -- Conjunctions on the right can always be decomposed.
        apply And.intro
        -- False on the left can always be used.
        apply False.elim h9
        -- False on the left can always be used.
        apply False.elim h9
      -- We have shown the premise of h2, we can now drive its conclusion.
      let h10 := h2 h8
      -- We want to use the implication h6 based on <expert-advice>. So we show its premise.
      have h11 : p3 := by
        -- One of the premise coincides with the conclusion.
        exact h10
      -- We have shown the premise of h6, we can now drive its conclusion.
      let h12 := h6 h11
      -- False on the left can always be used.
      apply False.elim h12
    case inr h13 =>
      -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
      have h14 : (False ∨ (False → (p3 ∧ ((p4 ∨ p3) ∨ (p3 ∧ p5))))) := by
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- Implications on the right can always be decomposed.
        intro h15
        -- Conjunctions on the right can always be decomposed.
        apply And.intro
        -- False on the left can always be used.
        apply False.elim h15
        -- False on the left can always be used.
        apply False.elim h15
      -- We have shown the premise of h2, we can now drive its conclusion.
      let h16 := h2 h14
      -- We want to use the implication h6 based on <expert-advice>. So we show its premise.
      have h17 : p3 := by
        -- One of the premise coincides with the conclusion.
        exact h16
      -- We have shown the premise of h6, we can now drive its conclusion.
      let h18 := h6 h17
      -- False on the left can always be used.
      apply False.elim h18
  case inr h19 =>
    -- False on the left can always be used.
    apply False.elim h19



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_117237213395129128002488529154 : ((True ∧ (p4 ∧ ((False ∧ True) ∧ ((p2 ∧ False) ∧ ((True ∧ (p3 ∨ (p2 ∨ ((p2 → ((True ∨ p3) → True)) ∨ p5)))) → p4))))) ∨ (False → p5)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_337515128163347200800229259851 : (p1 → ((((((True → (p2 ∧ (p5 ∧ (p5 ∧ (p5 ∨ p4))))) ∧ (p3 ∧ (p4 ∧ p3))) ∨ True) ∧ p5) ∧ p3) ∨ ((p1 ∨ p2) ∨ (p3 → p2)))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_649980198820427182776358868704 : ((((((p1 ∨ ((p1 ∨ ((p5 ∧ p3) ∨ p2)) ∧ (False ∧ p2))) ∨ (((p2 → p5) ∧ p5) → p2)) ∨ (p4 ∨ (p1 ∧ p1))) ∧ (p4 → p1)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_306525885413345657457798485389 : (p1 ∨ ((p2 ∧ True) → ((False → ((((((p3 → ((p4 ∧ p1) ∧ p2)) → (p3 ∨ True)) ∨ p3) ∧ False) → False) ∨ p3)) → (p3 ∨ (p4 ∨ p2))))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Conjunctions on the left can always be decomposed.
  let h3 := h1.left
  let h4 := h1.right
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h3



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_50092110482713533104731420126 : (((p2 ∧ (p4 ∧ ((p5 ∨ ((p4 ∧ (((p1 ∨ False) ∧ p4) → (False ∧ p1))) → p1)) → (p2 ∧ p5)))) ∧ (p2 ∨ ((p5 ∨ True) ∧ p4))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_692009390445095349328375659209 : (((((((((p3 → p3) ∧ (p5 → p4)) ∨ p3) ∨ (p4 ∨ p3)) ∨ p2) ∧ True) ∧ (p2 ∧ (((False → p1) ∨ ((False → p3) → p5)) → p2))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_651913851656807527672193040277 : (((((p2 → False) → (((p4 ∨ ((p3 → ((p5 → p4) → p5)) ∧ p1)) ∧ (((p3 ∧ p5) → p3) ∧ (p4 ∧ p5))) ∧ False)) ∧ (True ∧ p5)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_147363445989434613218856124899 : ((((p1 ∨ ((p1 ∧ p4) ∨ ((((p4 → p1) ∧ p3) ∨ p1) ∧ (p2 → p3)))) → ((True → p4) ∧ True)) ∨ p2) ∨ (((False ∨ True) ∨ True) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_180456471353694931648626326597 : (((True ∧ (p4 ∨ (((p4 → (p3 ∧ p2)) → p1) ∨ False))) → (p1 → p1)) → (((p5 ∧ True) ∨ (p3 → (p2 ∨ p2))) ∨ ((p1 ∨ p3) → True))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h2
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_128487195927537001352763821401 : ((p5 → ((((((p5 → p5) → p3) ∨ (p1 ∧ (p5 ∧ p3))) ∨ p3) ∨ p1) ∧ (p4 ∧ ((p5 ∧ (p3 ∨ (True ∧ p5))) → True)))) → (p4 ∨ True)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_732510337172408640164509676101 : ((((False ∧ p5) ∧ (p2 ∨ (((((p2 ∨ (p2 ∧ (True ∧ (True ∨ (p3 ∧ p5))))) ∨ p4) → (p1 ∨ False)) ∨ True) → (True ∧ (p2 ∧ p5))))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



