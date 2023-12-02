variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_205218909590224007436687762096 : ((((p4 ∧ False) ∧ p1) ∨ (p4 ∨ p5)) ∨ ((p5 ∧ (p2 → ((p4 ∨ (p1 → (p1 ∨ ((True ∨ p2) ∧ p1)))) → (True ∧ p5)))) → (False ∨ True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
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
theorem thm_5_vars_137269200779502805543647401711 : ((p1 ∧ (p1 ∨ ((p4 ∨ p3) → (((((p1 → (True → ((p1 → False) ∨ p4))) → p3) ∨ (p3 → p5)) → p2) → p4)))) ∨ (False → (False ∧ True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- False on the left can always be used.
  apply False.elim h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_116487521651449664100446041288 : (((p2 ∧ p2) ∧ (((p1 → (p4 ∨ ((p3 ∧ (p4 → False)) ∧ p2))) ∨ p2) ∨ ((False ∧ (True → False)) ∨ ((p4 ∧ p1) ∧ p1)))) ∨ (True ∧ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_112774876844286858197973151164 : (((((((p5 → p5) ∨ True) → p2) → (p5 → True)) ∧ ((p3 → p3) ∨ (p5 ∨ ((((False ∧ p2) ∧ p4) → p2) ∧ p4)))) → p3) ∨ (p2 → p2)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_149196735849410022732215453854 : (((p4 → False) ∧ ((p5 ∨ p1) → (((((((True ∨ True) ∧ p1) → (False ∧ p4)) ∨ p4) ∨ True) ∧ p3) ∧ p2))) ∨ (p3 → (p3 ∨ (p1 ∨ True)))) := by
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
theorem thm_5_vars_162458829719008805247218637754 : ((((p2 → True) ∧ (p4 ∨ ((p4 ∧ (p4 ∨ ((False ∧ p5) → (p3 → p2)))) ∨ False))) ∨ True) ∧ ((((False → p5) ∨ False) ∨ p5) → (p1 ∨ True))) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
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
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- True on the right can always be proven directly.
      apply True.intro
    case inr h4 =>
      -- False on the left can always be used.
      apply False.elim h4
  case inr h5 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_59571083985697978966960396478 : (((p3 → p5) ∨ ((((True ∧ (p2 → p1)) ∧ ((((p1 → True) ∨ (p3 ∨ p4)) → (p4 ∨ p1)) → p5)) → p3) ∧ (True ∨ (p5 ∨ p5)))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_224992766340441970003852753525 : (((True ∧ p2) ∧ p5) ∨ (((p1 ∧ p4) ∧ (p2 ∧ ((p2 ∨ False) ∨ p4))) ∨ ((p2 ∧ ((p3 ∨ (p3 ∧ p1)) ∨ p4)) → (False → (p1 ∧ False))))) := by
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
  -- False on the left can always be used.
  apply False.elim h2
  -- False on the left can always be used.
  apply False.elim h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_942142248083439846246426364973 : (((((p3 ∨ (p4 ∨ p1)) ∧ p3) ∧ ((p3 → p1) ∧ ((p1 ∧ ((False → (p3 → p1)) ∨ False)) → ((p1 ∨ p4) → ((False → p1) ∧ p5))))) → p1) ∧ True) := by
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
    -- Conjunctions on the left can always be decomposed.
    let h7 := h3.left
    let h8 := h3.right
    -- We want to use the implication h7 based on <expert-advice>. So we show its premise.
    have h9 : p3 := by
      -- One of the premise coincides with the conclusion.
      exact h5
    -- We have shown the premise of h7, we can now drive its conclusion.
    let h10 := h7 h9
    -- One of the premise coincides with the conclusion.
    exact h10
  case inr h11 =>
    -- Disjunctions on the left can always be decomposed.
    cases h11
    case inl h12 =>
      -- Conjunctions on the left can always be decomposed.
      let h13 := h3.left
      let h14 := h3.right
      -- We want to use the implication h13 based on <expert-advice>. So we show its premise.
      have h15 : p3 := by
        -- One of the premise coincides with the conclusion.
        exact h5
      -- We have shown the premise of h13, we can now drive its conclusion.
      let h16 := h13 h15
      -- One of the premise coincides with the conclusion.
      exact h16
    case inr h17 =>
      -- Conjunctions on the left can always be decomposed.
      let h18 := h3.left
      let h19 := h3.right
      -- One of the premise coincides with the conclusion.
      exact h17
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_621821697587933070964007101466 : ((((p1 ∧ ((p4 → ((p5 ∨ (p1 ∨ (((p2 ∧ p2) ∨ p2) ∧ True))) ∧ (((p5 → p1) → p2) ∨ p3))) → ((p3 → True) ∧ p3))) ∨ p5) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_714047517465142203875085818894 : (((((((p1 → p3) ∨ p2) → p5) → p3) → (p5 ∧ ((p3 → (True → ((False ∨ (p3 → (p4 ∨ p1))) ∧ (p4 ∧ False)))) ∧ (True ∧ p3)))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_66207677034184179111036260055 : ((p5 ∨ (((p4 ∨ (True ∨ ((p1 → p1) ∨ (((p2 ∧ p3) ∨ p3) ∧ True)))) → p5) → ((((p4 ∧ (p5 ∨ True)) ∧ p4) ∧ p3) ∨ p5))) ∨ p3) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h2 : (p4 ∨ (True ∨ ((p1 → p1) ∨ (((p2 ∧ p3) ∨ p3) ∧ True)))) := by
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h3 := h1 h2
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h3



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_782797510064055013787849937501 : (((p3 ∨ (((p2 → True) ∨ ((False ∧ (p5 ∨ ((((p5 → p4) ∨ (False ∨ (True ∧ False))) ∨ (p5 ∨ (True → p5))) ∨ p4))) ∨ p2)) → False)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_42206736681535873574277870944 : (((True ∧ (True → (((p1 ∧ ((p1 ∨ (((p5 ∧ p4) ∨ (p2 → True)) → True)) → False)) ∨ p5) ∧ ((p4 ∨ (p4 → p3)) ∨ p5)))) ∨ p1) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_166240698062173887228663172516 : ((p2 ∧ (True → (p2 ∨ (False ∨ ((((p4 ∧ (False ∨ p4)) ∧ (p5 ∧ p4)) → p2) ∨ p4))))) ∨ ((((p5 ∧ False) ∧ p1) → p4) → (p3 → True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_184739508557099404817297256881 : (((((False ∨ p2) → p4) ∨ False) ∧ (p2 ∧ (False ∧ (True ∧ p1)))) ∨ ((((True ∨ p5) ∧ True) → False) → ((True → p5) ∨ (True → (p1 → p5))))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h2 : ((True ∨ p5) ∧ True) := by
    -- Conjunctions on the right can always be decomposed.
    apply And.intro
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- True on the right can always be proven directly.
    apply True.intro
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h3 := h1 h2
  -- False on the left can always be used.
  apply False.elim h3



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_56447739686384510999792117735 : ((((p2 ∨ False) ∨ (p2 → p4)) → ((((p4 → ((p5 → True) ∨ p4)) ∧ p1) → ((True ∨ (((False → False) ∧ p4) → True)) ∧ p3)) → p2)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_318647280698649456816768672747 : (p4 ∨ ((p5 ∨ ((((p2 → p1) → (p1 ∨ (((p1 → (((True → (p3 → False)) → p5) ∧ p5)) ∨ True) ∨ p1))) → p5) ∨ False)) ∨ (True → True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_621846388401189793097473097811 : ((((p1 ∧ ((True ∧ (((False → p2) ∧ (p3 ∨ (False ∨ p1))) → p3)) ∧ ((((False ∧ (p5 → p3)) → p5) ∧ p5) → (False ∨ False)))) ∨ True) ∨ p1) ∧ True) := by
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
theorem thm_5_vars_147062463108696593874860701551 : ((((False → ((p2 ∨ p2) ∧ (p2 ∧ (p2 ∨ True)))) ∧ (((p5 ∧ p4) ∧ p4) ∨ (p4 ∧ (p3 → p5)))) ∧ p2) ∨ (p4 ∨ ((p2 → True) ∧ True))) := by
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
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_137377707527586157372651949458 : ((p3 ∧ ((p3 ∧ (((p2 ∧ p2) ∨ ((p2 → p4) ∧ p3)) ∧ p3)) ∨ (p4 ∨ (False ∧ ((p3 ∨ (p3 ∧ p4)) ∨ p1))))) ∨ (p5 → (p1 ∨ True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_320117377067308713551240862677 : (p4 ∨ ((p4 ∧ (p4 ∨ True)) → (((p4 → (True ∧ p3)) → True) ∧ ((p5 ∨ ((False ∨ p4) ∨ (p1 ∨ (p3 → (p2 ∨ (p4 → False)))))) ∧ p4)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h2
  -- True on the right can always be proven directly.
  apply True.intro
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Conjunctions on the left can always be decomposed.
  let h3 := h1.left
  let h4 := h1.right
  -- Disjunctions on the left can always be decomposed.
  cases h4
  case inl h5 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h5
  case inr h6 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h3
  -- Conjunctions on the left can always be decomposed.
  let h7 := h1.left
  let h8 := h1.right
  -- Disjunctions on the left can always be decomposed.
  cases h8
  case inl h9 =>
    -- One of the premise coincides with the conclusion.
    exact h9
  case inr h10 =>
    -- One of the premise coincides with the conclusion.
    exact h7



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_207733992988151147769866122730 : (((p4 ∧ (p3 ∧ (p2 ∨ p5))) → p4) → (((p1 → p3) → (((p3 ∧ (p3 → (p5 ∧ (p4 ∨ p4)))) ∧ p3) ∨ (p2 → (False → p4)))) ∨ p4)) := by
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
  -- Implications on the right can always be decomposed.
  intro h4
  -- False on the left can always be used.
  apply False.elim h4



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_167711940103232244507001106624 : (((p3 ∨ ((True ∨ (p4 ∧ True)) ∨ (((p4 ∧ p3) ∨ p1) → p5))) ∧ ((p1 → p4) ∧ p1)) → (((False ∨ (p4 ∨ p4)) ∨ (p5 → False)) ∨ p3)) := by
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
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h4
  case inr h7 =>
    -- Disjunctions on the left can always be decomposed.
    cases h7
    case inl h8 =>
      -- Disjunctions on the left can always be decomposed.
      cases h8
      case inl h9 =>
        -- Conjunctions on the left can always be decomposed.
        let h10 := h3.left
        let h11 := h3.right
        -- We want to use the implication h10 based on <expert-advice>. So we show its premise.
        have h12 : p1 := by
          -- One of the premise coincides with the conclusion.
          exact h11
        -- We have shown the premise of h10, we can now drive its conclusion.
        let h13 := h10 h12
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- One of the premise coincides with the conclusion.
        exact h13
      case inr h14 =>
        -- Conjunctions on the left can always be decomposed.
        let h15 := h14.left
        let h16 := h14.right
        -- Conjunctions on the left can always be decomposed.
        let h17 := h3.left
        let h18 := h3.right
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- One of the premise coincides with the conclusion.
        exact h15
    case inr h19 =>
      -- Conjunctions on the left can always be decomposed.
      let h20 := h3.left
      let h21 := h3.right
      -- We want to use the implication h20 based on <expert-advice>. So we show its premise.
      have h22 : p1 := by
        -- One of the premise coincides with the conclusion.
        exact h21
      -- We have shown the premise of h20, we can now drive its conclusion.
      let h23 := h20 h22
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- One of the premise coincides with the conclusion.
      exact h23



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_51176774254224329337766623935 : (((((((((p3 → p4) ∨ True) ∨ p5) → (p5 ∨ p1)) ∨ (p2 ∧ p1)) → False) → (p2 ∧ p1)) ∨ ((p3 ∧ p5) ∨ (True ∨ (True ∨ p5)))) ∨ p2) := by
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
theorem thm_5_vars_234489752094258352679767487225 : ((p2 → (p4 ∨ p4)) → (p2 → ((p1 ∨ (((p1 → p2) ∧ (p2 ∧ True)) → (p4 ∨ (((p5 ∨ p1) ∧ p1) ∧ (p1 → (False ∧ True)))))) ∨ True))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_47392697165325831669488297650 : ((((p3 → p4) → (True → ((p5 → p2) ∧ ((((p2 → (p3 → p4)) ∧ True) ∧ (((True ∨ p1) → p2) ∨ p5)) ∨ p2)))) ∨ (p5 → p5)) ∨ False) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_255285630588548502941073940092 : ((p4 ∧ p5) → (p1 ∨ (((p3 ∧ ((p4 ∨ p2) ∧ p3)) → (p3 → ((((False ∨ p1) ∧ (p4 ∨ (p4 ∧ p3))) ∧ p2) ∨ p4))) ∨ (p5 ∨ p3)))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- One of the premise coincides with the conclusion.
  exact h3



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_654118507669263941827625584594 : ((((((((p3 ∧ ((p1 ∨ ((p1 ∧ False) ∧ p1)) ∧ (p1 ∧ p5))) ∧ ((True ∨ p4) → p1)) ∨ (p1 → p5)) ∧ p2) ∨ True) ∨ (p4 ∧ p5)) ∨ False) ∧ True) := by
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
theorem thm_5_vars_252494607824569911487526440697 : ((p5 → p1) ∨ (p4 ∨ ((p2 ∨ (((p3 → (p2 ∨ p4)) → (p5 → (False → True))) ∨ True)) → (p2 → (((True ∧ p5) ∨ (False ∨ True)) ∨ p4))))) := by
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
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro
  case inr h4 =>
    -- Disjunctions on the left can always be decomposed.
    cases h4
    case inl h5 =>
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- True on the right can always be proven directly.
      apply True.intro
    case inr h6 =>
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- True on the right can always be proven directly.
      apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_151827464060024703552620123630 : (((p4 ∧ (p5 ∧ (True ∨ (((p5 ∨ p1) ∧ p5) ∨ ((p4 ∧ p5) ∧ True))))) ∧ ((p4 → p4) ∨ (p3 → p5))) → (((p3 ∨ p4) ∧ True) ∨ True)) := by
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
  cases h7
  case inl h8 =>
    -- Disjunctions on the left can always be decomposed.
    cases h3
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
    -- Disjunctions on the left can always be decomposed.
    cases h11
    case inl h12 =>
      -- Conjunctions on the left can always be decomposed.
      let h13 := h12.left
      let h14 := h12.right
      -- Disjunctions on the left can always be decomposed.
      cases h13
      case inl h15 =>
        -- Disjunctions on the left can always be decomposed.
        cases h3
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
        -- Disjunctions on the left can always be decomposed.
        cases h3
        case inl h19 =>
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- True on the right can always be proven directly.
          apply True.intro
        case inr h20 =>
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- True on the right can always be proven directly.
          apply True.intro
    case inr h21 =>
      -- Conjunctions on the left can always be decomposed.
      let h22 := h21.left
      let h23 := h21.right
      -- Conjunctions on the left can always be decomposed.
      let h24 := h22.left
      let h25 := h22.right
      -- Disjunctions on the left can always be decomposed.
      cases h3
      case inl h26 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- True on the right can always be proven directly.
        apply True.intro
      case inr h27 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- True on the right can always be proven directly.
        apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_610255697290763896669417587439 : ((((((((p2 → p3) ∧ (p5 ∧ p1)) ∨ (((True ∧ p5) ∨ p1) ∧ ((False ∧ ((p1 ∧ p4) → p5)) → (p5 → p2)))) ∨ True) → p3) ∨ p2) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_626262625355915561742692797449 : ((((p3 → ((((((p2 ∧ p2) ∨ p3) ∨ p4) ∧ p5) → p4) ∨ (True → (((p4 ∧ (p2 ∨ p1)) ∧ (p5 → p3)) → (p2 → p5))))) ∨ True) ∨ p2) ∧ True) := by
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
theorem thm_5_vars_45900398757942044826304469654 : (((p4 → (((True ∨ (p2 ∨ p5)) ∨ (((True → p5) ∧ (p1 ∧ p1)) ∨ (p5 ∨ ((p3 → (p2 → p1)) ∨ (p3 ∨ p3))))) ∨ p4)) → p1) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_738174090367126752328558335991 : ((((False ∧ p2) ∨ (p1 ∧ (((((False ∨ p2) → (((p3 ∨ p1) ∨ p4) ∧ ((p5 ∧ p2) ∧ p2))) ∨ ((p3 ∧ p5) ∧ p3)) ∨ p3) ∨ p5))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_46265294235351214463368080796 : ((((p3 ∧ (p5 → ((p4 ∨ (True ∨ p3)) → (False ∧ (True ∧ (p5 → ((False → p1) ∨ (p5 ∨ p1)))))))) → (p4 → p1)) ∧ (p5 ∧ True)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_44479039900740350493219429931 : ((((True ∧ ((p3 ∨ p4) ∨ (((True ∧ False) → (p3 ∧ p4)) → p3))) → (((p4 → p3) ∨ ((p4 ∨ (False ∨ p2)) ∧ p1)) ∧ p1)) → p5) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_58235282219797275435835453755 : (((p4 ∧ p5) ∧ (p5 ∧ ((((p3 ∨ p5) ∧ True) ∧ True) ∨ ((p4 ∨ True) ∨ (((p1 ∨ p2) ∨ ((p4 ∧ True) → (p3 ∧ p3))) ∨ p5))))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_166162396778500832098972087645 : ((False ∧ (((p2 ∨ True) → (p1 → (p1 ∨ p3))) ∨ (((p3 ∧ p1) → True) ∨ (p3 ∨ p2)))) ∨ ((p2 ∨ (p3 ∧ p5)) ∨ ((p5 → False) ∨ True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_600295215184826525021116445700 : (((((p4 → p3) → (p4 ∧ (p2 ∨ (((p1 ∨ p3) ∨ ((False → (False → p4)) ∧ False)) → (False ∨ (p3 → ((p3 → p3) ∧ p3))))))) ∧ p5) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_178078647273599892712998900693 : (((((((p1 → (p3 ∨ (True → True))) ∧ True) ∨ p5) ∨ p4) → p4) → p1) ∨ (((False ∨ True) ∧ True) ∧ (p2 → (((p4 ∧ True) ∨ True) → p2)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
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
    -- One of the premise coincides with the conclusion.
    exact h1
  case inr h6 =>
    -- One of the premise coincides with the conclusion.
    exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_158659720599998748511135908153 : ((p1 ∧ (p1 ∨ (((True ∧ True) ∧ (False ∨ ((((p3 ∧ (False → False)) ∨ False) → p3) ∧ p2))) ∧ p1))) ∨ (p2 ∨ (((p3 ∨ p5) ∨ p5) ∨ True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_137314052183947090802838506006 : ((p2 ∧ ((p2 → (p4 → (p3 ∧ ((p3 ∧ True) ∧ True)))) → ((p1 ∨ ((p4 ∧ p5) → p2)) ∨ (p3 ∧ (False ∧ p4))))) ∨ (False → (False ∨ p1))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_147017409596428503706182556476 : (((((p4 → ((p2 → False) ∨ True)) → (p5 ∧ ((((False → p1) ∨ p5) ∨ p3) ∨ False))) → (p4 ∨ p3)) ∧ True) ∨ ((True ∨ True) ∨ (False ∧ p3))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_158437535641079488244997885234 : (((p1 ∨ p4) ∨ ((p2 → ((p5 → p3) → (True → (p3 ∧ p5)))) ∧ (p1 ∧ ((p3 → p5) ∨ p3)))) ∨ (((p4 ∧ True) → True) ∨ (False ∨ True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_304004839495810001618006143075 : (p1 ∨ (((False ∨ p5) → ((((((False ∨ p3) ∨ p3) → ((True ∨ (p4 ∧ False)) ∧ (False ∨ p1))) ∧ p1) ∧ p4) ∨ ((p5 → p1) → True))) ∨ p1)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
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
    -- Implications on the right can always be decomposed.
    intro h4
    -- True on the right can always be proven directly.
    apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_184051115948698211316950014049 : ((((p4 ∨ (p5 ∨ (p2 → (p4 ∨ False)))) ∧ (p1 ∨ p4)) ∨ p1) ∨ (p1 ∨ ((False ∨ (p2 → ((((p5 ∧ p4) ∧ True) ∧ p4) ∨ True))) → True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_613572850124622329304346668944 : ((((((p2 ∧ (p2 → ((p4 ∨ p5) → (((p2 → (p3 ∨ p4)) ∨ ((p1 ∧ p5) ∨ False)) → False)))) ∨ p3) ∧ (p1 ∧ (p3 ∨ p3))) ∨ True) ∨ p3) ∧ True) := by
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
theorem thm_5_vars_738532315050529107619096154072 : ((((p1 ∧ p4) ∨ (p1 ∨ ((p2 ∧ p1) ∨ ((((False → p5) ∧ (True ∨ ((p5 → (False ∨ (True → (p2 ∧ p3)))) → False))) → True) ∧ p4)))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_654834104035020609992464145554 : ((((((True ∧ (((p3 → (p4 ∧ (((p5 ∧ (p1 ∧ (p4 ∧ p1))) → p2) → p5))) → p5) ∨ p3)) → (p5 ∧ p2)) → p5) ∨ (False ∨ True)) ∨ p3) ∧ True) := by
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
theorem thm_5_vars_216340501219056805484011806223 : ((p2 → (p5 → (True → p4))) ∨ (((((p2 ∧ True) ∧ p3) ∨ ((((p3 ∧ p4) ∨ p5) ∨ True) → p5)) ∨ p5) → (p5 ∨ (p3 ∨ (p5 → p3))))) := by
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
      -- Conjunctions on the left can always be decomposed.
      let h4 := h3.left
      let h5 := h3.right
      -- Conjunctions on the left can always be decomposed.
      let h6 := h4.left
      let h7 := h4.right
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- One of the premise coincides with the conclusion.
      exact h5
    case inr h8 =>
      -- We want to use the implication h8 based on <expert-advice>. So we show its premise.
      have h9 : (((p3 ∧ p4) ∨ p5) ∨ True) := by
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- True on the right can always be proven directly.
        apply True.intro
      -- We have shown the premise of h8, we can now drive its conclusion.
      let h10 := h8 h9
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- One of the premise coincides with the conclusion.
      exact h10
  case inr h11 =>
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- One of the premise coincides with the conclusion.
    exact h11



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_119060788160624172799592530483 : ((p1 → ((((p4 ∧ (p4 ∨ p2)) ∨ (p4 ∨ True)) → ((((p2 ∧ False) ∨ p2) ∧ (p2 → p4)) ∧ (p1 ∨ (p5 → p3)))) → p4)) ∨ (p3 → True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_216060731880028575360063420877 : ((p5 ∨ (p3 ∨ (True ∧ False))) ∨ (p5 ∨ ((p2 → (((((True ∧ p3) ∧ p2) ∨ (p2 ∨ (p5 ∨ p2))) ∧ False) ∧ (p3 → (p1 ∨ p5)))) ∨ True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_112650822604078543737158769221 : ((((((p3 → (p3 → (True → (((False → p3) ∨ False) → p5)))) ∨ p3) ∨ ((p4 ∧ False) → p1)) ∧ ((p3 → p1) ∨ True)) → p5) ∨ (False → False)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_53019032614778339284814409708 : ((((p2 ∨ (p2 ∧ (p4 ∧ p1))) ∧ ((p4 → p1) ∧ (p1 ∧ p5))) ∧ (((p2 ∨ p5) ∧ (True ∨ (p4 → False))) ∨ (True ∧ (True ∨ False)))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_654237359629431970265470798075 : (((((((True ∧ p5) ∨ (p1 ∧ (((p2 ∨ p2) ∨ (p1 ∧ ((p1 → p5) → (p4 ∧ p4)))) ∨ (p3 ∨ True)))) → p3) ∨ p5) ∨ (True ∨ p1)) ∨ p2) ∧ True) := by
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
theorem thm_5_vars_63958869702016080414934199049 : ((False ∨ ((p4 → ((False → p2) ∧ ((p2 ∧ p4) ∨ (p3 ∧ ((True ∨ ((p5 ∧ p3) ∧ (p5 → p2))) ∧ (p3 → (False ∨ True))))))) ∨ True)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_115115665375215289439197013049 : ((((p4 → (((False ∨ (p1 ∧ (p4 ∨ p3))) → p3) ∧ p4)) → p5) → (((p3 ∨ p5) ∧ ((p3 → False) → p4)) → (p5 ∨ p1))) ∨ (p3 → p4)) := by
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
  cases h3
  case inl h5 =>
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
    have h6 : (p4 → (((False ∨ (p1 ∧ (p4 ∨ p3))) → p3) ∧ p4)) := by
      -- Implications on the right can always be decomposed.
      intro h7
      -- Conjunctions on the right can always be decomposed.
      apply And.intro
      -- Implications on the right can always be decomposed.
      intro h8
      -- Disjunctions on the left can always be decomposed.
      cases h8
      case inl h9 =>
        -- False on the left can always be used.
        apply False.elim h9
      case inr h10 =>
        -- Conjunctions on the left can always be decomposed.
        let h11 := h10.left
        let h12 := h10.right
        -- Disjunctions on the left can always be decomposed.
        cases h12
        case inl h13 =>
          -- One of the premise coincides with the conclusion.
          exact h5
        case inr h14 =>
          -- One of the premise coincides with the conclusion.
          exact h14
      -- One of the premise coincides with the conclusion.
      exact h7
    -- We have shown the premise of h1, we can now drive its conclusion.
    let h15 := h1 h6
    -- One of the premise coincides with the conclusion.
    exact h15
  case inr h16 =>
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- One of the premise coincides with the conclusion.
    exact h16



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_342624855460392288145677065373 : (p2 → (((True → (((p5 ∨ True) ∧ (p1 ∨ True)) ∨ True)) ∨ p4) ∧ (((p4 ∧ p1) ∧ True) ∨ (p5 → (((p3 ∧ p4) ∨ p5) ∨ (p4 ∧ True)))))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h2
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h3
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h3



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_258962572465460090987793361128 : ((True → p3) → (((((((p1 → True) ∨ p2) ∨ p3) ∧ p3) ∨ (False ∨ False)) ∧ (((False ∧ p2) → p1) → (p3 ∧ False))) → (p4 ∨ (p1 ∧ p2)))) := by
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
    let h6 := h5.left
    let h7 := h5.right
    -- Disjunctions on the left can always be decomposed.
    cases h6
    case inl h8 =>
      -- Disjunctions on the left can always be decomposed.
      cases h8
      case inl h9 =>
        -- We want to use the implication h4 based on <expert-advice>. So we show its premise.
        have h10 : ((False ∧ p2) → p1) := by
          -- Implications on the right can always be decomposed.
          intro h11
          -- Conjunctions on the left can always be decomposed.
          let h12 := h11.left
          let h13 := h11.right
          -- False on the left can always be used.
          apply False.elim h12
        -- We have shown the premise of h4, we can now drive its conclusion.
        let h14 := h4 h10
        -- We need to get the right conjuct of h14 based on <expert-advice>.
        let h15 := h14.right
        -- False on the left can always be used.
        apply False.elim h15
      case inr h16 =>
        -- We want to use the implication h4 based on <expert-advice>. So we show its premise.
        have h17 : ((False ∧ p2) → p1) := by
          -- Implications on the right can always be decomposed.
          intro h18
          -- Conjunctions on the left can always be decomposed.
          let h19 := h18.left
          let h20 := h18.right
          -- False on the left can always be used.
          apply False.elim h19
        -- We have shown the premise of h4, we can now drive its conclusion.
        let h21 := h4 h17
        -- We need to get the right conjuct of h21 based on <expert-advice>.
        let h22 := h21.right
        -- False on the left can always be used.
        apply False.elim h22
    case inr h23 =>
      -- We want to use the implication h4 based on <expert-advice>. So we show its premise.
      have h24 : ((False ∧ p2) → p1) := by
        -- Implications on the right can always be decomposed.
        intro h25
        -- Conjunctions on the left can always be decomposed.
        let h26 := h25.left
        let h27 := h25.right
        -- False on the left can always be used.
        apply False.elim h26
      -- We have shown the premise of h4, we can now drive its conclusion.
      let h28 := h4 h24
      -- We need to get the right conjuct of h28 based on <expert-advice>.
      let h29 := h28.right
      -- False on the left can always be used.
      apply False.elim h29
  case inr h30 =>
    -- Disjunctions on the left can always be decomposed.
    cases h30
    case inl h31 =>
      -- False on the left can always be used.
      apply False.elim h31
    case inr h32 =>
      -- False on the left can always be used.
      apply False.elim h32



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_121671125835336678298342309442 : (((((p1 → p1) → (((p1 ∧ p5) ∨ (True ∨ True)) → (p2 ∧ p5))) ∨ (True → ((p3 ∧ ((True → p3) ∧ False)) → p1))) → p1) → (p1 ∨ False)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h2 : (((p1 → p1) → (((p1 ∧ p5) ∨ (True ∨ True)) → (p2 ∧ p5))) ∨ (True → ((p3 ∧ ((True → p3) ∧ False)) → p1))) := by
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h3
    -- Implications on the right can always be decomposed.
    intro h4
    -- Conjunctions on the left can always be decomposed.
    let h5 := h4.left
    let h6 := h4.right
    -- Conjunctions on the left can always be decomposed.
    let h7 := h6.left
    let h8 := h6.right
    -- False on the left can always be used.
    apply False.elim h8
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h9 := h1 h2
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- One of the premise coincides with the conclusion.
  exact h9



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_136582551716720933644439335997 : (((p2 ∧ (p2 ∨ p5)) ∨ (((True → False) → (p2 ∨ (p5 ∧ True))) ∧ ((p2 ∨ ((False → (p4 ∧ p4)) ∨ False)) ∧ p4))) ∨ (p3 ∨ (p4 → True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_57555455053572334692697155954 : ((((p3 ∧ p5) ∧ p3) → ((False ∨ (False ∧ ((p1 → ((p4 ∨ p5) ∧ (((p4 ∨ p4) ∧ p2) ∨ p2))) → ((True → p2) ∨ p1)))) ∨ p5)) ∨ p3) := by
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
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h5



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_112371422601975654876589786200 : ((((((p4 ∨ ((((p3 ∨ (((p2 ∧ p5) ∧ (p2 → True)) ∧ True)) ∧ p3) → p1) ∧ p4)) → p4) ∧ (False → p1)) ∧ True) → p1) ∨ (p2 → True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_38734762358388873908252938005 : ((((p2 ∨ (((True ∧ p2) ∧ p1) → p1)) → ((((p1 → p1) → False) ∨ p5) → (p4 ∧ (((p4 ∨ (p1 ∧ p5)) → p4) ∧ p3)))) ∧ True) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_243961566371788031937411579331 : ((True ∧ p1) ∨ ((((True → p4) ∨ True) ∧ (((False ∧ p2) ∧ (p3 ∧ (p1 ∧ p4))) ∧ ((p1 ∨ (p2 ∧ p3)) ∧ False))) ∨ ((p1 → p4) → True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_353557201619722913033116543465 : (p4 → (p3 ∨ (((False ∨ p2) ∨ (((False ∨ p3) → p1) → True)) ∧ (p3 ∨ ((((False ∨ p5) ∧ p2) ∨ (((p1 ∧ p2) ∧ p4) → p1)) ∨ p5))))) := by
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
  -- True on the right can always be proven directly.
  apply True.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h3
  -- Conjunctions on the left can always be decomposed.
  let h4 := h3.left
  let h5 := h3.right
  -- Conjunctions on the left can always be decomposed.
  let h6 := h4.left
  let h7 := h4.right
  -- One of the premise coincides with the conclusion.
  exact h6



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_32663483980777449728002353335 : ((p2 ∨ ((p1 → p3) ∨ (p2 → ((((True ∧ p5) ∨ True) ∧ (p2 → (((True ∧ (p2 → False)) ∧ (p2 ∨ (p1 ∨ p2))) ∧ True))) → False)))) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
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
    -- Conjunctions on the left can always be decomposed.
    let h6 := h5.left
    let h7 := h5.right
    -- We want to use the implication h4 based on <expert-advice>. So we show its premise.
    have h8 : p2 := by
      -- One of the premise coincides with the conclusion.
      exact h1
    -- We have shown the premise of h4, we can now drive its conclusion.
    let h9 := h4 h8
    -- We need to get the left conjuct of h9 based on <expert-advice>.
    let h10 := h9.left
    -- We need to get the left conjuct of h10 based on <expert-advice>.
    let h11 := h10.left
    -- We need to get the right conjuct of h11 based on <expert-advice>.
    let h12 := h11.right
    -- We want to use the implication h12 based on <expert-advice>. So we show its premise.
    have h13 : p2 := by
      -- One of the premise coincides with the conclusion.
      exact h1
    -- We have shown the premise of h12, we can now drive its conclusion.
    let h14 := h12 h13
    -- False on the left can always be used.
    apply False.elim h14
  case inr h15 =>
    -- We want to use the implication h4 based on <expert-advice>. So we show its premise.
    have h16 : p2 := by
      -- One of the premise coincides with the conclusion.
      exact h1
    -- We have shown the premise of h4, we can now drive its conclusion.
    let h17 := h4 h16
    -- We need to get the left conjuct of h17 based on <expert-advice>.
    let h18 := h17.left
    -- We need to get the left conjuct of h18 based on <expert-advice>.
    let h19 := h18.left
    -- We need to get the right conjuct of h19 based on <expert-advice>.
    let h20 := h19.right
    -- We want to use the implication h20 based on <expert-advice>. So we show its premise.
    have h21 : p2 := by
      -- One of the premise coincides with the conclusion.
      exact h1
    -- We have shown the premise of h20, we can now drive its conclusion.
    let h22 := h20 h21
    -- False on the left can always be used.
    apply False.elim h22
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_730791194683519112773931909125 : ((((p4 ∧ (p1 → p2)) → (False ∧ (p4 → (False ∧ ((False ∧ (p1 ∨ (False ∧ False))) ∨ ((p4 → False) → ((True ∧ (p2 → False)) ∧ p2))))))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_172457743123148927703620852239 : (((p2 ∧ ((p5 ∧ False) ∧ False)) ∨ ((((False → p3) → (p5 ∨ p1)) ∨ p1) ∧ False)) ∨ (((False → p1) ∨ ((True ∧ True) → (False ∨ p3))) → True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_118699445438506428550533590205 : ((p5 ∨ ((True → ((((p2 ∨ ((p3 ∧ (((p3 → p4) ∧ True) ∧ p5)) ∨ p3)) ∨ (p2 → (True ∧ p4))) ∧ True) ∨ True)) ∨ False)) ∨ (p4 ∧ p2)) := by
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
theorem thm_5_vars_142216450701481561383275147311 : ((p1 ∧ ((p4 → False) ∧ (False → ((p3 → p1) ∨ ((p4 ∨ (p5 ∧ (p1 ∨ p2))) → (False ∨ (p3 ∨ (p1 → p5)))))))) → (p4 → (p2 ∧ p5))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Conjunctions on the left can always be decomposed.
  let h3 := h1.left
  let h4 := h1.right
  -- Conjunctions on the left can always be decomposed.
  let h5 := h4.left
  let h6 := h4.right
  -- We want to use the implication h5 based on <expert-advice>. So we show its premise.
  have h7 : p4 := by
    -- One of the premise coincides with the conclusion.
    exact h2
  -- We have shown the premise of h5, we can now drive its conclusion.
  let h8 := h5 h7
  -- False on the left can always be used.
  apply False.elim h8
  -- Conjunctions on the left can always be decomposed.
  let h9 := h1.left
  let h10 := h1.right
  -- Conjunctions on the left can always be decomposed.
  let h11 := h10.left
  let h12 := h10.right
  -- We want to use the implication h11 based on <expert-advice>. So we show its premise.
  have h13 : p4 := by
    -- One of the premise coincides with the conclusion.
    exact h2
  -- We have shown the premise of h11, we can now drive its conclusion.
  let h14 := h11 h13
  -- False on the left can always be used.
  apply False.elim h14



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_614286676272120422974340889406 : ((((((((False ∨ (p4 ∧ p2)) → (True ∧ False)) ∨ True) → (True → (p2 ∨ ((True ∨ (p3 → p1)) ∨ p3)))) → (p1 ∧ (p3 ∨ p2))) ∨ True) ∨ False) ∧ True) := by
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
theorem thm_5_vars_65935355327075060253717373510 : ((p4 ∨ (False ∨ (((p1 → (False ∨ (True ∧ False))) ∧ (((p1 → p3) ∧ (p3 ∧ (p5 ∨ False))) ∧ (p3 ∧ p4))) ∧ (False ∨ (p5 → p3))))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_767395565131129484843264301183 : (((p5 ∧ ((p4 ∧ (((p4 ∨ (p4 ∨ ((p3 ∨ p4) ∧ p5))) → ((p1 ∧ p1) ∧ ((p1 → ((False → p4) ∧ p5)) ∧ True))) → False)) ∧ p4)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_47050444667272465612822609246 : ((((p4 ∨ ((p5 ∧ (((((False ∧ p2) → (p2 → p5)) ∨ p1) → ((p4 ∨ p2) ∧ p2)) → p5)) → p4)) ∧ (False ∨ p1)) ∨ (p1 ∨ True)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_752868227788738179098652881727 : (((False ∧ ((((True ∨ p2) → (((p1 ∨ (p1 → p1)) ∨ (((p5 ∨ False) ∨ False) ∧ ((p4 ∧ p1) ∨ p2))) ∨ (p2 ∨ p4))) ∧ True) → p1)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_204435822457439988617413389458 : (((((p5 → p4) ∧ p5) ∧ p4) ∨ p4) ∨ (((((p3 ∨ p1) → (True → ((p1 → (p2 ∧ True)) → (True ∨ (p3 ∨ p1))))) → p2) → p5) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_263264613664438358052135478220 : (True ∧ (((p3 → False) ∨ ((((True → (p2 ∧ p3)) ∧ (False → p1)) ∧ ((False ∧ p2) ∧ (p3 ∨ (p1 ∧ p2)))) → (p1 ∧ p4))) → (p2 ∨ True))) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- True on the right can always be proven directly.
  apply True.intro
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
theorem thm_5_vars_878180054131589899819471509531 : (((((False ∧ p5) ∨ ((True ∧ (p3 → True)) → (((p2 ∨ (p1 → p5)) ∧ (p5 → ((p5 ∨ p1) ∨ (p5 ∨ p5)))) ∧ p5))) ∧ (p3 → p4)) → p5) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
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
    -- False on the left can always be used.
    apply False.elim h5
  case inr h7 =>
    -- We want to use the implication h7 based on <expert-advice>. So we show its premise.
    have h8 : (True ∧ (p3 → True)) := by
      -- Conjunctions on the right can always be decomposed.
      apply And.intro
      -- True on the right can always be proven directly.
      apply True.intro
      -- Implications on the right can always be decomposed.
      intro h9
      -- True on the right can always be proven directly.
      apply True.intro
    -- We have shown the premise of h7, we can now drive its conclusion.
    let h10 := h7 h8
    -- We need to get the right conjuct of h10 based on <expert-advice>.
    let h11 := h10.right
    -- One of the premise coincides with the conclusion.
    exact h11
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_192410914676886493791596189381 : ((((((p4 ∨ True) ∨ p2) ∨ (p3 ∨ p2)) ∨ p1) ∨ True) → (False ∨ ((p2 ∨ p5) → (True ∨ (True ∨ (p2 ∧ (False ∨ (p5 ∨ (p2 ∧ p3))))))))) := by
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
        -- Disjunctions on the left can always be decomposed.
        cases h4
        case inl h5 =>
          -- Disjunctions on the left can always be decomposed.
          cases h5
          case inl h6 =>
            -- Show the right disjunct based on <expert-advice>.
            apply Or.inr
            -- Implications on the right can always be decomposed.
            intro h7
            -- Disjunctions on the left can always be decomposed.
            cases h7
            case inl h8 =>
              -- Show the left disjunct based on <expert-advice>.
              apply Or.inl
              -- True on the right can always be proven directly.
              apply True.intro
            case inr h9 =>
              -- Show the left disjunct based on <expert-advice>.
              apply Or.inl
              -- True on the right can always be proven directly.
              apply True.intro
          case inr h10 =>
            -- Show the right disjunct based on <expert-advice>.
            apply Or.inr
            -- Implications on the right can always be decomposed.
            intro h11
            -- Disjunctions on the left can always be decomposed.
            cases h11
            case inl h12 =>
              -- Show the left disjunct based on <expert-advice>.
              apply Or.inl
              -- True on the right can always be proven directly.
              apply True.intro
            case inr h13 =>
              -- Show the left disjunct based on <expert-advice>.
              apply Or.inl
              -- True on the right can always be proven directly.
              apply True.intro
        case inr h14 =>
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- Implications on the right can always be decomposed.
          intro h15
          -- Disjunctions on the left can always be decomposed.
          cases h15
          case inl h16 =>
            -- Show the left disjunct based on <expert-advice>.
            apply Or.inl
            -- True on the right can always be proven directly.
            apply True.intro
          case inr h17 =>
            -- Show the left disjunct based on <expert-advice>.
            apply Or.inl
            -- True on the right can always be proven directly.
            apply True.intro
      case inr h18 =>
        -- Disjunctions on the left can always be decomposed.
        cases h18
        case inl h19 =>
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- Implications on the right can always be decomposed.
          intro h20
          -- Disjunctions on the left can always be decomposed.
          cases h20
          case inl h21 =>
            -- Show the left disjunct based on <expert-advice>.
            apply Or.inl
            -- True on the right can always be proven directly.
            apply True.intro
          case inr h22 =>
            -- Show the left disjunct based on <expert-advice>.
            apply Or.inl
            -- True on the right can always be proven directly.
            apply True.intro
        case inr h23 =>
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- Implications on the right can always be decomposed.
          intro h24
          -- Disjunctions on the left can always be decomposed.
          cases h24
          case inl h25 =>
            -- Show the left disjunct based on <expert-advice>.
            apply Or.inl
            -- True on the right can always be proven directly.
            apply True.intro
          case inr h26 =>
            -- Show the left disjunct based on <expert-advice>.
            apply Or.inl
            -- True on the right can always be proven directly.
            apply True.intro
    case inr h27 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Implications on the right can always be decomposed.
      intro h28
      -- Disjunctions on the left can always be decomposed.
      cases h28
      case inl h29 =>
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- True on the right can always be proven directly.
        apply True.intro
      case inr h30 =>
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- True on the right can always be proven directly.
        apply True.intro
  case inr h31 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h32
    -- Disjunctions on the left can always be decomposed.
    cases h32
    case inl h33 =>
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- True on the right can always be proven directly.
      apply True.intro
    case inr h34 =>
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- True on the right can always be proven directly.
      apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_797470812543850984742582193577 : (((p1 → ((p1 → (True ∧ ((((p5 ∨ p3) → p3) → ((False ∧ (((p1 → p5) ∨ p1) ∧ p5)) ∨ (p5 ∧ (False → p4)))) ∧ p3))) ∨ True)) ∨ p5) ∧ True) := by
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
theorem thm_5_vars_671178747928836982707813766420 : ((((p2 ∨ (p5 → (p4 ∨ ((((p3 ∨ (p3 ∨ (False → ((p2 → p2) ∨ True)))) ∧ p2) → (p5 ∧ p3)) ∨ True)))) ∨ ((False ∧ p4) → p1)) ∨ p3) ∧ True) := by
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
theorem thm_5_vars_343829680123254373775914352755 : (p2 → (p2 ∧ ((p2 ∨ ((False → p1) ∧ p4)) → (p4 ∨ ((p4 ∧ (p1 ∨ False)) ∨ (p1 ∨ ((((False ∨ p5) ∨ p2) ∧ (p5 ∨ True)) ∨ p1))))))) := by
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
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Conjunctions on the right can always be decomposed.
    apply And.intro
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h1
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro
  case inr h4 =>
    -- Conjunctions on the left can always be decomposed.
    let h5 := h4.left
    let h6 := h4.right
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- One of the premise coincides with the conclusion.
    exact h6



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_722163483606689286527722563388 : ((((p4 → ((p4 → False) ∧ p3)) → (((p5 → False) ∨ False) ∨ ((p1 → (p1 ∨ ((((p4 ∧ False) → p5) ∧ False) ∧ p5))) ∨ (p5 → False)))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_160010066567232170796648032906 : (((((False → (p1 ∨ p1)) → True) → ((p3 → (((p4 ∨ True) ∨ (p4 → p3)) → True)) → p5)) → False) → (p2 ∨ (p4 ∨ ((False ∧ p5) ∨ True)))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_318586502401219405421148509934 : (p4 ∨ (((((((p4 ∨ (p5 ∧ False)) ∧ False) ∧ True) ∨ ((p3 ∧ p5) ∧ p4)) ∨ ((p4 ∧ p1) ∨ True)) ∨ ((p2 ∨ p4) ∨ p5)) ∨ (True ∨ False))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_112280500986893047969835167682 : (((True → (p3 ∧ (True ∧ ((False ∧ (False ∨ (p5 ∧ (True ∨ (((p5 ∨ p2) ∧ p3) → (p5 ∧ True)))))) ∨ (p4 ∧ p5))))) ∨ p1) ∨ (True ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_44813476518723606795752571116 : ((((True ∨ (False ∧ p3)) ∧ (p5 → ((p1 ∨ ((p3 → (p1 ∨ (p4 → (p5 ∧ (p1 ∧ ((p4 ∨ p1) → p4)))))) → p1)) → p3))) → p5) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_320988117169084028515268528454 : (p4 ∨ (False ∨ (((((p3 → False) ∧ ((p4 ∧ (p4 → p3)) → ((p4 ∧ ((p4 ∨ p3) → p4)) ∨ True))) → ((p5 ∨ p3) → p5)) ∨ p5) ∨ True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_261026534760487762849930805507 : ((p4 → p2) → ((((((p3 ∧ False) → p1) → (p5 ∨ p2)) ∧ p2) → (p1 ∨ (True ∨ ((p1 → p1) ∨ (p4 → p1))))) ∨ ((p3 ∧ p5) ∨ True))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_80134130993214135674215040209 : ((((p5 ∨ ((((p4 ∨ True) ∨ p4) ∧ (((p3 → p5) ∨ p5) → (p3 ∧ (p5 → p4)))) → ((False ∨ p5) ∨ True))) ∨ p2) → (True → p1)) → p1) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h2 : ((p5 ∨ ((((p4 ∨ True) ∨ p4) ∧ (((p3 → p5) ∨ p5) → (p3 ∧ (p5 → p4)))) → ((False ∨ p5) ∨ True))) ∨ p2) := by
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h3
    -- Conjunctions on the left can always be decomposed.
    let h4 := h3.left
    let h5 := h3.right
    -- Disjunctions on the left can always be decomposed.
    cases h4
    case inl h6 =>
      -- Disjunctions on the left can always be decomposed.
      cases h6
      case inl h7 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- True on the right can always be proven directly.
        apply True.intro
      case inr h8 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- True on the right can always be proven directly.
        apply True.intro
    case inr h9 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- True on the right can always be proven directly.
      apply True.intro
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h10 := h1 h2
  -- We want to use the implication h10 based on <expert-advice>. So we show its premise.
  have h11 : True := by
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h10, we can now drive its conclusion.
  let h12 := h10 h11
  -- One of the premise coincides with the conclusion.
  exact h12



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_217388072736715797409550638905 : (((True → (True ∧ False)) ∨ True) → ((((p4 → False) → ((True → (p2 ∨ p3)) ∨ True)) ∨ False) ∨ ((((True ∧ True) → True) ∧ p3) ∨ (p4 ∨ p1)))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h2 =>
    -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
    have h3 : True := by
      -- True on the right can always be proven directly.
      apply True.intro
    -- We have shown the premise of h2, we can now drive its conclusion.
    let h4 := h2 h3
    -- We need to get the right conjuct of h4 based on <expert-advice>.
    let h5 := h4.right
    -- False on the left can always be used.
    apply False.elim h5
  case inr h6 =>
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Implications on the right can always be decomposed.
    intro h7
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_549137486965721670130903262985 : (((False ∨ (p1 ∨ (p2 ∨ ((p1 → p2) ∨ ((True → ((((p1 → False) → (p4 ∧ True)) → p5) ∧ False)) ∨ ((p3 → p3) ∧ (False → p4))))))) ∧ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
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
  -- False on the left can always be used.
  apply False.elim h2
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_265660551790577849952370206424 : (True ∧ (p2 ∨ ((p3 ∧ (p5 ∧ (p3 ∧ (False ∨ p3)))) ∨ ((False → ((((p4 ∨ p5) ∧ p5) ∨ ((True → (p5 ∧ p1)) ∨ False)) ∧ p5)) ∨ p2)))) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
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
theorem thm_5_vars_184190817281256065018012246406 : (((((((p4 ∨ p2) ∧ (p5 → p2)) ∨ False) ∨ False) ∧ p4) → p5) ∨ (((False ∨ (p1 ∨ ((p1 ∨ False) → (p5 ∨ p1)))) ∧ p4) → (p2 → True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_338187733605201366707473483201 : (p1 → (((((False ∧ p5) ∨ p2) ∧ p4) ∨ True) ∧ (((((p3 ∨ True) → p1) ∧ p3) ∧ (p1 ∨ (p2 ∨ (p4 ∧ ((p5 ∧ p3) → p4))))) ∨ True))) := by
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
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_150160736639524313203640258707 : ((p1 → ((((p3 → p4) → (p3 ∨ (p3 ∧ (p2 → False)))) ∨ p1) ∨ (((p4 ∧ (p4 ∧ p2)) ∨ False) → p5))) ∨ (p3 → ((True ∧ True) ∧ True))) := by
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
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_114195408170299101291370046700 : ((((((True → ((p3 ∨ p2) → p2)) → p2) → False) ∧ (False → (True ∨ ((True ∨ p3) ∧ (False → p5))))) → ((p2 ∧ False) ∨ False)) ∨ (p5 → True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_199387422753214300870335229581 : ((((p4 ∧ (p3 ∧ p2)) → (True → p5)) ∨ p4) → (False ∨ (((p1 → p4) ∨ (p2 ∧ ((p1 ∧ p1) ∧ p1))) ∨ ((p1 ∧ (p3 ∧ p4)) → p1)))) := by
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
    -- Conjunctions on the left can always be decomposed.
    let h4 := h3.left
    let h5 := h3.right
    -- Conjunctions on the left can always be decomposed.
    let h6 := h5.left
    let h7 := h5.right
    -- One of the premise coincides with the conclusion.
    exact h4
  case inr h8 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Implications on the right can always be decomposed.
    intro h9
    -- One of the premise coincides with the conclusion.
    exact h8



