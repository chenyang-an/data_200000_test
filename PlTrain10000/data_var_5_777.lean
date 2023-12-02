variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_117547345290720047584437322529 : ((p2 ∧ (((False ∧ (p1 → True)) ∧ ((p4 ∨ (p5 → p1)) ∨ (((False ∧ p5) → p5) → p4))) ∨ (True ∨ (p5 ∨ (False ∨ p2))))) ∨ (p4 → True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_340863736718898366040921856184 : (p2 → (((((((((p3 ∧ p2) ∨ (p5 → (p1 → p3))) → (p2 ∧ True)) ∨ p4) → p1) ∨ p3) → p3) ∨ (((p1 ∨ True) ∨ False) → p3)) ∨ True)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_721858155481064227355545454058 : ((((p4 ∨ ((p3 → p5) ∧ p5)) → (((((((p5 ∧ p2) ∨ p2) → p3) → p2) ∨ p3) ∧ p3) → ((p1 ∨ p4) ∨ ((p2 ∧ True) → p2)))) ∨ p4) ∧ True) := by
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
  -- Disjunctions on the left can always be decomposed.
  cases h3
  case inl h5 =>
    -- Disjunctions on the left can always be decomposed.
    cases h1
    case inl h6 =>
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- One of the premise coincides with the conclusion.
      exact h6
    case inr h7 =>
      -- Conjunctions on the left can always be decomposed.
      let h8 := h7.left
      let h9 := h7.right
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Implications on the right can always be decomposed.
      intro h10
      -- Conjunctions on the left can always be decomposed.
      let h11 := h10.left
      let h12 := h10.right
      -- One of the premise coincides with the conclusion.
      exact h11
  case inr h13 =>
    -- Disjunctions on the left can always be decomposed.
    cases h1
    case inl h14 =>
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- One of the premise coincides with the conclusion.
      exact h14
    case inr h15 =>
      -- Conjunctions on the left can always be decomposed.
      let h16 := h15.left
      let h17 := h15.right
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Implications on the right can always be decomposed.
      intro h18
      -- Conjunctions on the left can always be decomposed.
      let h19 := h18.left
      let h20 := h18.right
      -- One of the premise coincides with the conclusion.
      exact h19
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_304048365282923254824356776418 : (p1 ∨ ((p5 ∧ (((p4 ∨ p2) ∧ p5) ∨ ((((p5 ∨ ((p1 → p1) ∨ (p1 ∨ ((False ∨ True) ∨ (p1 → p3))))) ∧ p4) → p1) → p3))) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_16854045419276996120895037508 : ((((False ∨ True) ∧ ((p3 ∧ p3) ∧ ((((True ∧ ((p3 ∧ p3) ∨ p5)) → (True ∧ p2)) ∧ p1) ∨ (p3 ∧ p3)))) ∨ (p2 ∨ (p2 ∨ True))) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
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
theorem thm_5_vars_328618543014725507737912589765 : (True → ((((p2 ∨ p2) ∨ p2) ∧ (((p4 ∧ p2) → p1) ∧ (p1 → (True ∧ p2)))) ∨ (True ∨ ((p1 ∨ (p3 → (p4 ∨ (False → p3)))) → p5)))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_47166074144377470699982025272 : (((((p2 ∧ p3) → (((False ∧ p3) ∧ ((p2 ∨ p1) ∨ (p3 → p4))) ∧ p2)) ∧ (p3 ∨ (False ∨ ((True → p5) → p4)))) ∨ (p2 → False)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_865077681420007692785040159645 : ((((((p5 ∨ p2) ∨ ((p5 → p2) ∧ p5)) ∨ ((p3 → (p1 → (p1 ∧ True))) ∨ (((True ∧ (True → (p4 ∨ p2))) ∧ True) ∨ p3))) → False) → p2) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h1
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h2 : (((p5 ∨ p2) ∨ ((p5 → p2) ∧ p5)) ∨ ((p3 → (p1 → (p1 ∧ True))) ∨ (((True ∧ (True → (p4 ∨ p2))) ∧ True) ∨ p3))) := by
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Implications on the right can always be decomposed.
    intro h3
    -- Implications on the right can always be decomposed.
    intro h4
    -- Conjunctions on the right can always be decomposed.
    apply And.intro
    -- One of the premise coincides with the conclusion.
    exact h4
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h5 := h1 h2
  -- False on the left can always be used.
  apply False.elim h5
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_862017817302266610172480679694 : ((((((((((p1 ∧ p1) ∨ ((p4 → p2) ∨ True)) → p4) ∨ ((False ∨ p3) ∨ True)) ∨ p3) ∧ True) ∨ ((False ∨ (p4 ∧ p2)) → p5)) → False) → p4) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h1
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h2 : (((((((p1 ∧ p1) ∨ ((p4 → p2) ∨ True)) → p4) ∨ ((False ∨ p3) ∨ True)) ∨ p3) ∧ True) ∨ ((False ∨ (p4 ∧ p2)) → p5)) := by
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
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
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h3 := h1 h2
  -- False on the left can always be used.
  apply False.elim h3
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_113076819844031356365378893787 : (((p4 ∨ ((((False ∨ ((p1 ∨ p3) ∨ p4)) ∨ ((((p5 ∨ p2) ∧ (p5 ∨ p1)) → False) ∨ False)) → (False ∨ p4)) ∧ True)) → p5) ∨ (p2 → p2)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_315016753065280863151483835977 : (p3 ∨ ((((p3 → (p3 → p5)) ∨ p2) → (p1 ∨ p3)) ∨ (p2 → (p5 → (((False → p4) → (p2 ∨ p3)) → (((p3 → True) → p5) → True)))))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Implications on the right can always be decomposed.
  intro h3
  -- Implications on the right can always be decomposed.
  intro h4
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_217422161357346397763990432666 : (((p2 → (p1 ∧ True)) ∨ p4) → ((((p1 ∧ False) → p5) → ((p1 ∨ False) ∨ (((p4 ∨ p5) → p3) → (((True ∨ p5) ∨ True) → True)))) ∨ p2)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h2 =>
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Implications on the right can always be decomposed.
    intro h3
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h4
    -- Implications on the right can always be decomposed.
    intro h5
    -- True on the right can always be proven directly.
    apply True.intro
  case inr h6 =>
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Implications on the right can always be decomposed.
    intro h7
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h8
    -- Implications on the right can always be decomposed.
    intro h9
    -- True on the right can always be proven directly.
    apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_188863880457552078886529828169 : (((p3 ∧ (p3 → (p2 → p3))) ∨ ((p1 → False) ∨ True)) ∧ (p3 ∨ (p2 → ((p1 ∨ True) ∧ ((p4 ∨ p2) ∧ ((p2 ∨ p2) → (p2 ∨ False))))))) := by
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
  -- One of the premise coincides with the conclusion.
  exact h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Disjunctions on the left can always be decomposed.
  cases h2
  case inl h3 =>
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- One of the premise coincides with the conclusion.
    exact h1
  case inr h4 =>
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- One of the premise coincides with the conclusion.
    exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_714503350541456243071508826678 : (((((p2 ∨ p1) ∧ ((p2 → False) → p1)) → ((p5 → p1) ∨ (p4 ∨ ((p4 ∨ (p2 → (((p1 → False) ∧ True) ∨ (False ∧ p4)))) ∨ p2)))) ∨ p4) ∧ True) := by
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
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h4
  case inr h5 =>
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Implications on the right can always be decomposed.
    intro h6
    -- One of the premise coincides with the conclusion.
    exact h5
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_58204309616575044312387487756 : (((p4 ∧ False) ∧ ((False ∧ (p3 ∧ (p5 → (False → ((p4 ∨ p5) → ((p4 ∨ False) ∧ (p4 ∨ (True ∨ (p2 ∧ False))))))))) ∧ (p5 ∧ p2))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_348888653262651441838319429477 : (p3 → (p2 ∨ (p3 ∧ ((((p5 → p2) → ((((p3 ∨ (((p4 ∨ True) ∧ (False → p3)) → (p2 ∧ True))) → p4) → True) → p4)) ∧ p5) ∨ True)))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- One of the premise coincides with the conclusion.
  exact h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_139914233307476613422261476631 : ((((True → ((((p2 ∨ (p1 ∨ p1)) → p1) → (p2 ∧ p4)) ∨ p4)) ∧ (((p4 ∨ p3) ∧ p5) → False)) ∧ (p2 ∧ p1)) → (p4 ∧ (p5 ∨ True))) := by
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
  let h6 := h3.left
  let h7 := h3.right
  -- We want to use the implication h4 based on <expert-advice>. So we show its premise.
  have h8 : True := by
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h4, we can now drive its conclusion.
  let h9 := h4 h8
  -- Disjunctions on the left can always be decomposed.
  cases h9
  case inl h10 =>
    -- We want to use the implication h10 based on <expert-advice>. So we show its premise.
    have h11 : ((p2 ∨ (p1 ∨ p1)) → p1) := by
      -- Implications on the right can always be decomposed.
      intro h12
      -- Disjunctions on the left can always be decomposed.
      cases h12
      case inl h13 =>
        -- One of the premise coincides with the conclusion.
        exact h7
      case inr h14 =>
        -- Disjunctions on the left can always be decomposed.
        cases h14
        case inl h15 =>
          -- One of the premise coincides with the conclusion.
          exact h15
        case inr h16 =>
          -- One of the premise coincides with the conclusion.
          exact h16
    -- We have shown the premise of h10, we can now drive its conclusion.
    let h17 := h10 h11
    -- We need to get the right conjuct of h17 based on <expert-advice>.
    let h18 := h17.right
    -- One of the premise coincides with the conclusion.
    exact h18
  case inr h19 =>
    -- One of the premise coincides with the conclusion.
    exact h19
  -- Conjunctions on the left can always be decomposed.
  let h20 := h1.left
  let h21 := h1.right
  -- Conjunctions on the left can always be decomposed.
  let h22 := h20.left
  let h23 := h20.right
  -- Conjunctions on the left can always be decomposed.
  let h24 := h21.left
  let h25 := h21.right
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_714810968755555176512293741749 : ((((p1 ∧ (p5 ∨ ((p2 → p4) → p1))) → (((False ∨ (True ∨ False)) → ((p5 ∨ (p1 → p3)) ∧ ((True → False) ∧ (False → p3)))) ∨ True)) ∨ False) ∧ True) := by
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
theorem thm_5_vars_193237599310866201771338870129 : ((((False ∧ False) → False) ∧ (p4 ∨ ((True → p2) → p2))) → (p3 → ((p4 ∧ True) ∨ (p5 → (p2 ∨ (False → (False ∧ (p3 ∨ (p3 ∨ p1))))))))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Conjunctions on the left can always be decomposed.
  let h3 := h1.left
  let h4 := h1.right
  -- Disjunctions on the left can always be decomposed.
  cases h4
  case inl h5 =>
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Conjunctions on the right can always be decomposed.
    apply And.intro
    -- One of the premise coincides with the conclusion.
    exact h5
    -- True on the right can always be proven directly.
    apply True.intro
  case inr h6 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h7
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h8
    -- Conjunctions on the right can always be decomposed.
    apply And.intro
    -- False on the left can always be used.
    apply False.elim h8
    -- False on the left can always be used.
    apply False.elim h8



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_184140572279789408223430623406 : (((p5 ∧ (((p2 ∨ (p4 → (p3 → True))) ∧ p2) ∨ p3)) ∨ p2) ∨ (True ∧ (((((p4 → (p3 ∨ p1)) → p2) ∧ p5) ∧ (p1 → p4)) ∨ True))) := by
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



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_41033888815517526461639514219 : (((((False ∧ (p5 ∧ (p3 ∧ ((p4 ∧ p4) ∧ ((True → p2) ∨ (p1 ∧ (p2 ∨ True))))))) → ((p2 ∨ p5) ∨ p3)) → (True ∧ p2)) ∨ p4) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_654771754215748170911022241408 : ((((((((p4 ∨ (p3 ∨ p4)) ∨ p2) ∧ (p5 → ((((((True → p4) → p3) → False) → p1) ∨ p4) ∨ True))) → False) → p1) ∨ (False → p1)) ∨ False) ∧ True) := by
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
theorem thm_5_vars_670141853708814420906727181609 : (((((p2 → (p2 → (True ∧ (p1 ∧ False)))) ∨ ((False ∧ p3) ∧ ((False ∧ (p1 ∨ (p1 ∧ (p1 ∧ p4)))) ∨ p2))) ∨ (p5 ∧ (True ∧ p3))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_300550473971845307316858954874 : (False ∨ ((((p3 ∧ ((False ∨ p5) ∧ True)) → ((p4 ∧ p3) → (p5 ∨ p5))) ∧ ((p1 → p2) → (p3 ∧ False))) ∨ (((False ∨ p4) → p1) ∨ True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_50256934036533037799079041565 : ((((False ∨ (p1 ∨ (p1 ∨ ((p1 → (((p1 ∧ p4) ∧ p2) ∨ p5)) ∨ ((True → False) ∨ p1))))) → p4) ∨ ((p4 ∧ True) ∨ (p3 → True))) ∨ p1) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_344390583217094556370625700515 : (p2 → (p4 ∨ (False ∨ ((p1 ∨ (((p5 ∨ False) → ((False → False) ∨ p1)) ∧ (False ∧ p3))) ∨ (False ∨ (((p4 → p3) → (p2 ∨ False)) ∨ p1)))))) := by
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
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h2
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_41154569914953456028528721605 : ((((True ∧ (((True ∧ False) ∨ (p3 ∨ ((((p2 ∧ p1) ∨ p4) ∨ ((p3 ∨ p1) ∨ p1)) ∧ True))) ∨ True)) ∨ (p5 → (p3 → True))) ∨ p3) ∨ p1) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_158401008552900128411847026130 : (((p5 → p3) ∧ ((((p4 → False) → p4) → False) → (p4 ∨ (p5 → ((p5 ∧ (p5 ∧ p2)) → False))))) ∨ (False → ((False ∧ True) ∨ (True ∧ p1)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_115938043684390919251978173030 : (((p5 ∧ (p3 → (p5 ∧ False))) ∨ ((((True → p4) → p4) ∧ p1) → ((((p1 → p1) ∧ p1) ∨ (p5 ∧ (p1 → p2))) ∧ False))) ∨ (True ∨ False)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_54003917815818184826234266814 : (((((((p2 ∧ (p3 → p1)) ∧ p5) → False) → True) → p4) → (((p3 ∧ p4) → ((False ∧ (True → p3)) ∧ (False ∧ (p3 ∧ p3)))) ∨ True)) ∨ p1) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_135318317285480529939007362527 : (((((p5 ∨ False) ∧ (((p1 ∨ p2) ∧ p2) → (p1 ∨ ((p3 → True) ∨ p5)))) → (p1 ∨ False)) ∧ ((False → p5) ∧ p4)) ∨ ((p4 → True) → True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_783163541775636372397822919206 : (((p3 ∨ (((((True ∨ (False ∨ p2)) ∧ (((p4 ∨ (p4 ∧ ((True ∨ p1) ∨ p1))) → p2) → p4)) → False) ∨ p1) ∨ ((p2 ∨ p3) ∧ False))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_184680939261179331869103024008 : (((p4 ∨ (((p1 → True) ∨ True) → p2)) ∨ (p3 ∨ (p2 ∧ p3))) ∨ ((((p3 ∧ p1) → p5) → (p5 → (True ∧ ((True ∨ p5) ∨ p5)))) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_685174023822023430291844857484 : ((((p4 ∨ (((p1 ∧ p5) ∨ True) → (p2 → (((((p4 → p4) ∧ p5) ∧ p4) → p5) → p4)))) ∨ (p3 → (((p3 ∨ p1) → p3) ∨ p4))) ∨ p4) ∧ True) := by
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
  -- Disjunctions on the left can always be decomposed.
  cases h2
  case inl h3 =>
    -- One of the premise coincides with the conclusion.
    exact h3
  case inr h4 =>
    -- One of the premise coincides with the conclusion.
    exact h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_44797259650415608901463929439 : (((((p1 → p1) ∨ p3) ∧ (True → ((p2 ∨ (((p3 ∨ True) ∧ True) ∨ p3)) ∧ (p3 ∧ (((True ∨ (p4 ∧ p5)) ∨ p3) → False))))) → p3) ∨ p2) := by
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
    -- We want to use the implication h3 based on <expert-advice>. So we show its premise.
    have h5 : True := by
      -- True on the right can always be proven directly.
      apply True.intro
    -- We have shown the premise of h3, we can now drive its conclusion.
    let h6 := h3 h5
    -- We need to get the right conjuct of h6 based on <expert-advice>.
    let h7 := h6.right
    -- We need to get the left conjuct of h7 based on <expert-advice>.
    let h8 := h7.left
    -- One of the premise coincides with the conclusion.
    exact h8
  case inr h9 =>
    -- One of the premise coincides with the conclusion.
    exact h9



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_165161030019630126844186121232 : ((((p5 ∧ (False ∧ p5)) ∨ (((p3 ∧ False) ∨ (p1 → (False ∧ p3))) ∧ p1)) ∧ (p2 ∨ True)) ∨ (((p2 ∨ p3) → True) ∨ (True ∧ (False → p4)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_351908749382658117739513779665 : (p4 → ((((p2 ∨ p3) ∧ (False ∨ True)) ∨ ((p5 ∧ p3) ∨ p2)) ∨ ((False → ((((p3 ∧ p2) ∨ p3) ∧ p4) ∨ (p4 ∨ p3))) ∨ (p5 → p1)))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h2
  -- False on the left can always be used.
  apply False.elim h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_214645355018252568336303851732 : (((p2 → False) ∧ (False ∧ False)) ∨ (p2 ∨ (p1 ∨ (p3 → ((False ∧ ((p4 ∧ False) → ((p3 ∨ p1) ∧ p5))) ∨ (p1 ∨ ((p5 ∨ True) ∨ p5))))))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
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
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_217196649954114691501043481368 : ((((p2 ∨ p5) → p1) ∨ p5) → ((((((True ∧ (False ∨ (p4 ∧ (p3 → False)))) ∧ (False ∨ p2)) → p5) → p1) ∨ p5) ∨ (False → (p4 → p2)))) := by
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
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h5



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_658716248907031157162360986820 : ((((p4 ∨ (p5 ∧ (False ∨ (((((True → (p5 ∧ ((p2 ∨ p5) ∨ (p1 → p3)))) ∨ False) → p2) → (True ∧ p4)) ∨ True)))) ∨ (True ∨ p4)) ∨ False) ∧ True) := by
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
theorem thm_5_vars_42598257535302827132920477941 : (((p2 ∨ (p2 ∨ ((((p3 → True) ∧ ((p5 ∧ p3) ∨ p2)) ∨ (p1 → (False ∨ (p4 ∨ p2)))) ∧ ((p1 ∧ p1) ∨ (p2 ∧ False))))) ∨ False) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_28172029861803234443151277379 : ((True ∧ (((p4 ∨ ((p1 ∧ ((p1 → False) ∨ (((p1 ∨ p3) ∧ p2) ∨ (((p1 → True) ∧ p1) ∧ p2)))) ∧ p2)) → (p4 ∨ p3)) ∨ True)) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
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
theorem thm_5_vars_114873535659323512955094011211 : (((((p3 ∧ p4) ∧ p2) ∧ (p3 ∧ ((False ∨ p4) → (True ∨ (p5 ∧ p2))))) ∨ ((p2 → (p5 ∨ (p1 → p2))) ∨ (p4 ∧ p5))) ∨ (p3 → p4)) := by
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
  -- Implications on the right can always be decomposed.
  intro h2
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_301611979949885412160631615393 : (False ∨ (((p4 ∨ p2) → p5) → ((((p2 ∨ (((False → (p4 ∧ p4)) → p2) ∨ p5)) ∨ True) → (p1 ∧ (p5 ∨ p2))) ∨ (p3 ∨ (p2 ∨ True))))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
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
theorem thm_5_vars_111665671786858431951028972053 : ((((p2 ∨ ((False ∨ (((p5 ∨ p3) ∨ ((True ∧ p3) ∨ (True → p3))) ∨ (p3 ∨ (p1 → p4)))) ∨ (p2 ∨ p5))) ∨ True) ∨ True) ∨ (False ∨ p2)) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_249667739736940036436515640681 : ((p5 ∨ p4) ∨ (((p2 → (p3 ∨ ((p1 ∨ (((p3 ∨ (((p5 ∧ p2) ∧ False) ∧ p2)) → p3) → p2)) → True))) → (p1 ∧ True)) → (p1 ∧ p1))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h2 : (p2 → (p3 ∨ ((p1 ∨ (((p3 ∨ (((p5 ∧ p2) ∧ False) ∧ p2)) → p3) → p2)) → True))) := by
    -- Implications on the right can always be decomposed.
    intro h3
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h4
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h5 := h1 h2
  -- We need to get the left conjuct of h5 based on <expert-advice>.
  let h6 := h5.left
  -- One of the premise coincides with the conclusion.
  exact h6
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h7 : (p2 → (p3 ∨ ((p1 ∨ (((p3 ∨ (((p5 ∧ p2) ∧ False) ∧ p2)) → p3) → p2)) → True))) := by
    -- Implications on the right can always be decomposed.
    intro h8
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h9
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h10 := h1 h7
  -- We need to get the left conjuct of h10 based on <expert-advice>.
  let h11 := h10.left
  -- One of the premise coincides with the conclusion.
  exact h11



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_176225148041426205907523642166 : ((((p1 ∧ (p5 ∨ p4)) ∨ ((p4 ∧ p3) ∨ (p2 ∨ True))) ∧ (p5 → p5)) ∧ ((((True → ((False ∧ (p5 → p2)) ∧ p3)) ∨ True) ∧ True) ∨ p1)) := by
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
  -- True on the right can always be proven directly.
  apply True.intro
  -- Implications on the right can always be decomposed.
  intro h1
  -- One of the premise coincides with the conclusion.
  exact h1
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
theorem thm_5_vars_299262058214746097938552105453 : (False ∨ (((((True → p2) → ((False → p2) ∧ (p5 ∨ False))) → (((p3 ∧ False) ∧ (p3 ∧ p2)) ∧ p4)) → ((False ∨ p3) ∨ (p1 ∨ True))) ∨ p5)) := by
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
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_40611184744663267835710837059 : (((((((p4 → ((p4 → (True ∧ p4)) ∧ False)) → (p1 ∧ p1)) → (((p3 ∨ p4) ∧ p4) ∧ (p4 ∨ (p1 ∧ p3)))) ∨ p5) → p1) ∨ p2) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_135048352661331870987650060269 : ((((((p1 → ((p2 → True) → p1)) → p4) ∨ (False ∧ (((p5 ∨ (p1 ∧ p3)) ∨ p1) ∧ p1))) ∨ p5) ∨ (p1 ∨ p5)) ∨ (True ∨ (p3 → p2))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_157973489692410266562590538536 : (((False ∨ (p2 ∨ (p5 ∧ ((p3 → p1) ∨ p3)))) ∨ ((p2 ∨ p4) ∨ (False ∨ (True ∧ (True ∨ False))))) ∨ ((p3 → p4) ∧ (p2 ∧ (p1 ∧ p4)))) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
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
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_16030648344678423861084088745 : (((False → ((((((True ∧ (p3 ∨ True)) → p3) → p1) → (False ∧ p2)) ∨ p3) → ((p3 → p5) ∨ ((True ∨ p2) ∧ False)))) → (p2 ∨ True)) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_312240730588700628600800871357 : (p2 ∨ (p1 → (((p4 → ((((p2 ∨ p2) → True) ∧ (p5 ∧ False)) ∨ p5)) → (((False ∨ p2) ∧ (p5 ∨ (p4 → False))) ∧ False)) ∨ (p3 → p1)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h2
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_761250156636766814943400034 : (((False ∧ False) ∧ (((p5 ∨ ((p2 ∧ p3) ∨ p2)) ∨ p1) ∨ (p3 → ((False ∧ (False ∨ True)) ∧ ((p4 → (p1 → p2)) → p2))))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_38685591889812112294125179516 : ((((p5 ∨ ((p2 ∧ (p2 ∧ p2)) → p2)) ∧ ((p5 → p3) ∧ (((p2 → p5) → p4) → (((p4 ∧ p5) ∨ p2) ∨ (True ∧ p3))))) ∧ p5) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_729923147899599616022043206118 : (((((p3 ∧ p3) → False) → (p2 ∧ (p5 ∧ (((p1 ∨ p1) ∨ ((((False ∨ False) ∧ ((p3 ∧ p1) ∧ False)) ∨ (p4 ∨ p5)) ∧ p2)) → p4)))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_800197633413657486389001001151 : (((p2 → (((((p2 → ((((p4 → p2) ∧ (p2 ∨ (p3 ∨ p1))) → False) ∧ p2)) ∧ p2) ∨ (p2 → (True ∧ (p1 → p5)))) ∧ True) ∨ True)) ∨ p2) ∧ True) := by
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
theorem thm_5_vars_245057784909412413122293691598 : ((p1 ∧ p5) ∨ ((p3 ∨ (p5 ∨ (p5 ∧ ((True ∧ (p1 ∧ True)) ∨ ((p4 → (True ∨ (p5 → p1))) → p4))))) → (((p4 ∨ True) ∧ True) ∨ p1))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h2 =>
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
  case inr h3 =>
    -- Disjunctions on the left can always be decomposed.
    cases h3
    case inl h4 =>
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
    case inr h5 =>
      -- Conjunctions on the left can always be decomposed.
      let h6 := h5.left
      let h7 := h5.right
      -- Disjunctions on the left can always be decomposed.
      cases h7
      case inl h8 =>
        -- Conjunctions on the left can always be decomposed.
        let h9 := h8.left
        let h10 := h8.right
        -- Conjunctions on the left can always be decomposed.
        let h11 := h10.left
        let h12 := h10.right
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- One of the premise coincides with the conclusion.
        exact h11
      case inr h13 =>
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
theorem thm_5_vars_165676052203513368704311276245 : ((((p4 → ((p4 ∧ p5) → p4)) ∧ p1) → (p4 ∧ (p3 ∧ (p5 ∧ ((True → p1) ∨ p3))))) ∨ (((p5 ∧ (True ∨ p3)) → p5) ∨ (p4 ∨ p1))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
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
    -- One of the premise coincides with the conclusion.
    exact h2
  case inr h5 =>
    -- One of the premise coincides with the conclusion.
    exact h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_336257945968200408418101652068 : (p1 → (((((False ∧ True) → p5) ∧ ((p2 → (False ∧ (p1 ∨ p4))) → (p1 ∧ (True ∨ p3)))) → ((((False ∧ p4) ∧ p2) → True) ∧ p4)) ∨ True)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_191006477718002311940634575071 : (((p4 ∧ ((p4 ∨ p1) ∨ p5)) ∨ (p3 ∨ (p5 → p5))) ∨ ((p4 ∨ ((p3 ∧ ((p3 → True) → p4)) → (p4 ∧ ((p3 ∧ p2) ∨ p1)))) ∨ p2)) := by
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



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_188091240755638526768536054892 : ((((((p3 ∧ (p3 → True)) ∨ p5) ∧ p1) ∧ p1) ∨ True) ∧ (p3 ∨ ((p2 ∧ (True ∧ (p3 ∧ False))) → (False ∨ (False ∨ (p4 ∧ (p4 ∧ p1))))))) := by
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
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- Conjunctions on the left can always be decomposed.
  let h4 := h3.left
  let h5 := h3.right
  -- Conjunctions on the left can always be decomposed.
  let h6 := h5.left
  let h7 := h5.right
  -- False on the left can always be used.
  apply False.elim h7



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_708786176366975333850242179216 : (((((p1 ∨ (((p3 ∨ p3) ∧ p4) → False)) → p5) → (((True ∧ p3) → (p2 → (False ∧ (p2 ∨ (p2 → ((True → p5) ∧ p2)))))) → False)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_68424641417052830891886677268 : ((p3 → ((True → p4) ∨ ((((((True ∨ p5) ∨ (False → False)) ∨ p2) → (p4 ∨ p5)) ∧ (p5 ∨ ((True → p2) ∧ (p2 ∧ p1)))) ∨ True))) ∨ p5) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_37259768999959841496380629137 : ((((p3 ∧ ((((p4 → ((False → (p2 ∧ ((p5 ∧ (p2 ∨ (True ∧ True))) ∧ True))) ∨ p4)) ∧ (p4 ∨ p1)) → False) → False)) ∧ p3) ∧ True) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_42415265868095393187774474538 : (((p5 ∧ ((((p1 ∨ p1) ∧ (((p2 ∨ p5) → (p3 ∨ (True → ((p2 → (p1 → False)) → True)))) → (p1 ∧ p1))) → p4) → p3)) ∨ p1) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_705158457249592883180009397206 : ((((((((True ∧ False) ∨ p5) → p4) → p2) ∧ p4) ∧ (p5 ∨ (False ∨ (p2 → (p4 ∨ ((((p1 ∧ p1) ∨ (p3 ∧ p1)) ∨ True) → False)))))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_157492294485354024840268235716 : ((((p5 ∧ ((False ∨ p4) ∨ p2)) ∧ ((p3 ∨ ((p2 ∨ p3) → p3)) ∨ (p2 ∨ p3))) ∨ (p3 → False)) ∨ (p5 ∨ (((True → p3) ∧ True) ∨ True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_137497298363777269406126181571 : ((p5 ∧ (((True → ((p2 ∧ False) ∧ True)) ∧ (((False ∨ True) ∨ False) ∧ (((True → False) ∧ p1) ∨ p4))) ∧ (p5 → p5))) ∨ (p5 → (p4 ∨ p5))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_151870081873212547754296013417 : (((p2 ∨ (p5 ∧ ((False ∧ p5) → ((((True ∨ p1) ∨ p5) ∨ p4) → p4)))) ∨ (p2 ∨ (p2 ∨ (p1 ∨ p5)))) → ((False ∧ False) ∨ (True ∨ True))) := by
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
  case inr h7 =>
    -- Disjunctions on the left can always be decomposed.
    cases h7
    case inl h8 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- True on the right can always be proven directly.
      apply True.intro
    case inr h9 =>
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
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- Show the left disjunct based on <expert-advice>.
          apply Or.inl
          -- True on the right can always be proven directly.
          apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_778902462742543146503707998010 : (((p1 ∨ (p1 → (((p3 ∧ (True ∧ (False ∧ ((False ∧ p4) ∧ (True → p5))))) ∨ False) ∧ ((False ∧ ((p3 ∧ (p4 ∧ p4)) → p4)) ∨ p2)))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_738282506985833040196916676845 : ((((False ∧ p5) ∨ ((False ∨ (True ∧ (p1 ∨ (((p5 ∨ p1) ∧ p1) → p5)))) ∨ (((p5 ∧ True) ∨ ((True → (p4 ∨ p2)) → True)) ∨ p2))) ∨ False) ∧ True) := by
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
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_614633101241659374454276237842 : (((((p5 ∨ ((True → (p1 ∧ p3)) → (p2 ∨ (p4 → (((True ∧ p5) ∧ (True ∨ p1)) → p4))))) ∧ (p5 → ((p4 ∨ p3) ∧ p2))) ∨ False) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_259916901515599910997936116293 : ((p1 → p5) → ((((p3 ∨ (p5 ∧ (p4 ∧ (False ∧ False)))) ∨ ((p4 ∨ (((p3 ∨ p2) → (p1 ∨ True)) ∧ (p5 ∨ False))) → p1)) ∨ True) ∨ p4)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_714727065340722720634885365570 : ((((True ∧ (((p5 ∧ p5) ∨ p2) ∨ False)) → ((p4 → (((p2 ∨ (p4 → p2)) → p3) ∨ p1)) ∨ ((((p5 → p3) → p3) ∨ p5) ∧ False))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_724731427995017783513719279027 : ((((p3 ∨ (p4 ∧ True)) ∧ (((p3 ∧ p2) → (p3 → (p3 ∧ (p5 ∧ (p4 ∨ (p3 ∨ False)))))) → (p2 → (p5 ∨ ((p3 ∨ p1) ∨ p4))))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_59926590473075259352237076342 : (((p5 ∧ p5) → ((((False → p3) ∨ p3) ∧ p2) → ((((p2 ∨ True) ∨ (p5 ∧ (p4 ∧ p1))) → (False ∧ ((p3 → p5) ∨ p5))) → False))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_263098286277730005393933102816 : (True ∧ (((((True → (p4 ∨ p3)) → (False ∧ (p2 ∨ ((((p4 → p1) ∨ (p1 → p5)) ∨ p1) → p5)))) ∧ False) ∧ (p5 ∨ p2)) ∨ (False → p4))) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_178332708482339797663168854336 : (((((p3 ∧ p3) → (True ∨ p2)) → (p3 ∧ (p3 ∧ p1))) ∨ (p1 ∧ p1)) ∨ (True ∧ (p3 → (False ∨ (p2 ∨ (p5 → ((p4 ∧ p2) → p2))))))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h2
  -- Implications on the right can always be decomposed.
  intro h3
  -- Conjunctions on the left can always be decomposed.
  let h4 := h3.left
  let h5 := h3.right
  -- One of the premise coincides with the conclusion.
  exact h5



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_153303190789001648065028255112 : ((p1 ∨ ((((((p2 ∨ p2) → (p2 → p1)) ∧ (p1 ∨ p2)) ∨ p1) ∨ p5) ∧ (((p4 ∧ p3) → p4) ∨ True))) → ((p5 → p4) ∨ (False → p4))) := by
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
    -- Conjunctions on the left can always be decomposed.
    let h5 := h4.left
    let h6 := h4.right
    -- Disjunctions on the left can always be decomposed.
    cases h5
    case inl h7 =>
      -- Disjunctions on the left can always be decomposed.
      cases h7
      case inl h8 =>
        -- Conjunctions on the left can always be decomposed.
        let h9 := h8.left
        let h10 := h8.right
        -- Disjunctions on the left can always be decomposed.
        cases h10
        case inl h11 =>
          -- Disjunctions on the left can always be decomposed.
          cases h6
          case inl h12 =>
            -- Show the right disjunct based on <expert-advice>.
            apply Or.inr
            -- Implications on the right can always be decomposed.
            intro h13
            -- False on the left can always be used.
            apply False.elim h13
          case inr h14 =>
            -- Show the right disjunct based on <expert-advice>.
            apply Or.inr
            -- Implications on the right can always be decomposed.
            intro h15
            -- False on the left can always be used.
            apply False.elim h15
        case inr h16 =>
          -- Disjunctions on the left can always be decomposed.
          cases h6
          case inl h17 =>
            -- Show the right disjunct based on <expert-advice>.
            apply Or.inr
            -- Implications on the right can always be decomposed.
            intro h18
            -- False on the left can always be used.
            apply False.elim h18
          case inr h19 =>
            -- Show the right disjunct based on <expert-advice>.
            apply Or.inr
            -- Implications on the right can always be decomposed.
            intro h20
            -- False on the left can always be used.
            apply False.elim h20
      case inr h21 =>
        -- Disjunctions on the left can always be decomposed.
        cases h6
        case inl h22 =>
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- Implications on the right can always be decomposed.
          intro h23
          -- False on the left can always be used.
          apply False.elim h23
        case inr h24 =>
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- Implications on the right can always be decomposed.
          intro h25
          -- False on the left can always be used.
          apply False.elim h25
    case inr h26 =>
      -- Disjunctions on the left can always be decomposed.
      cases h6
      case inl h27 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- Implications on the right can always be decomposed.
        intro h28
        -- False on the left can always be used.
        apply False.elim h28
      case inr h29 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- Implications on the right can always be decomposed.
        intro h30
        -- False on the left can always be used.
        apply False.elim h30



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_152232103485079434198919891459 : (((p2 → (((p4 ∧ p1) ∧ p2) ∧ p2)) ∧ ((p1 ∧ (False → (p2 ∨ ((p5 → True) ∧ (p2 ∧ p2))))) ∨ False)) → ((p3 ∧ (p5 → False)) ∨ True)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
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
    -- False on the left can always be used.
    apply False.elim h7



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_255213242139695732473562875710 : ((p4 ∧ p4) → ((True ∨ p1) ∧ (((p1 ∧ False) ∨ p3) ∨ ((False ∨ True) ∧ (((False ∨ (p3 ∧ (p5 → p3))) ∨ (True ∧ (p2 ∨ p4))) ∨ p4))))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro
  -- Conjunctions on the left can always be decomposed.
  let h4 := h1.left
  let h5 := h1.right
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
  -- One of the premise coincides with the conclusion.
  exact h5



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_912213414376490129757459502792 : ((((((True ∨ p1) → ((False ∧ (p5 ∧ p1)) ∨ ((p5 ∨ False) → (p3 → (True ∨ False))))) ∨ True) → ((p1 ∧ (p1 → False)) ∧ (False ∧ p5))) → p4) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h1
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h2 : (((True ∨ p1) → ((False ∧ (p5 ∧ p1)) ∨ ((p5 ∨ False) → (p3 → (True ∨ False))))) ∨ True) := by
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
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_190960616479289933790745165063 : (((p5 ∨ ((p3 ∨ p3) ∨ True)) ∧ ((p5 ∨ p5) ∧ False)) ∨ ((p2 ∧ False) → (p4 ∧ ((p2 → p1) ∨ (((p3 ∨ True) ∨ True) ∧ (p1 ∨ p2)))))) := by
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
theorem thm_5_vars_266179764050538503714333584516 : (True ∧ (p4 → (((p2 ∧ ((True ∧ ((p1 ∨ (p3 ∧ (((((p4 → False) → p1) → p4) ∨ p5) → p1))) ∧ (p4 ∨ p2))) → False)) ∨ p4) ∨ p2))) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_639963232449038868321060612811 : (((((True ∨ (p1 ∧ False)) ∨ ((p4 → (True ∨ (((p5 ∧ False) ∨ p5) ∨ (p3 ∨ (p5 ∨ p5))))) → (True ∧ (p2 → (False ∨ p3))))) → p2) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_166199830676476005163608874958 : ((p1 ∧ ((p4 ∧ p3) ∨ (((p4 ∧ ((((p1 ∧ p1) → p3) → p3) → p4)) → False) ∧ p2))) ∨ ((((p5 ∨ p3) → p1) → (p4 ∧ p4)) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_258065647593299123159301858433 : ((p4 ∨ p2) → (((p5 → p3) → p5) ∨ ((p3 → ((p5 ∨ True) → True)) ∨ (p3 ∧ ((((p5 ∨ p4) → p4) ∨ (p4 → (p1 ∧ p5))) → False))))) := by
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
    -- Implications on the right can always be decomposed.
    intro h4
    -- True on the right can always be proven directly.
    apply True.intro
  case inr h5 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Implications on the right can always be decomposed.
    intro h6
    -- Implications on the right can always be decomposed.
    intro h7
    -- True on the right can always be proven directly.
    apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_158450327628891588545794967713 : (((p5 ∨ p1) ∨ ((p1 ∨ (p2 → (p4 ∨ (p1 ∨ (p1 → ((p4 ∧ (False ∧ p4)) ∧ p5)))))) → p2)) ∨ ((p1 → p5) ∨ ((p4 ∨ False) → p4))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
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



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_218536031865284286041190871639 : (((p5 ∨ False) → (p2 ∧ p1)) → ((p4 ∨ ((p5 ∨ ((p4 ∨ ((p2 → (p3 → False)) ∨ True)) → True)) → ((True ∧ p1) ∨ (p4 ∨ True)))) ∨ True)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_133646428587789399778638755851 : ((((((True → (((p4 ∨ (p5 → p1)) → p5) ∨ False)) ∧ p1) → (False ∨ ((p5 ∧ True) → p4))) ∧ (p5 ∧ True)) ∧ p4) ∨ (p4 → (False → True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_190701638735948092556340707954 : (((((p3 → p2) → (p4 ∧ False)) ∨ p2) ∧ (False ∧ p1)) ∨ (p3 → ((p5 → (p5 → (p1 ∨ p2))) → (p2 → ((p2 → (p4 → True)) ∧ True))))) := by
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
  -- Implications on the right can always be decomposed.
  intro h4
  -- Implications on the right can always be decomposed.
  intro h5
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_184564737625603419677998964050 : (((((p3 ∧ p4) → p1) ∨ ((p3 → p1) ∧ p5)) → (False ∧ p3)) ∨ (p4 → ((p3 → ((p3 → (True → False)) ∨ p4)) ∨ (p2 ∧ (p1 → p1))))) := by
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
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_177639988683848866587304002136 : ((((p2 ∧ (((True → False) → (p3 ∨ p4)) ∨ (p3 → True))) ∧ False) ∧ False) ∨ (((p3 ∧ ((True ∨ (p5 → False)) → p4)) ∨ (False ∧ p2)) → p4)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h2 =>
    -- Conjunctions on the left can always be decomposed.
    let h3 := h2.left
    let h4 := h2.right
    -- We want to use the implication h4 based on <expert-advice>. So we show its premise.
    have h5 : (True ∨ (p5 → False)) := by
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- True on the right can always be proven directly.
      apply True.intro
    -- We have shown the premise of h4, we can now drive its conclusion.
    let h6 := h4 h5
    -- One of the premise coincides with the conclusion.
    exact h6
  case inr h7 =>
    -- Conjunctions on the left can always be decomposed.
    let h8 := h7.left
    let h9 := h7.right
    -- False on the left can always be used.
    apply False.elim h8



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_632266068800533995448314165577 : (((((p1 ∧ (p5 ∨ (((False ∨ (p5 → ((((p4 → ((p5 → True) ∧ p3)) ∨ p1) ∧ p5) → p2))) ∨ (p1 ∧ True)) ∨ p3))) → p4) → False) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_317060529999710802009968886357 : (p3 ∨ (p4 → (((p4 ∧ p2) ∧ (p3 ∧ (False ∧ False))) ∨ ((False → (p4 ∨ (p3 ∨ p3))) ∨ ((p4 → False) ∧ ((p1 ∧ False) → (False ∨ True))))))) := by
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
  -- False on the left can always be used.
  apply False.elim h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_249227807386384121354066563136 : ((p4 ∨ p4) ∨ ((((p1 ∨ (p2 → (((p3 → p3) → ((False ∧ ((p2 ∧ p3) ∧ ((True → p3) ∧ True))) ∨ p3)) ∨ p4))) → p1) ∧ p4) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_260250075870545884837946085154 : ((p2 → p3) → (((True ∧ (p1 ∨ p5)) ∨ p4) → (((((p2 → p5) ∧ (True ∧ p4)) ∧ p2) ∨ (p4 ∨ p3)) ∨ (((True → True) → False) ∨ True)))) := by
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
    -- Disjunctions on the left can always be decomposed.
    cases h5
    case inl h6 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- True on the right can always be proven directly.
      apply True.intro
    case inr h7 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- True on the right can always be proven directly.
      apply True.intro
  case inr h8 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_146988397414821437528532531651 : ((((True ∨ (((p2 ∧ (p1 ∨ (p5 → p2))) ∨ ((p3 ∧ p1) ∧ (p3 ∨ (p5 ∧ False)))) → True)) → False) ∧ p2) ∨ ((False ∨ True) ∨ (p4 → p3))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_229151955261122191124229941412 : ((True → (False ∨ p3)) ∨ ((((p2 → ((False ∨ p4) ∨ p3)) ∨ ((p1 → False) → (p2 ∨ p4))) ∧ (((p1 ∧ p5) ∧ True) → (p3 → p4))) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



