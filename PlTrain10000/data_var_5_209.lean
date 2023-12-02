variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_351543744232777609170139441121 : (p4 → ((p3 ∧ ((p1 → ((((((p2 ∨ p3) → p1) ∧ (p1 ∧ p5)) → p4) ∧ p1) → False)) ∨ p3)) ∨ ((p1 ∧ p3) → (p1 ∨ (p4 ∨ False))))) := by
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
  -- One of the premise coincides with the conclusion.
  exact h3



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_39167350013539534044256861079 : ((((p5 ∨ p2) → ((p3 ∧ ((p3 → p3) ∨ (p1 ∨ ((p2 → ((True ∨ ((False ∧ p4) ∨ p1)) ∨ p1)) ∧ (p5 → p3))))) ∨ p3)) ∧ True) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_41846583564224181189088071025 : ((((False → (p4 ∨ p5)) ∧ ((p3 ∧ p4) ∨ ((False ∨ (((p4 ∧ p3) ∨ p1) → p4)) ∨ (p4 ∨ (p2 ∨ ((True → p1) ∨ p3)))))) ∨ True) ∨ False) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_241370524417671064591219072540 : ((False → False) ∧ ((True → True) → (((True → ((True → ((p5 ∨ (p2 → p3)) ∨ p5)) → (p1 → False))) ∧ p3) ∨ ((p4 ∧ False) → (p4 ∧ False))))) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h1
  -- False on the left can always be used.
  apply False.elim h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h3
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Conjunctions on the left can always be decomposed.
  let h4 := h3.left
  let h5 := h3.right
  -- False on the left can always be used.
  apply False.elim h5
  -- Conjunctions on the left can always be decomposed.
  let h6 := h3.left
  let h7 := h3.right
  -- False on the left can always be used.
  apply False.elim h7



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_556859372139209967547012517147 : (((p3 ∨ ((p3 → ((p2 → p5) → (((p5 ∧ (p3 ∧ True)) ∨ (True ∧ (p4 → p2))) ∨ True))) ∨ ((True → (p2 ∧ (p1 ∧ False))) ∨ p3))) ∧ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_47394145779737383402070121863 : ((((p5 → False) → ((p1 → False) ∨ ((p1 ∧ True) → ((((p1 → p3) ∧ False) ∨ ((p4 → (p2 → True)) → p2)) ∨ p1)))) ∨ (p4 → p4)) ∨ False) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_204361266011287619225865377942 : (((p2 ∨ ((p1 ∧ p5) ∨ p3)) ∧ p4) ∨ ((p3 ∧ (p1 → ((p4 ∧ False) → (p3 → p2)))) → (((True ∨ p2) ∧ (False → (p3 ∧ p1))) → p3))) := by
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
    let h6 := h1.left
    let h7 := h1.right
    -- One of the premise coincides with the conclusion.
    exact h6
  case inr h8 =>
    -- Conjunctions on the left can always be decomposed.
    let h9 := h1.left
    let h10 := h1.right
    -- One of the premise coincides with the conclusion.
    exact h9



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_602073637384120313010772485228 : ((((p5 ∧ ((p3 → (((True ∧ (p3 ∨ p4)) ∨ (p2 → (p4 → ((p4 ∨ (False ∧ (p1 → p5))) → True)))) → False)) ∨ (p1 ∨ p4))) ∧ p2) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_27955011496770511129429541879 : (((p1 → p4) → (p5 ∨ ((((p4 ∧ (((p4 ∨ ((((False ∨ False) ∧ p1) ∧ p3) → p3)) → p4) → p4)) ∨ False) → p1) ∨ (True ∨ p5)))) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
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
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_112046249926356685287977705707 : ((((True ∧ (p5 → p3)) → (p4 ∨ ((p1 ∧ ((p2 ∧ ((((p2 ∧ False) ∧ p2) → p1) ∨ (True ∧ p5))) ∧ False)) ∨ p2))) ∨ True) ∨ (p3 ∨ False)) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_215316994159949373160251484982 : ((p1 ∧ (True ∧ (p5 ∨ p2))) ∨ (((p1 ∨ (True ∧ False)) → ((((p3 ∨ p4) ∨ p2) ∧ p4) ∧ ((p5 → (p4 ∨ p4)) ∨ (True → p1)))) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_47083232360973938554947113319 : (((((((((p4 → (True ∨ (True ∧ False))) → p3) ∨ (p5 ∧ False)) → p1) ∧ p5) ∨ ((False ∨ p4) ∧ True)) → (p3 → False)) ∨ (True ∧ p4)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_7824114412458383269620162094 : (((((True → (True → (False ∧ False))) → ((((((p1 ∨ p2) ∧ False) ∧ p5) → ((p3 ∧ p3) ∨ p2)) → p3) ∨ (p1 ∨ p4))) ∧ p3) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_259363468821968886717052964032 : ((False → p2) → (p5 → ((False ∨ ((((p1 ∧ p4) → (((p3 ∧ False) ∧ p2) ∨ p1)) ∧ p5) ∨ p2)) → ((p1 ∨ (p2 ∨ (p5 ∧ True))) ∨ p2)))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Implications on the right can always be decomposed.
  intro h3
  -- Disjunctions on the left can always be decomposed.
  cases h3
  case inl h4 =>
    -- False on the left can always be used.
    apply False.elim h4
  case inr h5 =>
    -- Disjunctions on the left can always be decomposed.
    cases h5
    case inl h6 =>
      -- Conjunctions on the left can always be decomposed.
      let h7 := h6.left
      let h8 := h6.right
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Conjunctions on the right can always be decomposed.
      apply And.intro
      -- One of the premise coincides with the conclusion.
      exact h2
      -- True on the right can always be proven directly.
      apply True.intro
    case inr h9 =>
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Conjunctions on the right can always be decomposed.
      apply And.intro
      -- One of the premise coincides with the conclusion.
      exact h2
      -- True on the right can always be proven directly.
      apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_257512436846254140872073832167 : ((p3 ∨ False) → ((p2 ∨ (p5 ∨ (((False ∧ p3) ∧ p2) ∧ (True ∧ p2)))) ∨ (p2 ∨ (((p1 ∨ (p2 → (p3 ∧ p3))) → True) ∨ (True ∨ p3))))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h2 =>
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
  case inr h3 =>
    -- False on the left can always be used.
    apply False.elim h3



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_41402376289674516215800189431 : (((((((True → p3) → ((((True → p2) ∨ p1) ∨ True) → p5)) ∨ p1) ∧ p2) ∨ (p4 → ((p4 ∧ ((p5 → p4) ∨ p4)) ∨ p1))) ∨ False) ∨ p4) := by
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
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- One of the premise coincides with the conclusion.
  exact h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_41498067776321271811835532877 : (((((((p4 ∧ p5) → (p2 → p2)) ∨ False) → ((p2 → p5) ∧ False)) → ((p4 ∧ (p1 ∧ (p3 → (p3 ∨ True)))) ∧ (p2 ∨ p1))) ∨ p4) ∨ False) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h2 : (((p4 ∧ p5) → (p2 → p2)) ∨ False) := by
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Implications on the right can always be decomposed.
    intro h3
    -- Implications on the right can always be decomposed.
    intro h4
    -- Conjunctions on the left can always be decomposed.
    let h5 := h3.left
    let h6 := h3.right
    -- One of the premise coincides with the conclusion.
    exact h4
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h7 := h1 h2
  -- We need to get the right conjuct of h7 based on <expert-advice>.
  let h8 := h7.right
  -- False on the left can always be used.
  apply False.elim h8
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h9 : (((p4 ∧ p5) → (p2 → p2)) ∨ False) := by
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Implications on the right can always be decomposed.
    intro h10
    -- Implications on the right can always be decomposed.
    intro h11
    -- Conjunctions on the left can always be decomposed.
    let h12 := h10.left
    let h13 := h10.right
    -- One of the premise coincides with the conclusion.
    exact h11
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h14 := h1 h9
  -- We need to get the right conjuct of h14 based on <expert-advice>.
  let h15 := h14.right
  -- False on the left can always be used.
  apply False.elim h15
  -- Implications on the right can always be decomposed.
  intro h16
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- One of the premise coincides with the conclusion.
  exact h16
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h17 : (((p4 ∧ p5) → (p2 → p2)) ∨ False) := by
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Implications on the right can always be decomposed.
    intro h18
    -- Implications on the right can always be decomposed.
    intro h19
    -- Conjunctions on the left can always be decomposed.
    let h20 := h18.left
    let h21 := h18.right
    -- One of the premise coincides with the conclusion.
    exact h19
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h22 := h1 h17
  -- We need to get the right conjuct of h22 based on <expert-advice>.
  let h23 := h22.right
  -- False on the left can always be used.
  apply False.elim h23



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_671347942683706703951668756113 : ((((True → (p4 ∨ (((p4 ∧ p4) ∨ ((((p1 ∨ False) ∧ p3) ∨ (p4 ∨ p1)) ∧ ((p5 → p3) ∧ p4))) ∧ p5))) ∨ ((True ∧ p4) ∧ True)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_169883740282200722825181690157 : ((((p3 ∨ p2) ∨ ((p4 → False) ∨ (((p4 ∨ p3) ∧ True) → p3))) ∨ (p5 → p5)) ∧ ((p2 ∧ p2) ∨ (((p4 ∨ p2) ∨ p2) ∨ (False → True)))) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- One of the premise coincides with the conclusion.
  exact h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h2
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_38871943945917595717682057510 : ((((p1 → (True → p2)) ∧ ((True ∨ ((p2 → p1) ∨ (p2 ∧ True))) ∧ (((p5 ∧ p1) ∨ (p2 → (p2 → False))) ∧ (p5 ∧ p3)))) ∧ p5) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_4681503526528065550873865263 : (p5 → (p2 → (((p1 ∨ p3) ∨ (p1 ∧ (((((p5 ∧ True) → (p5 ∨ p4)) ∧ p5) → False) → (p3 ∨ ((False → p1) ∧ p3))))) ∨ True))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_300677751352337065295093583833 : (False ∨ ((((p2 → p4) → ((p5 ∧ (p5 ∧ p4)) ∨ (False → p1))) ∧ ((p1 ∨ (p5 ∨ p3)) ∨ p3)) ∨ ((p4 ∧ p3) ∨ (p5 → (p4 → p5))))) := by
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
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_686035857540375134777557403390 : (((((((p2 ∨ (p5 ∨ ((p3 → (True ∨ False)) ∧ False))) ∧ p2) ∧ (p1 ∧ p3)) → (p3 ∨ p5)) → ((((p2 ∨ True) ∧ True) ∨ p4) → False)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_209132671214959527132043990511 : ((p3 ∨ ((p4 ∧ (p5 ∨ p5)) ∧ p3)) → ((p1 ∧ (p2 → False)) ∨ (((False ∧ False) ∨ ((p1 → p3) → p3)) ∨ (p1 ∧ (False → (p2 ∨ p5)))))) := by
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
    -- Implications on the right can always be decomposed.
    intro h3
    -- One of the premise coincides with the conclusion.
    exact h2
  case inr h4 =>
    -- Conjunctions on the left can always be decomposed.
    let h5 := h4.left
    let h6 := h4.right
    -- Conjunctions on the left can always be decomposed.
    let h7 := h5.left
    let h8 := h5.right
    -- Disjunctions on the left can always be decomposed.
    cases h8
    case inl h9 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Implications on the right can always be decomposed.
      intro h10
      -- One of the premise coincides with the conclusion.
      exact h6
    case inr h11 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Implications on the right can always be decomposed.
      intro h12
      -- One of the premise coincides with the conclusion.
      exact h6



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_255213654797283925871115269956 : ((p4 ∧ p4) → ((p4 ∨ p5) ∧ ((((((((True ∧ p5) ∧ p3) ∨ p1) ∧ p2) → (False ∧ False)) ∨ p2) → (((True ∨ p2) → False) ∨ p4)) ∨ p1))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- One of the premise coincides with the conclusion.
  exact h3
  -- Conjunctions on the left can always be decomposed.
  let h4 := h1.left
  let h5 := h1.right
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h6
  -- Disjunctions on the left can always be decomposed.
  cases h6
  case inl h7 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h5
  case inr h8 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h5



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_670176295586913717107631459845 : (((((((p5 → p2) ∨ p1) ∧ p3) ∧ ((p2 ∨ (p4 → (((((p2 ∨ p5) ∧ p3) → p5) → p5) → p4))) ∨ p5)) ∨ (p3 ∨ (p5 ∧ False))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_632261679440249875473754746918 : (((((p1 ∧ (True ∧ ((((p3 ∧ p3) ∨ ((p5 → True) ∨ (p4 ∧ (p5 ∧ p5)))) → False) → ((p5 ∧ (False ∨ p2)) ∨ True)))) → False) → p4) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_54412955917286566282410723037 : ((((p5 ∨ ((p5 ∨ (p4 ∧ p1)) ∨ p1)) ∧ True) ∨ (((p3 → p5) ∧ (False ∧ (((True ∨ False) ∧ (p1 ∨ p3)) ∨ (p4 ∧ p3)))) ∨ True)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_652873710794161126055501165779 : ((((p4 ∨ ((p1 ∨ ((((((True ∨ (((False ∧ p1) ∧ p2) ∧ p4)) → p3) → p5) → (p3 → p4)) → p1) ∧ p1)) ∧ p3)) ∧ (False ∨ p3)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_346321286396151256857467337698 : (p3 → ((((p4 ∨ p4) ∨ (((p3 ∧ p2) ∨ ((((p5 ∧ p2) ∧ (True ∨ (p5 → False))) ∧ p5) ∨ p1)) ∨ p2)) → (p1 ∨ p2)) ∨ (p3 ∧ True))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- One of the premise coincides with the conclusion.
  exact h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_126411110202054624767090767163 : ((p1 ∧ (p4 ∨ ((((((p1 ∧ ((p4 ∧ (p3 → ((p4 ∧ p1) ∧ p1))) → p1)) ∨ p1) → p1) ∨ p2) ∧ p2) ∧ (p5 ∨ p3)))) → (False ∨ p1)) := by
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
    -- One of the premise coincides with the conclusion.
    exact h2
  case inr h5 =>
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
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- One of the premise coincides with the conclusion.
        exact h2
      case inr h12 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- One of the premise coincides with the conclusion.
        exact h2
    case inr h13 =>
      -- Disjunctions on the left can always be decomposed.
      cases h7
      case inl h14 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- One of the premise coincides with the conclusion.
        exact h2
      case inr h15 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- One of the premise coincides with the conclusion.
        exact h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_65348116014248865568291239194 : ((p3 ∨ ((((True → ((p5 ∨ p3) ∨ p3)) → (False ∧ (p1 ∨ p2))) → ((p3 → False) → p2)) → (((p2 → False) ∨ (p1 ∨ False)) ∧ True))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_50921095756980481983025592342 : ((((((False ∧ p4) ∨ ((True → p3) ∧ (True ∧ (p5 ∧ p5)))) ∧ p4) ∧ ((p4 → False) → p2)) ∧ ((p1 ∨ (p1 ∨ (p3 ∨ p4))) ∨ True)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_175075852532633866706046285050 : ((p3 ∧ (((p5 ∨ (p4 ∨ (p1 ∧ (True → (p5 ∧ p3))))) ∧ p2) ∧ (p1 ∧ True))) → (((False → False) ∧ (p3 → ((p4 ∨ False) ∧ p5))) ∨ p2)) := by
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
    -- Conjunctions on the left can always be decomposed.
    let h9 := h5.left
    let h10 := h5.right
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h7
  case inr h11 =>
    -- Disjunctions on the left can always be decomposed.
    cases h11
    case inl h12 =>
      -- Conjunctions on the left can always be decomposed.
      let h13 := h5.left
      let h14 := h5.right
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- One of the premise coincides with the conclusion.
      exact h7
    case inr h15 =>
      -- Conjunctions on the left can always be decomposed.
      let h16 := h15.left
      let h17 := h15.right
      -- Conjunctions on the left can always be decomposed.
      let h18 := h5.left
      let h19 := h5.right
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- One of the premise coincides with the conclusion.
      exact h7



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_2561635164241382343896025338 : ((False ∧ ((((False ∧ p3) ∨ p1) ∧ p4) ∨ p2)) ∨ (True → (False → ((False ∨ (p3 ∨ ((p3 → (True → p3)) ∧ (p1 → True)))) → p2)))) := by
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
    -- False on the left can always be used.
    apply False.elim h4
  case inr h5 =>
    -- Disjunctions on the left can always be decomposed.
    cases h5
    case inl h6 =>
      -- False on the left can always be used.
      apply False.elim h2
    case inr h7 =>
      -- Conjunctions on the left can always be decomposed.
      let h8 := h7.left
      let h9 := h7.right
      -- False on the left can always be used.
      apply False.elim h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_975579142954191593094272485959 : ((((p5 → True) → ((((False ∨ p1) → ((p1 → p5) → p5)) ∧ ((p4 ∨ p4) ∨ (((False → (p5 ∧ p2)) ∧ (True ∨ p4)) ∧ True))) ∧ False)) → p3) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h1
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h2 : (p5 → True) := by
    -- Implications on the right can always be decomposed.
    intro h3
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h4 := h1 h2
  -- We need to get the right conjuct of h4 based on <expert-advice>.
  let h5 := h4.right
  -- False on the left can always be used.
  apply False.elim h5
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_208032414489298676947562117483 : (((p1 ∧ (True ∧ p2)) ∨ (False → p2)) → ((p3 → ((p5 ∧ ((p3 ∨ p4) ∧ (p5 ∧ (True → (p5 ∧ p2))))) → p1)) ∨ ((False ∧ p5) → p5))) := by
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
    -- Conjunctions on the left can always be decomposed.
    let h8 := h7.left
    let h9 := h7.right
    -- False on the left can always be used.
    apply False.elim h8
  case inr h10 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h11
    -- Conjunctions on the left can always be decomposed.
    let h12 := h11.left
    let h13 := h11.right
    -- False on the left can always be used.
    apply False.elim h12



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_185029135451239552873092917223 : (((p5 ∨ p4) ∧ (p2 → ((True ∧ p4) ∧ ((p1 → p2) → p4)))) ∨ ((((True ∨ p2) ∨ p2) ∧ False) → ((p4 ∨ p1) ∨ ((p5 ∨ False) ∨ p5)))) := by
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
      -- False on the left can always be used.
      apply False.elim h3
    case inr h6 =>
      -- False on the left can always be used.
      apply False.elim h3
  case inr h7 =>
    -- False on the left can always be used.
    apply False.elim h3



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_226037879890534784054527495314 : (((p5 ∧ True) ∨ p4) ∨ (((((False ∧ p2) ∧ p5) ∨ p1) ∧ p4) ∨ ((((p1 ∧ (((False ∨ False) ∧ p1) ∧ p1)) ∧ False) → (True ∧ p4)) ∧ True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- True on the right can always be proven directly.
  apply True.intro
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
    -- False on the left can always be used.
    apply False.elim h10
  case inr h11 =>
    -- False on the left can always be used.
    apply False.elim h11
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_111842402265505405957096723592 : ((((p2 ∨ ((p3 → (p2 ∧ (((p2 ∨ (p3 ∨ p3)) → p3) → True))) ∨ (p2 ∧ (False ∧ p2)))) ∨ ((False → False) ∨ p5)) ∨ p4) ∨ (p1 → p5)) := by
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
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_723685627693942628533018492817 : (((((True → True) → p1) ∧ (p5 ∧ ((((p5 ∨ False) ∧ ((False ∨ p3) ∧ p4)) ∨ ((p2 ∨ p1) → (p1 → True))) ∧ (p1 → (p4 ∨ False))))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_64341989071173341236980167302 : ((p1 ∨ ((True → ((p3 ∨ p4) ∧ (p4 → ((p3 ∧ ((True ∨ False) → (((p4 → p1) → ((p5 ∧ False) ∧ True)) ∧ p5))) ∨ p1)))) ∧ p2)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_200571600016539436824045109454 : ((True ∧ (((p2 ∧ p5) ∨ (p2 ∧ False)) ∧ True)) → (((((((p5 ∨ p3) → p1) → (p1 → p1)) ∨ (p4 ∧ p2)) → p2) → (p4 ∨ False)) ∨ p5)) := by
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
    -- Conjunctions on the left can always be decomposed.
    let h7 := h6.left
    let h8 := h6.right
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h8
  case inr h9 =>
    -- Conjunctions on the left can always be decomposed.
    let h10 := h9.left
    let h11 := h9.right
    -- False on the left can always be used.
    apply False.elim h11



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_65665634187601272247430810747 : ((p4 ∨ (((((p2 ∧ p4) ∨ (True ∧ (p1 → True))) ∧ ((True ∧ p3) ∧ (((p2 → p1) ∨ p4) → ((p5 → p1) ∧ False)))) ∨ p2) → p1)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_197501155664293962028371394527 : (((False ∨ (p2 ∧ (False ∧ p2))) ∧ (True ∧ False)) ∨ ((((p1 ∧ p3) ∨ p1) ∧ ((p4 ∧ (False ∨ (p2 ∧ p5))) ∧ False)) → (p1 ∨ (True ∧ p4)))) := by
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
    let h7 := h3.left
    let h8 := h3.right
    -- Conjunctions on the left can always be decomposed.
    let h9 := h7.left
    let h10 := h7.right
    -- Disjunctions on the left can always be decomposed.
    cases h10
    case inl h11 =>
      -- False on the left can always be used.
      apply False.elim h11
    case inr h12 =>
      -- Conjunctions on the left can always be decomposed.
      let h13 := h12.left
      let h14 := h12.right
      -- False on the left can always be used.
      apply False.elim h8
  case inr h15 =>
    -- Conjunctions on the left can always be decomposed.
    let h16 := h3.left
    let h17 := h3.right
    -- Conjunctions on the left can always be decomposed.
    let h18 := h16.left
    let h19 := h16.right
    -- Disjunctions on the left can always be decomposed.
    cases h19
    case inl h20 =>
      -- False on the left can always be used.
      apply False.elim h20
    case inr h21 =>
      -- Conjunctions on the left can always be decomposed.
      let h22 := h21.left
      let h23 := h21.right
      -- False on the left can always be used.
      apply False.elim h17



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_588161168157707644243326313570 : (((((((p1 ∨ ((p3 → (p3 ∨ p1)) ∧ p5)) ∨ (p1 ∨ False)) ∧ (((False ∨ (True ∧ ((p2 → True) ∧ p3))) ∧ p3) ∧ True)) ∨ p5) ∧ p4) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_45172319725381983312702303647 : (((True ∧ ((p2 ∨ False) ∧ (p4 ∧ ((p1 ∨ ((p4 ∧ True) → ((p4 ∧ (False ∨ False)) → p3))) ∧ (p5 ∧ (p3 ∨ (p4 ∨ True))))))) → False) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_56705142773891682699300936558 : ((((p3 ∧ p2) ∨ p1) ∧ (p4 ∨ (((p3 ∨ True) ∨ (p5 ∧ ((((p2 → True) ∨ False) → ((p4 ∨ p3) ∧ p1)) ∧ p3))) ∧ (p1 ∧ p5)))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_354617308844768771683570697043 : (p5 → ((((((True ∨ (p4 → p4)) → p3) ∨ (p1 ∨ p4)) ∧ ((p2 ∨ (p1 ∨ ((p2 ∨ ((True ∨ p1) ∨ False)) ∧ p5))) ∨ p5)) ∨ p3) ∨ True)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_669392170268164741775181674023 : ((((((p1 ∧ (((False → ((p4 → ((p2 ∧ p4) ∨ (p5 ∧ p4))) ∨ p1)) ∧ p3) → p4)) ∨ False) ∨ (True ∨ p3)) ∨ ((p4 → False) ∧ True)) ∨ False) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
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
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_326584929636486178752933068006 : (True → (((((p5 ∧ p2) → ((p2 → p2) → (((p3 ∨ p4) ∨ (p2 → False)) ∧ p4))) ∧ p3) → (((p5 → (p5 ∧ True)) → p5) ∨ p3)) ∧ True)) := by
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
  -- One of the premise coincides with the conclusion.
  exact h4
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_308375899438099067716658544111 : (p2 ∨ ((((((True ∧ (p1 → (p2 ∧ p4))) → p3) ∨ (((True ∨ (p3 ∧ True)) → ((p4 → (p5 ∨ p4)) ∧ p1)) ∨ p1)) → p5) ∨ False) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_309364265961418589104848750572 : (p2 ∨ (((p1 ∨ ((p1 ∧ p5) ∧ True)) ∨ ((p2 → (True ∧ ((((p5 ∧ p5) → (True ∨ p3)) → p2) ∧ (p3 ∨ p2)))) ∨ p1)) ∨ (False → p3))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_153270089142242716282567812403 : ((False ∨ ((p2 → p4) → ((((False ∨ ((True ∨ p4) → p4)) ∨ p3) → (False ∧ ((p2 → p1) → p3))) ∨ p2))) → ((True → p1) → (p2 ∨ p1))) := by
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
    -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
    have h5 : True := by
      -- True on the right can always be proven directly.
      apply True.intro
    -- We have shown the premise of h2, we can now drive its conclusion.
    let h6 := h2 h5
    -- One of the premise coincides with the conclusion.
    exact h6



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_145135581001461747387523796483 : ((((((p2 ∧ True) → (p2 → p4)) → (p3 ∨ p3)) ∧ p4) → ((((True ∧ (p2 ∨ True)) → p3) ∧ p3) ∧ True)) ∧ ((False → False) ∨ (p3 ∨ p1))) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
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
    -- We want to use the implication h6 based on <expert-advice>. So we show its premise.
    have h8 : ((p2 ∧ True) → (p2 → p4)) := by
      -- Implications on the right can always be decomposed.
      intro h9
      -- Implications on the right can always be decomposed.
      intro h10
      -- Conjunctions on the left can always be decomposed.
      let h11 := h9.left
      let h12 := h9.right
      -- One of the premise coincides with the conclusion.
      exact h7
    -- We have shown the premise of h6, we can now drive its conclusion.
    let h13 := h6 h8
    -- Disjunctions on the left can always be decomposed.
    cases h13
    case inl h14 =>
      -- One of the premise coincides with the conclusion.
      exact h14
    case inr h15 =>
      -- One of the premise coincides with the conclusion.
      exact h15
  case inr h16 =>
    -- Conjunctions on the left can always be decomposed.
    let h17 := h1.left
    let h18 := h1.right
    -- We want to use the implication h17 based on <expert-advice>. So we show its premise.
    have h19 : ((p2 ∧ True) → (p2 → p4)) := by
      -- Implications on the right can always be decomposed.
      intro h20
      -- Implications on the right can always be decomposed.
      intro h21
      -- Conjunctions on the left can always be decomposed.
      let h22 := h20.left
      let h23 := h20.right
      -- One of the premise coincides with the conclusion.
      exact h18
    -- We have shown the premise of h17, we can now drive its conclusion.
    let h24 := h17 h19
    -- Disjunctions on the left can always be decomposed.
    cases h24
    case inl h25 =>
      -- One of the premise coincides with the conclusion.
      exact h25
    case inr h26 =>
      -- One of the premise coincides with the conclusion.
      exact h26
  -- Conjunctions on the left can always be decomposed.
  let h27 := h1.left
  let h28 := h1.right
  -- We want to use the implication h27 based on <expert-advice>. So we show its premise.
  have h29 : ((p2 ∧ True) → (p2 → p4)) := by
    -- Implications on the right can always be decomposed.
    intro h30
    -- Implications on the right can always be decomposed.
    intro h31
    -- Conjunctions on the left can always be decomposed.
    let h32 := h30.left
    let h33 := h30.right
    -- One of the premise coincides with the conclusion.
    exact h28
  -- We have shown the premise of h27, we can now drive its conclusion.
  let h34 := h27 h29
  -- Disjunctions on the left can always be decomposed.
  cases h34
  case inl h35 =>
    -- One of the premise coincides with the conclusion.
    exact h35
  case inr h36 =>
    -- One of the premise coincides with the conclusion.
    exact h36
  -- True on the right can always be proven directly.
  apply True.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h37
  -- False on the left can always be used.
  apply False.elim h37



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_156619166150945015339382870037 : (((((p5 → (((((p4 ∧ (p4 ∧ False)) → True) ∧ p1) → False) ∧ (True → False))) ∧ p1) ∨ True) ∧ p3) ∨ ((p5 ∧ False) → ((False ∧ False) ∨ False))) := by
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
theorem thm_5_vars_256090345674305444505411191648 : ((True ∨ p5) → ((((((p2 → False) ∨ p4) → (False ∧ (((True ∨ (p4 ∨ True)) ∧ p4) ∨ p3))) ∨ ((False → (p2 ∧ p5)) → False)) ∧ p2) ∨ True)) := by
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
theorem thm_5_vars_50415474535996939375179670515 : (((p1 ∧ (p2 → (True → ((p4 ∧ ((p5 → False) ∨ ((p3 ∧ ((p2 ∨ p5) ∧ p4)) ∧ False))) ∧ False)))) ∨ (p3 ∨ ((False ∧ True) → p5))) ∨ p3) := by
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
theorem thm_5_vars_95505598095080410418768624500 : ((p5 ∧ ((p4 ∨ (((True ∧ p3) ∨ ((p4 ∨ p3) ∨ (False → p2))) ∨ ((p4 ∧ ((p4 ∧ p4) ∨ (p2 ∨ (p5 ∨ True)))) ∨ p2))) → False)) → False) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- We want to use the implication h3 based on <expert-advice>. So we show its premise.
  have h4 : (p4 ∨ (((True ∧ p3) ∨ ((p4 ∨ p3) ∨ (False → p2))) ∨ ((p4 ∧ ((p4 ∧ p4) ∨ (p2 ∨ (p5 ∨ True)))) ∨ p2))) := by
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h5
    -- False on the left can always be used.
    apply False.elim h5
  -- We have shown the premise of h3, we can now drive its conclusion.
  let h6 := h3 h4
  -- False on the left can always be used.
  apply False.elim h6



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_60245617850485012258198959476 : (((False → True) → ((((p2 ∨ True) ∨ ((True ∨ p4) ∨ False)) ∧ (p2 ∨ (((p3 ∨ (p3 ∨ True)) → p2) → (False ∨ p2)))) ∨ (p1 ∨ True))) ∨ p3) := by
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
theorem thm_5_vars_788057426335179665068014054171 : (((p5 ∨ (((True → (((False → False) ∧ p5) ∧ ((False ∨ p2) ∧ (((False ∨ (p1 ∧ (p5 ∧ True))) → (p5 → p1)) → False)))) ∨ p5) ∧ p5)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_153350167944371154011025209996 : ((p2 ∨ (((p4 ∨ (p4 → p2)) ∨ (True ∨ ((p5 ∨ p2) ∧ (p3 ∨ p1)))) ∧ ((True → False) → (p1 ∧ p3)))) → (((p3 ∨ True) → p3) → p3)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h3 =>
    -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
    have h4 : (p3 ∨ True) := by
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- True on the right can always be proven directly.
      apply True.intro
    -- We have shown the premise of h2, we can now drive its conclusion.
    let h5 := h2 h4
    -- One of the premise coincides with the conclusion.
    exact h5
  case inr h6 =>
    -- Conjunctions on the left can always be decomposed.
    let h7 := h6.left
    let h8 := h6.right
    -- Disjunctions on the left can always be decomposed.
    cases h7
    case inl h9 =>
      -- Disjunctions on the left can always be decomposed.
      cases h9
      case inl h10 =>
        -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
        have h11 : (p3 ∨ True) := by
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- True on the right can always be proven directly.
          apply True.intro
        -- We have shown the premise of h2, we can now drive its conclusion.
        let h12 := h2 h11
        -- One of the premise coincides with the conclusion.
        exact h12
      case inr h13 =>
        -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
        have h14 : (p3 ∨ True) := by
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- True on the right can always be proven directly.
          apply True.intro
        -- We have shown the premise of h2, we can now drive its conclusion.
        let h15 := h2 h14
        -- One of the premise coincides with the conclusion.
        exact h15
    case inr h16 =>
      -- Disjunctions on the left can always be decomposed.
      cases h16
      case inl h17 =>
        -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
        have h18 : (p3 ∨ True) := by
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- True on the right can always be proven directly.
          apply True.intro
        -- We have shown the premise of h2, we can now drive its conclusion.
        let h19 := h2 h18
        -- One of the premise coincides with the conclusion.
        exact h19
      case inr h20 =>
        -- Conjunctions on the left can always be decomposed.
        let h21 := h20.left
        let h22 := h20.right
        -- Disjunctions on the left can always be decomposed.
        cases h21
        case inl h23 =>
          -- Disjunctions on the left can always be decomposed.
          cases h22
          case inl h24 =>
            -- One of the premise coincides with the conclusion.
            exact h24
          case inr h25 =>
            -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
            have h26 : (p3 ∨ True) := by
              -- Show the right disjunct based on <expert-advice>.
              apply Or.inr
              -- True on the right can always be proven directly.
              apply True.intro
            -- We have shown the premise of h2, we can now drive its conclusion.
            let h27 := h2 h26
            -- One of the premise coincides with the conclusion.
            exact h27
        case inr h28 =>
          -- Disjunctions on the left can always be decomposed.
          cases h22
          case inl h29 =>
            -- One of the premise coincides with the conclusion.
            exact h29
          case inr h30 =>
            -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
            have h31 : (p3 ∨ True) := by
              -- Show the right disjunct based on <expert-advice>.
              apply Or.inr
              -- True on the right can always be proven directly.
              apply True.intro
            -- We have shown the premise of h2, we can now drive its conclusion.
            let h32 := h2 h31
            -- One of the premise coincides with the conclusion.
            exact h32



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_177670131121917936729489569378 : ((((((True ∧ p2) ∨ (((True ∧ p4) → True) → p5)) ∨ p4) → p3) ∧ p2) ∨ (((p3 → p1) ∧ ((False ∧ (p5 → p2)) ∧ True)) ∨ (False → False))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_37615064277865664406206883451 : ((((((p1 ∨ p4) → (((p2 → (((((p5 → False) ∨ True) ∨ p1) → p1) ∨ ((p2 ∧ p1) → True))) → False) ∧ p2)) ∧ p4) → False) ∧ True) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_679866907561976148523846661912 : (((((p5 → ((((((p5 ∨ False) ∨ (p2 ∨ False)) ∨ (p5 ∨ True)) ∧ (p5 ∧ True)) → p2) ∧ False)) ∨ p2) → ((p2 → True) → (p5 ∨ p2))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_62064609203710157931168899659 : ((p2 ∧ (True ∧ ((((p3 ∧ ((False → (False ∨ (p1 ∨ (p2 ∧ p5)))) → (p4 ∧ p2))) ∨ p2) ∧ p3) ∧ ((p5 ∧ (p3 ∨ p5)) ∧ False)))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_179759465732639787990648121321 : ((((False → (p3 ∨ (True ∨ (False ∨ p2)))) ∧ ((False ∨ p5) → False)) ∧ p5) → ((p1 ∨ p5) → (p3 ∨ ((True ∨ p3) ∧ (p5 → (p2 ∧ p5)))))) := by
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
    -- We want to use the implication h7 based on <expert-advice>. So we show its premise.
    have h8 : (False ∨ p5) := by
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- One of the premise coincides with the conclusion.
      exact h5
    -- We have shown the premise of h7, we can now drive its conclusion.
    let h9 := h7 h8
    -- False on the left can always be used.
    apply False.elim h9
  case inr h10 =>
    -- Conjunctions on the left can always be decomposed.
    let h11 := h1.left
    let h12 := h1.right
    -- Conjunctions on the left can always be decomposed.
    let h13 := h11.left
    let h14 := h11.right
    -- We want to use the implication h14 based on <expert-advice>. So we show its premise.
    have h15 : (False ∨ p5) := by
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- One of the premise coincides with the conclusion.
      exact h12
    -- We have shown the premise of h14, we can now drive its conclusion.
    let h16 := h14 h15
    -- False on the left can always be used.
    apply False.elim h16



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_231738461366428162279673709619 : (((p2 ∧ p5) → p2) → (p4 → (((((((False → (p5 → p1)) ∧ p4) ∧ p1) → p1) → p2) ∨ (p5 → ((p1 ∧ p1) → (p1 ∧ p4)))) ∨ p1))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h3
  -- Implications on the right can always be decomposed.
  intro h4
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Conjunctions on the left can always be decomposed.
  let h5 := h4.left
  let h6 := h4.right
  -- One of the premise coincides with the conclusion.
  exact h6
  -- Conjunctions on the left can always be decomposed.
  let h7 := h4.left
  let h8 := h4.right
  -- One of the premise coincides with the conclusion.
  exact h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_200543643888341260097082769555 : (((False → False) → ((p4 ∨ (p2 ∨ True)) → p4)) → ((((((((True ∨ p4) ∧ False) ∨ ((p2 → False) ∨ p4)) ∨ p3) → True) ∧ p1) → p4) ∨ p4)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h2 : (False → False) := by
    -- Implications on the right can always be decomposed.
    intro h3
    -- False on the left can always be used.
    apply False.elim h3
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h4 := h1 h2
  -- We want to use the implication h4 based on <expert-advice>. So we show its premise.
  have h5 : (p4 ∨ (p2 ∨ True)) := by
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h4, we can now drive its conclusion.
  let h6 := h4 h5
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h6



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_40358467916833444391860491264 : (((((((((p5 ∨ p5) ∨ ((p5 ∧ p3) ∧ ((True → (p5 ∨ p4)) ∨ p4))) ∧ False) → False) ∨ (p2 ∧ (p5 ∨ p4))) → p4) ∨ True) ∨ p4) ∨ p3) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_2083644573636826053348711640 : ((((((p4 ∧ p4) ∨ False) ∨ (True ∨ p5)) → (p4 → p5)) ∨ ((p5 → (p4 ∧ p4)) ∨ False)) ∨ (p3 → ((p4 ∨ p1) → (p3 ∨ p3)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
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
theorem thm_5_vars_310546783992012082223160133798 : (p2 ∨ ((p3 ∧ (False → ((p5 ∧ p3) → False))) → (((((p1 ∨ p2) → p3) → p2) ∨ False) ∨ ((((p5 ∧ (p1 ∨ p4)) → p1) ∨ False) ∨ p3)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_111759976285979066912937822180 : (((((False → (p5 ∨ (p5 → (p4 → ((p3 ∧ p2) ∧ ((((p4 ∧ p4) ∧ p1) ∧ p4) ∨ p2)))))) → False) ∧ (p1 ∨ True)) ∨ p1) ∨ (False → p1)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_166702651639745706948269909872 : ((p3 → ((((p2 ∨ ((p5 → False) ∨ False)) → p5) → ((p3 → p2) ∧ (False ∧ p4))) ∨ p4)) ∨ (False ∨ ((True → ((True ∧ p2) ∨ p2)) → True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_211549870497714172772169623426 : (((p1 ∨ p1) → (True ∧ p1)) ∧ (((p5 ∧ p5) ∨ ((False ∨ (((p3 ∧ ((p2 ∨ False) ∨ (p2 → p1))) ∧ p1) ∨ True)) ∨ p3)) ∨ (False ∨ p1))) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h2 =>
    -- One of the premise coincides with the conclusion.
    exact h2
  case inr h3 =>
    -- One of the premise coincides with the conclusion.
    exact h3
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



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_48436727859895479844045153127 : (((p4 → ((p3 ∨ ((p4 ∧ False) ∧ (True ∨ (p3 ∧ p2)))) → ((((p3 ∨ p3) → (True ∨ p3)) ∨ (p3 ∧ p2)) ∧ p5))) → (p3 ∧ p2)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_634918412386381167568324863972 : (((((p2 ∨ (((True ∨ ((p5 → True) ∧ (p4 ∨ p2))) ∨ (p3 ∨ p2)) ∧ ((p5 ∧ (p5 ∧ p2)) → p2))) ∨ (p5 ∨ (False → False))) → p3) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_66439978826490554116219198965 : ((True → ((((p3 → ((p4 ∨ ((p3 ∧ False) ∨ ((((p2 → p1) ∧ False) → p4) ∧ (p4 ∨ p5)))) → p1)) ∧ (True ∧ p1)) → p5) ∧ p2)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_183448664381140369027955644002 : ((p2 ∨ (((p5 ∨ ((False ∨ p1) ∨ False)) ∨ True) ∨ (p2 ∨ p1))) ∧ (False ∨ (((p3 → (p4 → (p2 ∧ (False ∨ False)))) → (False → p4)) ∧ True))) := by
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
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- False on the left can always be used.
  apply False.elim h2
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_212793106593536647243098889130 : ((p1 → (True → (p5 ∨ p1))) ∧ ((((False ∨ p1) ∨ (p3 → p2)) → (True ∧ p5)) ∨ ((False → False) ∨ ((p1 → (True ∧ True)) → (p1 ∧ p1))))) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h3
  -- False on the left can always be used.
  apply False.elim h3



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_49659891860524542233075198723 : (((((True → p4) ∧ p2) ∨ ((p4 ∧ ((p4 → True) → p2)) ∧ (p1 → (((p4 ∧ False) → (p1 ∧ p4)) ∧ True)))) → (p2 ∨ (p1 ∧ p2))) ∨ p4) := by
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
    -- One of the premise coincides with the conclusion.
    exact h4
  case inr h5 =>
    -- Conjunctions on the left can always be decomposed.
    let h6 := h5.left
    let h7 := h5.right
    -- Conjunctions on the left can always be decomposed.
    let h8 := h6.left
    let h9 := h6.right
    -- We want to use the implication h9 based on <expert-advice>. So we show its premise.
    have h10 : (p4 → True) := by
      -- Implications on the right can always be decomposed.
      intro h11
      -- True on the right can always be proven directly.
      apply True.intro
    -- We have shown the premise of h9, we can now drive its conclusion.
    let h12 := h9 h10
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- One of the premise coincides with the conclusion.
    exact h12



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_318580226362595781018853420030 : (p4 ∨ (((p4 ∧ ((((p2 ∨ p3) → p4) → (((p4 → True) → p2) → (False ∧ ((p1 ∧ p3) → p5)))) ∨ p4)) ∨ (True ∧ True)) ∨ (False → True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_135080034780673712663822603316 : (((((((p1 → p5) → (False ∧ ((p2 ∧ p2) → (p4 → False)))) ∨ p2) ∨ True) ∨ ((p5 ∨ p5) ∧ True)) ∨ (p5 ∨ p3)) ∨ (p1 → (p4 ∧ True))) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_40755165151165201711342138585 : (((((p1 → p5) ∧ ((p1 ∨ ((False → p5) ∨ (False → ((False ∧ p2) ∨ ((((p3 ∧ True) ∧ p5) ∧ p2) → p3))))) ∨ p5)) → False) ∨ True) ∨ p2) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_350926819452048094217140035546 : (p4 → ((((p3 ∧ ((((p4 → p1) ∧ (p3 ∨ (p3 → (p4 → p5)))) ∧ (True ∨ p2)) ∧ ((p5 → p5) ∨ p1))) ∨ p2) → p2) ∨ (p2 → p2))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h2
  -- One of the premise coincides with the conclusion.
  exact h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_150017211001133257632891937643 : ((p5 ∨ ((((p1 → p3) ∧ p1) ∨ ((p3 → p2) → (((p2 ∧ p1) → False) ∧ p1))) ∨ (p4 → (p3 → p4)))) ∨ (p2 ∧ (p4 → (False ∨ p4)))) := by
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
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_135068025632373007798319156350 : ((((((((p4 → ((p3 ∧ True) → p1)) ∨ (p2 ∨ p5)) → p4) ∨ p5) ∨ (p5 ∨ p3)) ∧ (p3 → True)) ∨ (p2 → True)) ∨ ((True ∧ p4) ∧ False)) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_148682097135008593125868908107 : ((((p3 ∧ (False ∧ False)) ∧ ((p2 → p4) ∧ True)) ∨ (p4 → ((p5 ∨ ((p2 ∨ p4) ∧ (p4 → False))) ∧ p4))) ∨ (((p2 ∨ p1) ∧ False) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_621290587257218523936142428605 : ((((True ∧ ((((True ∨ True) → True) ∧ ((True ∧ (p1 → p5)) ∧ (p3 ∧ p1))) ∨ ((p3 → p3) ∧ ((True ∨ p1) → (p2 ∨ p2))))) ∨ True) ∨ p5) ∧ True) := by
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
theorem thm_5_vars_165003960729237632975105959392 : ((((p5 → ((True ∨ (p2 ∨ (p4 ∨ p4))) ∧ p1)) → (((True → p3) → p1) → p5)) → p2) ∨ (((False → False) ∨ ((True ∨ True) ∨ False)) ∧ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_427912454036930059436867300862 : ((((((True ∧ (False → False)) → ((p4 ∧ ((p3 ∨ (p1 → False)) ∧ ((False → (p4 ∧ (False → True))) ∧ False))) ∨ True)) ∨ p1) ∨ (True → p2)) ∧ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
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
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_140064210205360847012078916271 : ((((((True → p3) ∨ p2) → p1) → (((p2 ∨ (p1 ∧ (p1 ∨ p1))) → p2) ∨ (p2 → (p3 → p1)))) ∨ (True ∧ p5)) → (p3 → (p1 → p1))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Implications on the right can always be decomposed.
  intro h3
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h4 =>
    -- One of the premise coincides with the conclusion.
    exact h3
  case inr h5 =>
    -- Conjunctions on the left can always be decomposed.
    let h6 := h5.left
    let h7 := h5.right
    -- One of the premise coincides with the conclusion.
    exact h3



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_199635009054878325227023964173 : (((((p5 → p2) → p5) ∨ (p2 ∧ p5)) → p2) → ((True → p2) → ((((p3 ∧ (True → p5)) → p5) ∧ p2) ∨ ((p4 → False) ∧ (False ∨ p3))))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h3
  -- Conjunctions on the left can always be decomposed.
  let h4 := h3.left
  let h5 := h3.right
  -- We want to use the implication h5 based on <expert-advice>. So we show its premise.
  have h6 : True := by
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h5, we can now drive its conclusion.
  let h7 := h5 h6
  -- One of the premise coincides with the conclusion.
  exact h7
  -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
  have h8 : True := by
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h2, we can now drive its conclusion.
  let h9 := h2 h8
  -- One of the premise coincides with the conclusion.
  exact h9



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_78892506851843175740161782542 : ((((p5 ∧ False) ∨ (((True → p4) ∧ ((p1 ∧ (p1 → False)) ∧ (p2 ∨ p1))) ∧ (((p4 ∨ False) → (False ∨ False)) ∧ p5))) ∧ (p4 ∨ p2)) → False) := by
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
    apply False.elim h6
  case inr h7 =>
    -- Conjunctions on the left can always be decomposed.
    let h8 := h7.left
    let h9 := h7.right
    -- Conjunctions on the left can always be decomposed.
    let h10 := h8.left
    let h11 := h8.right
    -- Conjunctions on the left can always be decomposed.
    let h12 := h11.left
    let h13 := h11.right
    -- Conjunctions on the left can always be decomposed.
    let h14 := h12.left
    let h15 := h12.right
    -- Disjunctions on the left can always be decomposed.
    cases h13
    case inl h16 =>
      -- Conjunctions on the left can always be decomposed.
      let h17 := h9.left
      let h18 := h9.right
      -- Disjunctions on the left can always be decomposed.
      cases h3
      case inl h19 =>
        -- We want to use the implication h15 based on <expert-advice>. So we show its premise.
        have h20 : p1 := by
          -- One of the premise coincides with the conclusion.
          exact h14
        -- We have shown the premise of h15, we can now drive its conclusion.
        let h21 := h15 h20
        -- False on the left can always be used.
        apply False.elim h21
      case inr h22 =>
        -- We want to use the implication h15 based on <expert-advice>. So we show its premise.
        have h23 : p1 := by
          -- One of the premise coincides with the conclusion.
          exact h14
        -- We have shown the premise of h15, we can now drive its conclusion.
        let h24 := h15 h23
        -- False on the left can always be used.
        apply False.elim h24
    case inr h25 =>
      -- Conjunctions on the left can always be decomposed.
      let h26 := h9.left
      let h27 := h9.right
      -- Disjunctions on the left can always be decomposed.
      cases h3
      case inl h28 =>
        -- We want to use the implication h15 based on <expert-advice>. So we show its premise.
        have h29 : p1 := by
          -- One of the premise coincides with the conclusion.
          exact h25
        -- We have shown the premise of h15, we can now drive its conclusion.
        let h30 := h15 h29
        -- False on the left can always be used.
        apply False.elim h30
      case inr h31 =>
        -- We want to use the implication h15 based on <expert-advice>. So we show its premise.
        have h32 : p1 := by
          -- One of the premise coincides with the conclusion.
          exact h25
        -- We have shown the premise of h15, we can now drive its conclusion.
        let h33 := h15 h32
        -- False on the left can always be used.
        apply False.elim h33



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_216875950825840197915528928413 : (((p1 ∨ (p3 ∨ p1)) ∧ p2) → ((((p4 ∨ p1) ∧ (False ∧ p2)) ∨ (p3 ∨ ((p3 → p1) ∨ False))) ∧ (((p2 ∨ p3) → p2) ∨ (p4 → p3)))) := by
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
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Implications on the right can always be decomposed.
    intro h5
    -- One of the premise coincides with the conclusion.
    exact h4
  case inr h6 =>
    -- Disjunctions on the left can always be decomposed.
    cases h6
    case inl h7 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- One of the premise coincides with the conclusion.
      exact h7
    case inr h8 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- Implications on the right can always be decomposed.
      intro h9
      -- One of the premise coincides with the conclusion.
      exact h8
  -- Conjunctions on the left can always be decomposed.
  let h10 := h1.left
  let h11 := h1.right
  -- Disjunctions on the left can always be decomposed.
  cases h10
  case inl h12 =>
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Implications on the right can always be decomposed.
    intro h13
    -- Disjunctions on the left can always be decomposed.
    cases h13
    case inl h14 =>
      -- One of the premise coincides with the conclusion.
      exact h14
    case inr h15 =>
      -- One of the premise coincides with the conclusion.
      exact h11
  case inr h16 =>
    -- Disjunctions on the left can always be decomposed.
    cases h16
    case inl h17 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Implications on the right can always be decomposed.
      intro h18
      -- One of the premise coincides with the conclusion.
      exact h17
    case inr h19 =>
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- Implications on the right can always be decomposed.
      intro h20
      -- Disjunctions on the left can always be decomposed.
      cases h20
      case inl h21 =>
        -- One of the premise coincides with the conclusion.
        exact h21
      case inr h22 =>
        -- One of the premise coincides with the conclusion.
        exact h11



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_792877066490990937955709515613 : (((True → (((p4 ∨ p5) → False) → (((p1 → p1) → (p3 ∧ (p5 ∧ True))) → (((p3 → p2) ∨ p1) → ((True ∨ p1) ∧ (p3 ∧ p4)))))) ∨ False) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
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
  -- Disjunctions on the left can always be decomposed.
  cases h4
  case inl h5 =>
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- True on the right can always be proven directly.
    apply True.intro
  case inr h6 =>
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- True on the right can always be proven directly.
    apply True.intro
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Disjunctions on the left can always be decomposed.
  cases h4
  case inl h7 =>
    -- We want to use the implication h3 based on <expert-advice>. So we show its premise.
    have h8 : (p1 → p1) := by
      -- Implications on the right can always be decomposed.
      intro h9
      -- One of the premise coincides with the conclusion.
      exact h9
    -- We have shown the premise of h3, we can now drive its conclusion.
    let h10 := h3 h8
    -- We need to get the left conjuct of h10 based on <expert-advice>.
    let h11 := h10.left
    -- One of the premise coincides with the conclusion.
    exact h11
  case inr h12 =>
    -- We want to use the implication h3 based on <expert-advice>. So we show its premise.
    have h13 : (p1 → p1) := by
      -- Implications on the right can always be decomposed.
      intro h14
      -- One of the premise coincides with the conclusion.
      exact h14
    -- We have shown the premise of h3, we can now drive its conclusion.
    let h15 := h3 h13
    -- We need to get the left conjuct of h15 based on <expert-advice>.
    let h16 := h15.left
    -- One of the premise coincides with the conclusion.
    exact h16
  -- Disjunctions on the left can always be decomposed.
  cases h4
  case inl h17 =>
    -- We want to use the implication h3 based on <expert-advice>. So we show its premise.
    have h18 : (p1 → p1) := by
      -- Implications on the right can always be decomposed.
      intro h19
      -- One of the premise coincides with the conclusion.
      exact h19
    -- We have shown the premise of h3, we can now drive its conclusion.
    let h20 := h3 h18
    -- We need to get the right conjuct of h20 based on <expert-advice>.
    let h21 := h20.right
    -- We need to get the left conjuct of h21 based on <expert-advice>.
    let h22 := h21.left
    -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
    have h23 : (p4 ∨ p5) := by
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- One of the premise coincides with the conclusion.
      exact h22
    -- We have shown the premise of h2, we can now drive its conclusion.
    let h24 := h2 h23
    -- False on the left can always be used.
    apply False.elim h24
  case inr h25 =>
    -- We want to use the implication h3 based on <expert-advice>. So we show its premise.
    have h26 : (p1 → p1) := by
      -- Implications on the right can always be decomposed.
      intro h27
      -- One of the premise coincides with the conclusion.
      exact h27
    -- We have shown the premise of h3, we can now drive its conclusion.
    let h28 := h3 h26
    -- We need to get the right conjuct of h28 based on <expert-advice>.
    let h29 := h28.right
    -- We need to get the left conjuct of h29 based on <expert-advice>.
    let h30 := h29.left
    -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
    have h31 : (p4 ∨ p5) := by
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- One of the premise coincides with the conclusion.
      exact h30
    -- We have shown the premise of h2, we can now drive its conclusion.
    let h32 := h2 h31
    -- False on the left can always be used.
    apply False.elim h32
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_391384869956026979880075850867 : (((((p1 ∧ (p1 ∧ ((p4 ∧ True) ∨ True))) → ((p3 ∨ (((p2 ∧ ((p1 → p2) ∨ (p3 → p1))) → (p4 ∨ True)) → False)) ∨ p1)) ∨ p2) ∧ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
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
  let h4 := h3.left
  let h5 := h3.right
  -- Disjunctions on the left can always be decomposed.
  cases h5
  case inl h6 =>
    -- Conjunctions on the left can always be decomposed.
    let h7 := h6.left
    let h8 := h6.right
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h4
  case inr h9 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h4
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_381964286339587102902827951581 : (((((((p4 ∧ ((True ∨ ((p3 ∧ True) → (True → p4))) ∨ p2)) → ((((p5 ∨ (p3 → p4)) ∨ p2) ∨ False) ∨ p5)) → p4) ∨ False) ∨ True) ∧ True) ∧ True) := by
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
theorem thm_5_vars_225325844561126445047369656282 : (((p1 ∨ True) ∧ False) ∨ (((p5 → p5) → (((p2 ∨ (p2 ∧ (p2 ∧ p1))) → p5) ∨ ((True ∧ p5) ∧ (p4 ∨ (p5 ∧ (p1 ∨ True)))))) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_327866242179731423134355290481 : (True → (((p4 → p1) ∧ (((False → p4) ∨ ((((p4 → (p4 ∨ p3)) → p2) → False) → ((p1 ∧ p5) → (False ∧ p3)))) → p1)) ∨ (True ∨ p5))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



