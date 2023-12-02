variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_262414759467695332997130526209 : (True ∧ ((False ∧ (p2 → (True ∧ ((p3 ∧ ((p1 → (p1 ∨ p1)) → p4)) ∨ (p5 → (((p1 ∨ (p2 ∨ p3)) → p2) → (p5 ∧ p4))))))) ∨ True)) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_57947928136402839138128534412 : (((p1 → (p4 ∧ p1)) → (p5 ∨ (((p5 ∧ p5) → (p3 ∧ (p2 ∧ ((p5 ∧ ((False ∧ p3) ∨ p3)) ∧ p3)))) ∨ ((p5 ∧ p3) ∨ True)))) ∨ p3) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
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
theorem thm_5_vars_85185403791937654765296819454 : ((((p3 ∨ (False ∧ (p1 ∨ p3))) → (p1 ∨ (True ∨ ((p2 ∧ p4) ∨ p5)))) → ((p3 → p4) ∧ ((p3 ∨ p5) ∧ ((p2 ∨ True) → False)))) → False) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h2 : ((p3 ∨ (False ∧ (p1 ∨ p3))) → (p1 ∨ (True ∨ ((p2 ∧ p4) ∨ p5)))) := by
    -- Implications on the right can always be decomposed.
    intro h3
    -- Disjunctions on the left can always be decomposed.
    cases h3
    case inl h4 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- True on the right can always be proven directly.
      apply True.intro
    case inr h5 =>
      -- Conjunctions on the left can always be decomposed.
      let h6 := h5.left
      let h7 := h5.right
      -- False on the left can always be used.
      apply False.elim h6
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h8 := h1 h2
  -- We need to get the right conjuct of h8 based on <expert-advice>.
  let h9 := h8.right
  -- We need to get the right conjuct of h9 based on <expert-advice>.
  let h10 := h9.right
  -- We want to use the implication h10 based on <expert-advice>. So we show its premise.
  have h11 : (p2 ∨ True) := by
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h10, we can now drive its conclusion.
  let h12 := h10 h11
  -- False on the left can always be used.
  apply False.elim h12



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_303864234920791077499759820633 : (p1 ∨ ((((((p1 → True) ∨ (p3 ∧ (((p3 ∨ p1) ∧ p1) ∨ True))) → p3) ∨ (p3 ∨ ((True → False) ∨ p2))) ∨ (p4 → (p1 → p1))) ∨ p3)) := by
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
  -- One of the premise coincides with the conclusion.
  exact h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_148895581393732704286126999042 : (((p2 ∧ ((False ∨ p2) ∨ p4)) ∨ (p1 → (p4 → ((False ∧ ((False ∧ ((False ∧ True) ∨ p3)) → p3)) ∨ p1)))) ∨ ((False ∨ (p2 ∧ False)) → p1)) := by
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
    -- False on the left can always be used.
    apply False.elim h5



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_299191500744193685816552623861 : (False ∨ (((p5 ∧ ((p2 ∧ ((True ∧ p5) → (p2 ∧ (p4 ∨ ((((False ∧ (p2 ∨ p1)) → p1) ∧ True) ∨ p2))))) ∨ (False → p3))) → p4) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_40640696928442432456477917620 : ((((((p3 ∧ p2) ∧ (p1 ∨ (p3 ∧ (p1 → ((False → ((p1 ∧ (p4 ∨ (True → (p1 ∧ p2)))) ∨ p2)) → p2))))) → p3) → p1) ∨ p4) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_654363262134329191432504278861 : ((((((((p5 ∨ p5) ∨ ((p5 ∨ (False ∧ p3)) ∧ True)) ∨ False) ∨ (((False ∨ p1) ∧ (True → (p1 → p2))) → p2)) ∨ False) ∨ (p3 → p4)) ∨ p2) ∧ True) := by
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
    -- We want to use the implication h3 based on <expert-advice>. So we show its premise.
    have h6 : True := by
      -- True on the right can always be proven directly.
      apply True.intro
    -- We have shown the premise of h3, we can now drive its conclusion.
    let h7 := h3 h6
    -- We want to use the implication h7 based on <expert-advice>. So we show its premise.
    have h8 : p1 := by
      -- One of the premise coincides with the conclusion.
      exact h5
    -- We have shown the premise of h7, we can now drive its conclusion.
    let h9 := h7 h8
    -- One of the premise coincides with the conclusion.
    exact h9
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_78501834187148600657459037276 : (((((p4 ∧ ((p5 ∨ p4) ∨ (((p2 ∧ False) → ((False ∧ (p2 ∧ (p4 ∨ p1))) ∨ False)) ∧ (p3 ∨ p1)))) ∨ True) → False) ∧ (p3 → p1)) → p2) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
  have h4 : ((p4 ∧ ((p5 ∨ p4) ∨ (((p2 ∧ False) → ((False ∧ (p2 ∧ (p4 ∨ p1))) ∨ False)) ∧ (p3 ∨ p1)))) ∨ True) := by
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h2, we can now drive its conclusion.
  let h5 := h2 h4
  -- False on the left can always be used.
  apply False.elim h5



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_117117967275189492988000870994 : (((p3 → p3) → (p5 ∨ ((p2 ∧ True) ∧ (((p3 ∧ p5) ∧ (p3 ∨ p4)) → ((((p4 ∧ p5) ∨ p1) → (False ∨ False)) ∧ p5))))) ∨ (True ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_172594136558948937167854740477 : ((((True → p4) → True) → (((True ∧ p3) ∨ p2) ∨ (p4 ∨ (p3 ∧ (p3 → p4))))) ∨ (((p3 → p2) ∨ False) ∨ (False → (p4 ∨ (p2 ∨ p3))))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_177504442209703703796765423272 : ((p1 → (p5 ∨ (True ∧ (p5 ∨ (True ∨ ((p4 → (p2 ∧ p4)) ∧ p2)))))) ∧ (((p1 ∨ (p2 ∧ (p5 ∨ p3))) ∨ ((p3 ∨ False) → p3)) ∨ p2)) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
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
theorem thm_5_vars_152445409449569402404906122091 : ((((False → p5) → p3) ∧ (((p2 → (p1 ∨ ((p2 → p1) → p1))) ∨ (p5 ∧ (p4 ∧ (False ∨ p3)))) ∧ p1)) → (((p4 ∧ p2) ∧ False) ∨ True)) := by
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
    -- Conjunctions on the left can always be decomposed.
    let h10 := h9.left
    let h11 := h9.right
    -- Disjunctions on the left can always be decomposed.
    cases h11
    case inl h12 =>
      -- False on the left can always be used.
      apply False.elim h12
    case inr h13 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- True on the right can always be proven directly.
      apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_381997751627401910616183062922 : (((((((False → p4) ∨ ((p4 ∧ (p5 ∧ (p2 → (((p5 → False) ∨ (True ∨ True)) → True)))) ∨ (False → (p2 → p5)))) → p4) ∨ True) ∨ False) ∧ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
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
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_64015032723526263190679838895 : ((False ∨ ((((True ∧ p1) → (((p2 ∨ p4) ∨ (p4 ∨ False)) ∨ (False ∨ p1))) ∨ ((True → p4) → (p1 ∨ (p2 ∨ p5)))) ∨ (p1 ∨ p4))) ∨ False) := by
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
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h3



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_192341465016406456110671251554 : (((p3 ∨ (False ∧ ((False → (True → p1)) ∨ p4))) ∧ p2) → (((p5 ∨ ((False ∨ p1) ∨ (False ∧ (False ∨ p2)))) ∨ (False ∨ True)) ∨ (p4 ∨ p4))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- Disjunctions on the left can always be decomposed.
  cases h2
  case inl h4 =>
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro
  case inr h5 =>
    -- Conjunctions on the left can always be decomposed.
    let h6 := h5.left
    let h7 := h5.right
    -- False on the left can always be used.
    apply False.elim h6



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_725739487085622024332497961732 : (((((p1 ∨ p5) ∧ p2) ∨ (((((((p5 ∨ (False → p2)) ∧ p5) ∨ p5) → (p3 ∧ (p1 ∧ p4))) → p5) ∨ ((p1 ∨ p5) → p4)) → p4)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_147132392282081865303787656360 : ((((p1 → False) → (((((True ∧ (((p3 ∨ p2) → p1) ∧ False)) ∧ p3) ∨ (False ∨ True)) → False) → p5)) ∧ True) ∨ ((p2 ∨ (p3 → p1)) → True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_234825326993387461820084267719 : ((p5 → (p1 ∨ p2)) → ((p5 → p2) ∨ ((((p5 ∨ (p2 ∧ False)) ∧ p4) → p1) ∨ (p1 ∨ (False → ((((p5 → True) → p4) ∨ p2) ∨ p4)))))) := by
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
  -- False on the left can always be used.
  apply False.elim h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_258601381093242922963845607532 : ((p5 ∨ p4) → (((p4 ∨ ((p5 ∧ True) ∧ p3)) ∨ ((p1 ∨ (((p2 ∨ p1) ∨ p1) ∨ p5)) → p4)) ∨ (p2 → ((p4 ∧ (p4 ∧ p1)) ∨ p2)))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h2 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h3
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h3
  case inr h4 =>
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- One of the premise coincides with the conclusion.
    exact h4



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_44803478307916818891090511836 : (((((p5 ∨ p1) → p2) ∧ (((((p4 ∧ False) ∧ ((p5 ∨ p5) ∨ False)) ∨ ((p4 ∧ p1) → p1)) ∧ True) ∨ (p1 → (p1 ∧ False)))) → p1) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_593587222322350651715106314157 : (((((p1 → ((((p4 ∨ True) ∧ ((p1 → p3) ∧ False)) ∨ (p2 → (p1 → (p5 → (p3 ∧ p1))))) → p5)) → (True ∧ (p2 → False))) ∧ p1) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_41259603145663357070878485996 : ((((((p5 ∧ p2) ∧ p3) ∧ (False ∨ ((((False → (p1 ∨ p4)) ∧ (p2 → False)) ∨ p5) → p3))) ∨ ((False → p3) ∨ (p1 ∧ True))) ∨ p5) ∨ p2) := by
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
theorem thm_5_vars_157653379097168921304416602048 : (((((p1 ∧ (((p4 ∧ p4) ∧ (p2 → (p2 ∧ True))) ∨ False)) ∨ p1) ∨ True) ∨ ((p3 ∨ p3) → p3)) ∨ (p1 ∧ (p2 → ((p3 ∧ p1) → True)))) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_44408108629044090822782721579 : (((((((((p2 → p3) → True) ∨ p3) → (p1 ∨ p2)) ∧ p5) → (p5 ∨ False)) → (p5 → (p1 ∧ (p3 ∧ ((p2 ∧ p1) ∧ p4))))) → False) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_179948414193184189864853314864 : ((((((((p3 → p3) ∨ p1) → p4) ∨ p2) → p5) ∨ (p5 → p5)) ∨ p5) → ((p5 ∧ p3) ∨ ((p4 → (((False ∨ False) ∨ p1) ∨ p3)) → True))) := by
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
      -- True on the right can always be proven directly.
      apply True.intro
    case inr h5 =>
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
theorem thm_5_vars_303360414731942292184968134683 : (p1 ∨ ((((True ∧ (((((((True ∨ p2) ∧ (False ∧ (p5 → p2))) ∨ False) ∨ p4) ∨ (True → p1)) → (p4 → False)) ∧ p4)) ∧ p4) → p2) ∧ True)) := by
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
  let h4 := h2.left
  let h5 := h2.right
  -- Conjunctions on the left can always be decomposed.
  let h6 := h5.left
  let h7 := h5.right
  -- We want to use the implication h6 based on <expert-advice>. So we show its premise.
  have h8 : (((((True ∨ p2) ∧ (False ∧ (p5 → p2))) ∨ False) ∨ p4) ∨ (True → p1)) := by
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h3
  -- We have shown the premise of h6, we can now drive its conclusion.
  let h9 := h6 h8
  -- We want to use the implication h9 based on <expert-advice>. So we show its premise.
  have h10 : p4 := by
    -- One of the premise coincides with the conclusion.
    exact h3
  -- We have shown the premise of h9, we can now drive its conclusion.
  let h11 := h9 h10
  -- False on the left can always be used.
  apply False.elim h11
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_42964344772927420144966673741 : (((p5 → (((p5 ∨ p5) → (((p4 ∨ (p4 ∨ (p1 ∧ p2))) ∨ (p5 ∨ (((p3 ∨ (p5 → False)) ∨ p2) → p1))) ∨ p5)) ∨ p3)) ∨ p5) ∨ p3) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h2
  -- Disjunctions on the left can always be decomposed.
  cases h2
  case inl h3 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h3
  case inr h4 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h4



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_42350400696230433883083399942 : (((p3 ∧ ((True → (p5 ∨ (p4 ∨ (p2 ∨ p3)))) → (((p5 ∨ ((p4 ∧ False) ∨ p4)) → p1) → (((p4 ∨ False) → False) → p1)))) ∨ True) ∨ p3) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_165719575138607530385003883565 : (((False ∧ ((p4 ∧ True) ∨ p2)) ∧ (p3 ∧ (((p2 ∨ p4) ∨ (p4 ∧ p5)) → (True → p3)))) ∨ ((p3 → ((True ∨ p1) → False)) → (p4 → p4))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- One of the premise coincides with the conclusion.
  exact h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_301011008421875081800923877692 : (False ∨ ((p5 → (((False → p5) ∧ (((p3 → p4) ∧ p2) ∧ p2)) ∧ p2)) → ((p2 ∨ True) ∨ (((p5 ∨ p4) ∧ (p1 ∧ (p4 ∨ True))) ∧ p1)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_136934154044857805300699733084 : (((p3 → p2) ∨ (((p2 ∧ (((False ∨ p5) → (p4 ∨ (True → p1))) ∨ (p5 ∧ p5))) → (True ∧ (p3 ∧ False))) ∨ True)) ∨ (p3 ∨ (True ∨ False))) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_48339121394346588265950763931 : (((p2 ∨ ((p3 ∧ p1) ∨ ((p1 ∨ ((p2 ∨ p5) ∨ p2)) → ((False → (True ∨ p5)) ∨ (((p1 ∧ True) ∨ p5) → p5))))) → (p3 ∨ p1)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_587467285769315908353237806994 : (((((((False → (((p1 → ((True ∨ p4) ∧ False)) ∧ (p1 ∧ p2)) → (p4 ∧ (p5 → p3)))) → ((False ∨ True) → p1)) ∨ True) ∨ p2) ∧ False) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_457284624239078071091684050568 : ((((((((p1 → (False ∨ p3)) ∨ (p5 → p3)) ∨ False) → ((p5 ∨ p2) ∨ (p4 ∧ False))) ∨ p4) ∨ (((p1 → p3) → (False ∨ p4)) → True)) ∧ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
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
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_191763653152592491422865189873 : ((p1 ∨ (((p4 → (p5 ∨ p1)) ∨ (p1 ∧ p5)) ∨ True)) ∨ (((True ∧ p5) ∧ (((p3 ∨ p4) ∧ (p2 → p4)) ∨ p4)) ∧ ((p4 → True) → p4))) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_69159469159144789147141986961 : ((p5 → (((True ∧ p1) → ((((p5 ∨ (p1 ∧ (False ∨ (p4 ∨ p4)))) ∨ (p5 ∨ True)) → p3) → p4)) ∨ (((p2 → p1) ∧ False) → p4))) ∨ p1) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h2
  -- Conjunctions on the left can always be decomposed.
  let h3 := h2.left
  let h4 := h2.right
  -- False on the left can always be used.
  apply False.elim h4



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_342777764374889037134203247754 : (p2 → ((((p1 → (p2 ∧ (p4 ∨ p1))) ∧ p4) ∨ p1) → (False ∨ ((((p4 ∨ ((p4 ∨ p1) → p5)) ∧ True) ∧ p1) ∨ ((p4 ∨ p1) ∨ True))))) := by
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
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro
  case inr h6 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_678147803276592804402501000089 : (((((p2 ∧ ((p4 ∨ ((p4 ∧ p3) ∧ True)) ∧ (p4 ∨ (True → p5)))) ∨ (True → (p4 ∨ (p4 → p5)))) ∨ (False → ((p3 ∨ p2) ∧ p3))) ∨ p3) ∧ True) := by
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
  -- False on the left can always be used.
  apply False.elim h1
  -- False on the left can always be used.
  apply False.elim h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_700496401469434034029130775965 : ((((p3 ∨ (((((p4 → p4) → False) ∧ True) ∧ True) ∧ (p4 → p5))) → (((True ∧ ((False → p1) ∧ ((p2 ∨ p4) ∧ False))) ∧ True) ∧ p2)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_729197791922052949522517040879 : (((((p3 → p1) ∧ p4) → ((p1 ∨ p3) ∨ ((p3 ∧ ((((p4 → ((False → p3) ∧ False)) ∨ False) ∧ p5) → False)) ∨ (p1 ∨ (p4 → p4))))) ∨ p1) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
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
  -- One of the premise coincides with the conclusion.
  exact h4
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_161615403123116099552347213344 : ((False ∨ (((False → (p3 ∨ (False ∨ (p4 ∧ ((p4 ∨ p3) ∨ p3))))) → p5) → (p2 ∧ (p2 ∧ p2)))) → (p5 → (p5 ∧ (p2 → (True → p5))))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h3 =>
    -- False on the left can always be used.
    apply False.elim h3
  case inr h4 =>
    -- One of the premise coincides with the conclusion.
    exact h2
  -- Implications on the right can always be decomposed.
  intro h5
  -- Implications on the right can always be decomposed.
  intro h6
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h7 =>
    -- False on the left can always be used.
    apply False.elim h7
  case inr h8 =>
    -- One of the premise coincides with the conclusion.
    exact h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_594957488339656059888304877290 : (((((((False ∧ p3) → ((((True ∧ p4) → p2) ∧ p2) ∧ (p5 ∨ p5))) ∧ p4) ∨ (p3 ∨ ((p3 → p1) → (True ∧ (False ∧ False))))) ∧ p3) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_251841535982691122944199776171 : ((p3 → p5) ∨ ((((p5 → p4) → ((p2 ∨ p1) ∧ ((p5 ∧ p1) ∧ ((p5 ∨ p2) → p1)))) ∧ (p2 → (((p3 ∨ False) ∨ False) → p4))) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_715024238156677984634657592573 : ((((p1 ∨ (p4 ∧ ((True → p3) → p2))) → (((((True → p3) → (p5 ∧ p5)) ∨ p5) ∨ (False ∨ (p5 → (True ∧ p1)))) ∨ (True ∧ p4))) ∨ p2) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h2 =>
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h3
    -- Conjunctions on the right can always be decomposed.
    apply And.intro
    -- True on the right can always be proven directly.
    apply True.intro
    -- One of the premise coincides with the conclusion.
    exact h2
  case inr h4 =>
    -- Conjunctions on the left can always be decomposed.
    let h5 := h4.left
    let h6 := h4.right
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Conjunctions on the right can always be decomposed.
    apply And.intro
    -- True on the right can always be proven directly.
    apply True.intro
    -- One of the premise coincides with the conclusion.
    exact h5
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_308336830946567869168996046662 : (p2 ∨ (((((False → (p1 → True)) ∨ (False → (((p3 ∨ (p4 ∧ (p2 → (False ∧ False)))) ∨ False) ∧ (p1 ∨ (p4 → False))))) → p5) ∧ False) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_307787632307652666070314131964 : (p1 ∨ (p4 → (((((True ∧ p3) ∧ False) ∨ (p2 ∧ ((False → (((p3 ∧ (p4 ∧ (p2 → p3))) → p1) ∨ (True ∧ p5))) ∨ False))) → False) ∨ True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_300695092677855340998233202555 : (False ∨ ((p5 ∨ ((True → p2) ∧ ((False ∨ (p5 ∧ (True ∨ (p1 ∨ p3)))) ∧ ((p3 → p1) ∧ p4)))) ∨ ((p5 ∧ p4) ∨ ((False → p3) ∨ p3)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
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
theorem thm_5_vars_255806019237577600156039354326 : ((True ∨ False) → ((((((p1 → p2) ∧ ((True → p4) → p4)) → p5) ∨ p2) ∧ (p5 → (p2 ∧ (p5 ∨ p3)))) ∨ ((p1 ∧ p2) ∨ (p2 → p2)))) := by
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
    -- One of the premise coincides with the conclusion.
    exact h3
  case inr h4 =>
    -- False on the left can always be used.
    apply False.elim h4



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_42645445400395653666039001610 : (((p4 ∨ (((p5 ∨ (p3 ∧ p5)) ∨ (((p5 ∨ ((((p3 ∧ p5) → False) → ((p2 ∨ False) → False)) ∧ p3)) ∨ p2) → True)) ∧ p2)) ∨ p2) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_430067049575496022387170268061 : ((((((p3 ∨ p5) ∧ ((p2 ∧ (p4 ∨ p3)) ∧ False)) ∨ (p1 → (((p4 ∨ True) ∧ p1) → (((p5 ∨ True) ∨ p5) ∨ p3)))) ∨ (p3 → p3)) ∧ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
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
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_622202991327790033597976531355 : ((((p2 ∧ (p4 ∧ ((p2 → (p1 ∧ (((p4 ∨ True) ∨ (False ∨ (p2 ∨ p1))) → ((p1 ∨ ((False → p2) → p1)) ∨ p1)))) ∧ p3))) ∨ True) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_590936516961848938336461782392 : (((((False → (p2 ∧ (((True ∧ False) → p4) ∧ ((p1 ∧ p5) ∧ ((p4 ∨ (((p1 ∨ p2) → (p5 ∧ p5)) ∧ p3)) ∧ p2))))) → False) ∧ False) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_240850663296092361890436077138 : ((True → True) ∧ (((p4 ∨ p3) ∧ (p4 ∧ ((((True ∨ (True ∨ False)) ∧ (True ∨ ((((p4 ∨ p5) ∨ True) → True) ∧ p1))) → p4) ∧ p2))) ∨ True)) := by
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



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_56996701993522608385164135361 : (((p5 ∨ (p4 → p5)) ∧ ((p1 ∧ p1) ∧ ((p4 ∧ ((p5 ∨ p5) ∨ p1)) ∧ ((False ∨ ((p4 ∧ p1) ∧ (p2 ∧ p5))) → (p5 → False))))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_117218042998780177055462843352 : ((True ∧ (((p1 → p4) → p3) → (((((p1 ∨ p3) → (True ∨ p2)) → p1) ∨ (True → (((False ∧ p1) ∨ p3) → False))) ∧ False))) ∨ (p5 → p5)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_734204387031792218307071099150 : ((((False ∨ True) ∧ (p5 ∨ (((p5 ∧ (True ∨ (p4 ∨ (p3 ∨ p3)))) ∧ ((((p2 → (p4 ∨ p1)) ∧ p5) → p2) ∨ (p4 ∨ True))) → False))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_753327791210699933970796162626 : (((False ∧ (((True → (False → p1)) ∨ (p3 ∨ ((p3 → (True ∨ ((p5 ∨ p3) → ((p2 → p2) ∨ p5)))) ∨ (False → False)))) → (False ∨ True))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_218997882082904659547296328123 : ((p4 ∧ (True ∨ (p2 ∨ p1))) → ((p3 ∨ (p4 → p2)) ∨ (((True ∨ p5) ∨ False) ∨ ((False ∧ ((True ∧ True) ∨ p2)) ∨ ((True → p1) ∧ p5))))) := by
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
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- True on the right can always be proven directly.
    apply True.intro
  case inr h5 =>
    -- Disjunctions on the left can always be decomposed.
    cases h5
    case inl h6 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- True on the right can always be proven directly.
      apply True.intro
    case inr h7 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- True on the right can always be proven directly.
      apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_791255986105530125123892605146 : (((True → ((p5 → (((((p2 → p5) → True) ∧ (p4 ∨ ((p2 ∧ False) → p1))) ∧ (p1 → (((False ∨ p3) ∨ p5) → p2))) ∧ p4)) ∧ p3)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_349224899601018826195491441870 : (p3 → (p1 → ((((((True ∨ (p1 → ((p4 ∧ True) ∧ p2))) → p2) → ((p5 → False) → True)) → False) ∧ ((p5 ∧ p5) ∨ p3)) ∨ (p3 ∧ p3)))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- One of the premise coincides with the conclusion.
  exact h1
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_808054169775353978696804066006 : (((p4 → (False ∧ ((p4 ∧ ((p5 → ((p1 → False) ∧ p2)) ∨ ((p2 ∧ (((p5 ∧ (True ∨ (p3 ∨ p4))) ∧ p5) → p3)) ∧ p3))) ∧ False))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_615769611821208059564879796868 : (((((p2 → ((p2 ∧ ((p4 ∧ p2) ∧ False)) ∧ ((True → False) ∨ (p4 → p1)))) ∧ (((False ∨ False) → p3) ∧ ((p5 ∨ p1) ∧ p5))) ∨ p5) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_51992374044923882791939680550 : ((((p3 ∨ p4) → ((((p2 → p4) → p5) → p2) ∨ ((False ∨ p2) ∨ (p3 ∨ p1)))) ∨ (p1 → (((p4 → (p5 ∨ p5)) ∧ p5) ∧ p4))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_638445554748777261079927688453 : (((((p5 → (p1 ∨ (False ∨ (p3 ∨ p5)))) ∧ (((p2 → p3) ∨ ((p1 ∧ (False → (False → (p3 ∧ p1)))) ∨ p2)) ∧ (p1 → True))) → p2) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_303868712211099977109354798878 : (p1 ∨ (((((p5 ∨ (p4 ∧ p3)) ∧ (p4 → ((True ∨ True) ∧ (((True ∨ (p1 ∨ p1)) ∧ p1) ∨ False)))) ∨ p1) → ((p5 ∨ p5) ∧ p5)) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_167055832998964718691717418938 : (((((False ∨ ((p1 ∨ (p1 ∨ p4)) ∧ p1)) → ((p5 ∧ False) ∨ (p3 → True))) ∨ p3) ∨ p3) → ((p1 ∧ p2) → ((p1 → False) → (False ∧ p3)))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Implications on the right can always be decomposed.
  intro h3
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Conjunctions on the left can always be decomposed.
  let h4 := h2.left
  let h5 := h2.right
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h6 =>
    -- Disjunctions on the left can always be decomposed.
    cases h6
    case inl h7 =>
      -- We want to use the implication h3 based on <expert-advice>. So we show its premise.
      have h8 : p1 := by
        -- One of the premise coincides with the conclusion.
        exact h4
      -- We have shown the premise of h3, we can now drive its conclusion.
      let h9 := h3 h8
      -- False on the left can always be used.
      apply False.elim h9
    case inr h10 =>
      -- We want to use the implication h3 based on <expert-advice>. So we show its premise.
      have h11 : p1 := by
        -- One of the premise coincides with the conclusion.
        exact h4
      -- We have shown the premise of h3, we can now drive its conclusion.
      let h12 := h3 h11
      -- False on the left can always be used.
      apply False.elim h12
  case inr h13 =>
    -- We want to use the implication h3 based on <expert-advice>. So we show its premise.
    have h14 : p1 := by
      -- One of the premise coincides with the conclusion.
      exact h4
    -- We have shown the premise of h3, we can now drive its conclusion.
    let h15 := h3 h14
    -- False on the left can always be used.
    apply False.elim h15
  -- Conjunctions on the left can always be decomposed.
  let h16 := h2.left
  let h17 := h2.right
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h18 =>
    -- Disjunctions on the left can always be decomposed.
    cases h18
    case inl h19 =>
      -- We want to use the implication h3 based on <expert-advice>. So we show its premise.
      have h20 : p1 := by
        -- One of the premise coincides with the conclusion.
        exact h16
      -- We have shown the premise of h3, we can now drive its conclusion.
      let h21 := h3 h20
      -- False on the left can always be used.
      apply False.elim h21
    case inr h22 =>
      -- One of the premise coincides with the conclusion.
      exact h22
  case inr h23 =>
    -- One of the premise coincides with the conclusion.
    exact h23



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_226277308166308169541890356846 : (((p4 ∨ False) ∨ p1) ∨ (((False → True) ∨ p2) ∧ (p3 ∨ ((p5 ∧ p1) → ((p3 ∨ (p3 ∧ False)) ∨ ((((p4 ∨ True) ∧ p5) ∧ True) → True)))))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h2
  -- Conjunctions on the left can always be decomposed.
  let h3 := h2.left
  let h4 := h2.right
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h5
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_694712681840050013244549165084 : ((((p2 ∨ ((p3 → False) → (p5 ∨ ((p2 → (p2 → (False ∧ True))) → p4)))) ∨ ((p2 ∨ p4) ∨ (False ∨ ((p3 ∧ p4) ∨ (p3 → True))))) ∨ p4) ∧ True) := by
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
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_610773350403714698233314989750 : ((((((p5 → ((p5 ∧ (((p2 → ((p3 → False) ∧ p2)) ∨ (p2 ∧ p1)) → p1)) ∨ True)) ∧ (False → (p5 ∨ (False ∧ p4)))) → p4) ∨ True) ∨ p4) ∧ True) := by
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
theorem thm_5_vars_791467272782535473224751170422 : (((True → ((p1 ∧ ((p5 → ((p5 → p2) ∧ (p5 → False))) → ((p2 ∧ False) ∨ (p1 ∨ (False ∨ (p4 ∨ (True ∨ (False → p1)))))))) ∨ p5)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_623578036907931900615381518342 : ((((False ∨ (p3 ∧ ((p5 ∨ ((((True → p5) → p5) ∧ ((p4 ∨ (False ∨ p1)) ∨ p2)) ∧ (p5 ∨ p1))) ∧ ((p1 ∧ True) ∨ p4)))) ∨ True) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_749242964570895519357708258288 : ((((p5 → p3) → (p2 → (True ∧ (True → (((p5 → (((p5 → p4) ∨ False) → (p2 → ((p3 ∧ p1) ∧ False)))) ∧ p5) ∨ (p3 ∨ True)))))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_227618009574606699186588496361 : ((False ∧ (False ∨ p4)) ∨ ((((p5 ∧ False) ∨ p5) ∨ p2) → (((True ∧ ((p4 ∧ p5) ∨ True)) → p5) → ((p5 ∧ ((p4 ∨ p3) ∨ p2)) ∨ True)))) := by
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
      -- Conjunctions on the left can always be decomposed.
      let h5 := h4.left
      let h6 := h4.right
      -- False on the left can always be used.
      apply False.elim h6
    case inr h7 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- True on the right can always be proven directly.
      apply True.intro
  case inr h8 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_102938554950849391830540983745 : (((((((p3 ∨ (((p4 ∧ (p3 → p4)) ∨ p2) ∨ p2)) → (False ∧ p1)) ∨ p1) ∧ p4) ∨ (((False → p2) ∧ p5) ∧ True)) ∨ True) ∧ (True ∨ False)) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_318572541715043439372019537686 : (p4 ∨ (((p5 ∧ ((False ∧ p5) ∨ (((((p4 ∧ p5) → (True ∨ ((p2 ∨ p3) ∧ (False ∨ p5)))) → p3) → p4) ∧ p5))) → p1) ∨ (True ∨ p3))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_612932092924279890693825329835 : (((((True → (((((p2 ∨ (p4 → ((False ∨ p3) ∧ (False ∧ False)))) ∧ (False ∨ True)) ∧ (False → p2)) ∨ p2) → p1)) ∨ (p2 ∧ p4)) ∨ p5) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_65039533220787005472760024556 : ((p2 ∨ (True ∧ ((p1 ∧ ((((p5 ∨ p3) ∧ p3) ∧ True) ∨ (True ∧ (((p5 → True) ∧ ((p3 ∨ (False → p1)) ∧ p4)) ∧ p1)))) → p3))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_53885038016273942379533995987 : ((((False → p2) → ((p3 ∧ p1) → ((True ∧ p3) ∧ False))) ∨ (((p4 ∧ (((p3 → p3) → (p1 ∨ (True ∨ p3))) ∨ p3)) ∨ p1) ∨ True)) ∨ False) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_746388488460383886439168942746 : ((((p2 ∨ p1) → (((((True ∧ (p4 → True)) ∧ p3) ∨ ((p4 → (p5 → p2)) ∨ p3)) ∧ p2) ∧ (p3 ∧ (True ∧ ((p4 ∧ p5) ∧ p5))))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_245790021539085755031841663041 : ((p3 ∧ p3) ∨ ((((p5 → (((True ∨ p2) ∨ p2) ∧ p4)) → (True → False)) ∨ True) ∨ (((p4 → p5) → ((p5 → p3) ∨ p2)) ∨ (p2 → p2)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_218645744291484765684987439765 : ((True ∧ ((p1 ∧ p2) → p3)) → (((True ∨ p5) → ((False ∨ (p4 ∧ (p5 → (False ∧ p2)))) → (p3 ∨ False))) ∨ (((p3 → p4) ∧ p1) → p1))) := by
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
  -- One of the premise coincides with the conclusion.
  exact h6



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_64082102128393480278117846351 : ((False ∨ (((p4 ∧ ((p2 ∨ (((p2 ∧ p3) ∨ (True ∧ p3)) ∨ False)) ∧ p5)) → p5) → ((False ∧ (False ∧ p5)) ∨ (p2 → (p3 → p4))))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_45997217964315709263442986695 : ((((((p3 ∧ (((p3 ∧ ((p4 ∧ p1) → p2)) ∧ (p1 ∧ (p5 ∨ (p1 ∨ p4)))) ∨ False)) ∧ True) ∨ (p3 → False)) ∧ p4) ∧ (p3 → False)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_190937584039411381626503095266 : ((((False ∨ p2) ∧ (False ∧ p1)) ∧ (False ∨ (True ∨ p4))) ∨ ((((p1 → True) → (((p3 ∧ p5) ∨ True) ∨ ((False ∧ p1) → p2))) ∨ p1) ∨ p2)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
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
theorem thm_5_vars_117092066857566340840213678083 : (((p1 → p1) → (((p3 ∨ p3) ∨ ((p1 ∧ (p2 ∧ (p5 → (p4 ∧ p3)))) ∨ False)) ∧ (((p3 → (p4 ∨ p3)) → p4) ∨ p2))) ∨ (True ∨ p3)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_54563679726139734273570222106 : (((p4 ∧ (p5 ∨ (((False ∧ p3) ∧ p4) → p1))) ∨ ((p2 ∧ (((p2 → False) → True) → p3)) ∨ ((((p4 ∨ p2) ∧ p1) ∨ True) ∨ p1))) ∨ p1) := by
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
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_399718478980126487619198964322 : ((((p3 → (((p2 ∨ (p1 → (p3 ∧ (p4 ∨ p1)))) → ((p5 → p3) ∧ p2)) ∧ ((p5 ∨ ((True ∧ p4) → (p1 ∨ p4))) → p1))) ∨ True) ∧ True) ∧ True) := by
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
theorem thm_5_vars_116425976858436677687322302567 : (((p5 ∨ (p4 ∨ p5)) → (False ∧ ((p2 → (p4 ∧ (((((p4 ∨ p5) ∨ p4) → (p1 ∨ True)) ∧ (False ∧ True)) → True))) ∨ True))) ∨ (True ∨ p2)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_60288306502376350839030106407 : (((p1 → True) → (True → ((((p2 ∨ (p4 ∧ False)) ∧ ((p5 → p5) ∧ (p1 ∨ ((True → p3) → p2)))) ∨ p1) ∨ (True ∧ (False → p5))))) ∨ p1) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
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
  -- Implications on the right can always be decomposed.
  intro h3
  -- False on the left can always be used.
  apply False.elim h3



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_83235300627406797987285618956 : ((((((p1 ∧ ((p2 ∧ p1) → (p2 ∨ ((p4 ∨ (p2 → p3)) ∧ p4)))) → p5) ∧ p5) → False) ∧ ((p5 ∧ (p3 ∧ p5)) ∨ (False ∧ p3))) → p1) := by
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
    -- Conjunctions on the left can always be decomposed.
    let h7 := h6.left
    let h8 := h6.right
    -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
    have h9 : (((p1 ∧ ((p2 ∧ p1) → (p2 ∨ ((p4 ∨ (p2 → p3)) ∧ p4)))) → p5) ∧ p5) := by
      -- Conjunctions on the right can always be decomposed.
      apply And.intro
      -- Implications on the right can always be decomposed.
      intro h10
      -- Conjunctions on the left can always be decomposed.
      let h11 := h10.left
      let h12 := h10.right
      -- One of the premise coincides with the conclusion.
      exact h8
      -- One of the premise coincides with the conclusion.
      exact h8
    -- We have shown the premise of h2, we can now drive its conclusion.
    let h13 := h2 h9
    -- False on the left can always be used.
    apply False.elim h13
  case inr h14 =>
    -- Conjunctions on the left can always be decomposed.
    let h15 := h14.left
    let h16 := h14.right
    -- False on the left can always be used.
    apply False.elim h15



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_114055245221983873219128428555 : ((((p2 → ((p5 ∨ ((p4 ∧ (False ∨ ((p5 → False) ∧ p3))) → p4)) ∧ p1)) → ((p4 ∨ p4) → p1)) ∨ ((True ∧ p4) ∧ p3)) ∨ (p3 → p3)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_256593254873680774255487884088 : ((p1 ∨ True) → ((((True ∨ p2) ∨ ((p5 → p4) → (p4 ∧ True))) ∧ ((False ∧ p2) ∨ (p5 → ((False ∨ p5) ∨ True)))) ∨ (p4 → (p4 → p2)))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h2 =>
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Conjunctions on the right can always be decomposed.
    apply And.intro
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- True on the right can always be proven directly.
    apply True.intro
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h3
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro
  case inr h4 =>
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Conjunctions on the right can always be decomposed.
    apply And.intro
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- True on the right can always be proven directly.
    apply True.intro
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h5
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_785181449153394849520582056719 : (((p4 ∨ ((((p4 ∨ p5) ∧ ((p3 ∨ p2) ∧ p2)) ∧ (p2 ∧ ((p3 ∨ p1) ∨ ((p2 ∨ p4) ∧ (p5 → (p2 → (p4 → True))))))) ∧ p2)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_247971833508237711937827627814 : ((p1 ∨ p4) ∨ (((p1 ∧ ((p1 ∨ (((p1 ∨ p4) → p1) ∨ p3)) → ((p4 → p4) ∧ p1))) ∨ (True ∨ p2)) ∨ (p1 ∧ ((True ∨ True) ∧ p4)))) := by
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
theorem thm_5_vars_231410293891104648956569777812 : (((p1 → p3) ∨ False) → ((True ∧ ((((p2 ∧ (p5 ∨ ((p4 ∧ False) ∧ p3))) ∧ p3) ∨ p1) → p1)) ∨ (p1 ∨ (((p5 → p1) ∧ False) → p2)))) := by
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
    -- False on the left can always be used.
    apply False.elim h5
  case inr h6 =>
    -- False on the left can always be used.
    apply False.elim h6



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_337085632400350154221070072761 : (p1 → ((((((((True ∧ (p5 → p5)) ∧ p1) ∧ p2) → (p5 → True)) ∨ p1) → p2) ∧ ((False ∨ ((p1 → p4) → False)) → p1)) ∨ (p4 → p4))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h2
  -- One of the premise coincides with the conclusion.
  exact h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_304747396204330322325118958278 : (p1 ∨ (((p2 ∧ (p1 ∨ p1)) → (((p4 ∧ ((p5 ∨ (((p1 ∨ p3) ∧ p4) → True)) ∧ False)) ∨ p1) → ((p3 ∨ False) ∧ False))) ∨ (True ∧ True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_176796440017278658077370687955 : ((((p5 ∧ True) → p2) → (p2 ∨ ((p2 → False) ∨ (p4 → (p1 ∨ p4))))) ∧ (((((p2 ∧ (p5 ∧ p4)) ∧ False) ∨ p4) → (False → True)) ∨ p3)) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h2
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h2
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h3
  -- Implications on the right can always be decomposed.
  intro h4
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_58803959872717014452121493057 : (((p5 → p1) ∧ (p1 → ((p5 ∨ ((p4 ∨ True) ∧ (((p5 → True) → p4) ∧ (p4 → True)))) → (True → ((p5 ∨ (p2 ∨ p5)) → p4))))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



