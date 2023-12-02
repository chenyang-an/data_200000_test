variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_249406746953495414799012315413 : ((p5 ∨ False) ∨ ((((((p3 ∨ (p5 → ((p5 → p4) ∨ False))) → (True ∨ p3)) → p3) ∨ True) ∨ (((False ∨ p5) → p1) ∨ (p5 ∨ p2))) ∧ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
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
theorem thm_5_vars_327832296187284414821129060576 : (True → (((((((True ∨ p4) ∧ ((p1 ∧ (False ∨ p5)) → p4)) ∧ p5) ∧ (p5 → (False → p2))) → False) ∨ ((p2 ∨ p1) → p3)) ∨ (p2 ∨ True))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_4075144568250194921932856714 : (p2 ∨ (p3 → (((p4 ∧ p4) ∨ ((p5 ∧ (((p2 → False) → (True ∧ p4)) ∨ ((False ∨ p2) → p1))) ∨ (True ∨ p3))) ∨ (False ∧ True)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
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
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_188848751509427970120177742802 : ((((p3 ∧ p3) ∧ (p2 ∧ p5)) ∨ (False → (p5 ∨ False))) ∧ ((((p3 → (p2 ∨ (p3 → (p5 → p5)))) ∨ p1) → (True ∧ (False ∧ p2))) ∨ True)) := by
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



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_655166124829873498120807738798 : (((((p3 → (p5 ∧ ((p3 ∨ ((((p3 ∨ ((False → True) → True)) ∧ p1) ∧ p3) → p2)) ∨ ((p5 → False) ∨ False)))) → p1) ∨ (True ∨ p5)) ∨ p1) ∧ True) := by
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
theorem thm_5_vars_42021593623171897076363924588 : ((((False ∧ p1) ∨ ((p2 ∧ True) ∧ (p2 → (((True ∧ (p5 → (((True → p2) ∨ (p5 ∨ p3)) ∧ (p3 ∨ p1)))) ∧ p2) ∧ p4)))) ∨ False) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_134000621882243641740248182182 : (((((p2 ∧ p5) ∧ (((p2 ∧ ((p2 → True) → (p5 ∨ False))) ∧ (((p2 ∨ p2) ∨ p2) ∧ True)) ∧ True)) ∧ True) ∨ p1) ∨ ((p4 ∨ True) ∨ p4)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_157295946230950382468012697392 : ((((True ∨ p4) → (((((p5 → True) ∨ (True → p2)) ∨ (True ∨ p2)) ∨ (p1 → False)) ∧ False)) → p5) ∨ ((False ∧ False) ∨ ((p2 → p3) ∧ p3))) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h2 : (True ∨ p4) := by
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h3 := h1 h2
  -- We need to get the right conjuct of h3 based on <expert-advice>.
  let h4 := h3.right
  -- False on the left can always be used.
  apply False.elim h4



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_41256832914400280399615514492 : (((((p1 ∨ (p4 ∧ (False → ((p5 → False) ∨ p5)))) ∨ (p2 ∧ (p2 → (p1 → (True → p5))))) ∨ ((True → (p2 ∧ p1)) ∧ True)) ∨ p5) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_258805623721500996479650182296 : ((True → False) → (p5 ∧ (((p2 → p2) → (((((p1 ∨ p1) ∧ p5) ∨ False) → (p4 ∧ p1)) ∨ (p5 → False))) ∨ (p5 → (p2 → (p4 ∧ p4)))))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h2 : True := by
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h3 := h1 h2
  -- False on the left can always be used.
  apply False.elim h3
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h4 : True := by
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h5 := h1 h4
  -- False on the left can always be used.
  apply False.elim h5



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_728037941381037600124892230311 : ((((p4 ∨ (p1 ∧ True)) ∨ ((p4 ∧ p3) → ((p1 ∧ p1) ∨ ((((p3 → True) ∧ True) → (False ∨ p2)) → (True → (p3 → (p5 ∨ p4))))))) ∨ p4) ∧ True) := by
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
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h4
  -- Implications on the right can always be decomposed.
  intro h5
  -- Implications on the right can always be decomposed.
  intro h6
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h2
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_156617607910794891042947122436 : ((((((p4 → (((p3 → p1) → ((p1 ∧ False) ∨ p3)) ∧ p1)) ∨ (p3 ∨ p4)) ∧ p2) ∨ p2) ∧ p3) ∨ ((p3 → p5) → (p5 → (False → False)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Implications on the right can always be decomposed.
  intro h3
  -- False on the left can always be used.
  apply False.elim h3



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_167448121778262133920569127132 : (((p3 ∨ (p2 → ((True → ((p5 → p1) → False)) ∨ ((p5 ∧ (True → p2)) → p2)))) → p5) → (((p1 → p1) ∨ True) → (p4 ∨ (p5 ∨ False)))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Disjunctions on the left can always be decomposed.
  cases h2
  case inl h3 =>
    -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
    have h4 : (p3 ∨ (p2 → ((True → ((p5 → p1) → False)) ∨ ((p5 ∧ (True → p2)) → p2)))) := by
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Implications on the right can always be decomposed.
      intro h5
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Implications on the right can always be decomposed.
      intro h6
      -- Conjunctions on the left can always be decomposed.
      let h7 := h6.left
      let h8 := h6.right
      -- One of the premise coincides with the conclusion.
      exact h5
    -- We have shown the premise of h1, we can now drive its conclusion.
    let h9 := h1 h4
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- One of the premise coincides with the conclusion.
    exact h9
  case inr h10 =>
    -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
    have h11 : (p3 ∨ (p2 → ((True → ((p5 → p1) → False)) ∨ ((p5 ∧ (True → p2)) → p2)))) := by
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Implications on the right can always be decomposed.
      intro h12
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Implications on the right can always be decomposed.
      intro h13
      -- Conjunctions on the left can always be decomposed.
      let h14 := h13.left
      let h15 := h13.right
      -- One of the premise coincides with the conclusion.
      exact h12
    -- We have shown the premise of h1, we can now drive its conclusion.
    let h16 := h1 h11
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- One of the premise coincides with the conclusion.
    exact h16



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_789944482672857923502983549546 : (((p5 ∨ ((p4 ∧ True) ∧ ((((p1 → (False ∧ ((False → p1) → (p2 ∧ (p4 ∧ (True ∧ p1)))))) ∨ p3) ∨ p2) ∧ (True ∧ (p3 ∧ p5))))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_191866529894206304657949522046 : ((p4 ∨ ((p4 → ((p3 → p4) → (p3 ∧ True))) → False)) ∨ ((((False ∧ p2) → p5) → ((True ∧ p1) ∨ (((p5 ∨ True) ∨ False) ∧ p1))) → p1)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h2 : ((False ∧ p2) → p5) := by
    -- Implications on the right can always be decomposed.
    intro h3
    -- Conjunctions on the left can always be decomposed.
    let h4 := h3.left
    let h5 := h3.right
    -- False on the left can always be used.
    apply False.elim h4
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h6 := h1 h2
  -- Disjunctions on the left can always be decomposed.
  cases h6
  case inl h7 =>
    -- Conjunctions on the left can always be decomposed.
    let h8 := h7.left
    let h9 := h7.right
    -- One of the premise coincides with the conclusion.
    exact h9
  case inr h10 =>
    -- Conjunctions on the left can always be decomposed.
    let h11 := h10.left
    let h12 := h10.right
    -- Disjunctions on the left can always be decomposed.
    cases h11
    case inl h13 =>
      -- Disjunctions on the left can always be decomposed.
      cases h13
      case inl h14 =>
        -- One of the premise coincides with the conclusion.
        exact h12
      case inr h15 =>
        -- One of the premise coincides with the conclusion.
        exact h12
    case inr h16 =>
      -- False on the left can always be used.
      apply False.elim h16



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_657712228502681603646999411297 : (((((p3 → p4) → (p4 ∧ ((((((True → False) ∧ True) ∨ (False → False)) ∨ ((p5 ∨ (p2 ∨ p4)) → p4)) ∨ p4) ∨ True))) ∨ (p4 → p3)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_55509205353094702881463864708 : ((((p1 → False) ∧ (p1 → (p1 ∧ p2))) → (((p4 → p4) ∧ (p4 ∧ (p4 → p1))) → (((((p5 ∧ False) → p3) ∨ p2) ∨ p2) → False))) ∨ p5) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
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
    cases h4
    case inl h5 =>
      -- Conjunctions on the left can always be decomposed.
      let h6 := h2.left
      let h7 := h2.right
      -- Conjunctions on the left can always be decomposed.
      let h8 := h7.left
      let h9 := h7.right
      -- Conjunctions on the left can always be decomposed.
      let h10 := h1.left
      let h11 := h1.right
      -- We want to use the implication h9 based on <expert-advice>. So we show its premise.
      have h12 : p4 := by
        -- One of the premise coincides with the conclusion.
        exact h8
      -- We have shown the premise of h9, we can now drive its conclusion.
      let h13 := h9 h12
      -- We want to use the implication h10 based on <expert-advice>. So we show its premise.
      have h14 : p1 := by
        -- One of the premise coincides with the conclusion.
        exact h13
      -- We have shown the premise of h10, we can now drive its conclusion.
      let h15 := h10 h14
      -- False on the left can always be used.
      apply False.elim h15
    case inr h16 =>
      -- Conjunctions on the left can always be decomposed.
      let h17 := h2.left
      let h18 := h2.right
      -- Conjunctions on the left can always be decomposed.
      let h19 := h18.left
      let h20 := h18.right
      -- Conjunctions on the left can always be decomposed.
      let h21 := h1.left
      let h22 := h1.right
      -- We want to use the implication h20 based on <expert-advice>. So we show its premise.
      have h23 : p4 := by
        -- One of the premise coincides with the conclusion.
        exact h19
      -- We have shown the premise of h20, we can now drive its conclusion.
      let h24 := h20 h23
      -- We want to use the implication h21 based on <expert-advice>. So we show its premise.
      have h25 : p1 := by
        -- One of the premise coincides with the conclusion.
        exact h24
      -- We have shown the premise of h21, we can now drive its conclusion.
      let h26 := h21 h25
      -- False on the left can always be used.
      apply False.elim h26
  case inr h27 =>
    -- Conjunctions on the left can always be decomposed.
    let h28 := h2.left
    let h29 := h2.right
    -- Conjunctions on the left can always be decomposed.
    let h30 := h29.left
    let h31 := h29.right
    -- Conjunctions on the left can always be decomposed.
    let h32 := h1.left
    let h33 := h1.right
    -- We want to use the implication h31 based on <expert-advice>. So we show its premise.
    have h34 : p4 := by
      -- One of the premise coincides with the conclusion.
      exact h30
    -- We have shown the premise of h31, we can now drive its conclusion.
    let h35 := h31 h34
    -- We want to use the implication h32 based on <expert-advice>. So we show its premise.
    have h36 : p1 := by
      -- One of the premise coincides with the conclusion.
      exact h35
    -- We have shown the premise of h32, we can now drive its conclusion.
    let h37 := h32 h36
    -- False on the left can always be used.
    apply False.elim h37



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_55962163154693022214922084647 : (((((p5 ∨ p4) ∧ True) ∧ True) ∨ (((p1 ∨ (False ∧ (((p5 ∧ p4) ∧ (p3 ∨ (p4 ∨ False))) → ((p3 ∨ p1) ∨ False)))) ∨ p3) ∧ p2)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_165486451101364371562408947797 : (((((False ∧ p2) → ((False ∧ False) ∨ p5)) → (False ∨ p1)) ∨ (False ∨ ((False ∧ True) → p2))) ∨ (p3 → (p4 ∨ ((p3 → (p1 ∧ p1)) → p2)))) := by
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
theorem thm_5_vars_192318470560753312527910192969 : (((p4 ∧ (((p5 ∧ p4) ∧ (p5 → p3)) → True)) ∧ p5) → (((p1 → True) ∧ ((True → ((p2 ∧ p1) ∧ p2)) ∨ ((False ∧ p4) ∨ p4))) ∨ p3)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- Conjunctions on the left can always be decomposed.
  let h4 := h2.left
  let h5 := h2.right
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h6
  -- True on the right can always be proven directly.
  apply True.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h4



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_260160978508925397381215696994 : ((p2 → p2) → ((((p5 → p2) ∧ ((p2 ∨ True) ∨ (((True → (((True ∨ p3) ∨ p3) ∧ p4)) → (p2 → p2)) ∨ True))) → (p3 ∧ p3)) ∨ True)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_258766573530628072477407551057 : ((True → False) → ((p2 ∧ (p4 → ((((False ∧ p4) ∨ ((((p3 ∧ False) ∨ p4) → (p4 → p1)) → ((p3 ∨ p2) → p1))) → p3) ∧ p1))) ∨ p2)) := by
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
theorem thm_5_vars_134176205343283452440032150493 : (((((p1 → ((False → p5) → p1)) → ((((p3 ∨ p3) → False) ∨ p1) → p2)) → (False ∧ (True ∨ (p5 ∧ p1)))) ∨ p1) ∨ (p3 ∨ (False → p3))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_760985096666033183118052046518 : (((p2 ∧ (True → (p3 ∨ ((p4 ∨ ((((p4 → False) ∨ (True → ((p2 → p1) → False))) ∧ p3) ∨ ((p5 → True) ∨ (p2 ∧ p4)))) ∨ False)))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_149553497415838542514068070868 : ((p2 ∧ (((p1 ∨ ((p3 ∨ p1) ∨ True)) ∧ ((p2 → p3) → p3)) ∨ ((((p5 → p4) → p5) ∨ p5) ∧ True))) ∨ (p1 ∨ ((p4 ∧ p1) → True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_719329240454978615563998694406 : ((((p5 ∧ (p5 ∧ (p3 ∨ p3))) ∨ (p5 → ((((p1 ∧ True) ∧ p1) ∨ True) → (p1 ∨ ((p5 → (p2 ∧ p1)) → ((p4 → p4) ∨ False)))))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_136025234968748299256370407901 : ((((p4 ∧ ((True ∧ p5) ∨ (True ∧ p4))) → (False → p5)) → ((((p3 ∨ (p4 ∨ (True → p3))) ∧ p5) ∨ True) ∨ False)) ∨ ((p5 → False) ∨ p4)) := by
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
theorem thm_5_vars_44481026336582484295971662737 : ((((True ∨ ((p1 ∨ ((p5 ∧ (p4 ∨ (p1 → p1))) ∧ p5)) ∧ p1)) → (p4 → (((p5 → False) → (False ∧ p1)) ∧ (p1 ∨ p4)))) → False) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_214031629170661356780897609200 : ((((p2 ∨ p1) ∧ p4) → p2) ∨ (((p3 ∨ p3) ∧ p1) → (((p2 → True) ∧ (p4 ∨ False)) ∨ ((((p4 → p5) ∧ p4) → False) ∨ (p4 → True))))) := by
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
    -- Implications on the right can always be decomposed.
    intro h5
    -- True on the right can always be proven directly.
    apply True.intro
  case inr h6 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h7
    -- True on the right can always be proven directly.
    apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_207433742146507494195177442643 : (((p1 ∨ (p2 → (p2 ∧ p3))) ∨ p5) → (((p1 ∨ (p2 ∧ False)) → (False ∧ (False → True))) ∨ (((True → False) ∨ (p5 ∧ (p5 ∧ False))) → p2))) := by
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
      -- Disjunctions on the left can always be decomposed.
      cases h4
      case inl h5 =>
        -- We want to use the implication h5 based on <expert-advice>. So we show its premise.
        have h6 : True := by
          -- True on the right can always be proven directly.
          apply True.intro
        -- We have shown the premise of h5, we can now drive its conclusion.
        let h7 := h5 h6
        -- False on the left can always be used.
        apply False.elim h7
      case inr h8 =>
        -- Conjunctions on the left can always be decomposed.
        let h9 := h8.left
        let h10 := h8.right
        -- Conjunctions on the left can always be decomposed.
        let h11 := h10.left
        let h12 := h10.right
        -- False on the left can always be used.
        apply False.elim h12
    case inr h13 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Implications on the right can always be decomposed.
      intro h14
      -- Disjunctions on the left can always be decomposed.
      cases h14
      case inl h15 =>
        -- We want to use the implication h15 based on <expert-advice>. So we show its premise.
        have h16 : True := by
          -- True on the right can always be proven directly.
          apply True.intro
        -- We have shown the premise of h15, we can now drive its conclusion.
        let h17 := h15 h16
        -- False on the left can always be used.
        apply False.elim h17
      case inr h18 =>
        -- Conjunctions on the left can always be decomposed.
        let h19 := h18.left
        let h20 := h18.right
        -- Conjunctions on the left can always be decomposed.
        let h21 := h20.left
        let h22 := h20.right
        -- False on the left can always be used.
        apply False.elim h22
  case inr h23 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h24
    -- Disjunctions on the left can always be decomposed.
    cases h24
    case inl h25 =>
      -- We want to use the implication h25 based on <expert-advice>. So we show its premise.
      have h26 : True := by
        -- True on the right can always be proven directly.
        apply True.intro
      -- We have shown the premise of h25, we can now drive its conclusion.
      let h27 := h25 h26
      -- False on the left can always be used.
      apply False.elim h27
    case inr h28 =>
      -- Conjunctions on the left can always be decomposed.
      let h29 := h28.left
      let h30 := h28.right
      -- Conjunctions on the left can always be decomposed.
      let h31 := h30.left
      let h32 := h30.right
      -- False on the left can always be used.
      apply False.elim h32



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_301983574354217141459330105151 : (False ∨ ((p2 → p1) → (True → (((p1 → ((((p3 → p4) ∧ p1) → p2) ∧ ((p5 → (p4 ∨ p4)) → p5))) ∨ (p1 ∨ (p4 ∨ True))) ∨ p1)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
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



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_593430240496431600050451332628 : (((((((((False → False) ∧ (p4 ∧ False)) ∨ (p5 → p1)) ∧ (False → p2)) ∧ ((p5 → True) → (p5 → True))) → (p1 ∨ (False ∨ True))) ∧ True) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_313139730674339693966750400338 : (p3 ∨ (((p1 ∧ ((p3 ∨ p5) → ((((p4 ∨ (p1 → p3)) → True) ∨ (p5 ∨ False)) → p1))) ∨ ((False → ((True → p5) → p5)) ∧ p1)) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_342486162747028154057164446113 : (p2 → (((((p4 ∨ p3) → p4) ∨ p1) ∧ (((p1 → False) ∧ (p5 ∨ p4)) ∨ False)) ∨ ((p1 ∧ False) → (p1 ∨ ((True ∨ (p4 → p2)) ∧ p5))))) := by
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
theorem thm_5_vars_205928398964547639498414052323 : ((False ∧ (((p3 ∨ p3) ∨ p2) → p1)) ∨ ((((False ∨ (((p4 → p5) ∧ (p2 ∨ p2)) ∨ ((p5 → p5) → True))) ∨ (p1 ∧ p5)) ∧ p2) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_173432438925003477430412873091 : ((p5 → (p1 → (((False ∨ (True ∨ False)) ∨ (p1 → (p3 ∨ (p1 ∨ False)))) ∧ p2))) ∨ ((((p2 → True) ∨ (True → True)) → p3) ∨ (p3 ∨ True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_205373545496187301480820705852 : ((((True ∨ True) ∨ p5) → (True → p3)) ∨ ((False ∧ (p4 ∧ p2)) ∨ (((p3 → (p2 ∨ (p1 → ((False ∨ p5) ∨ p3)))) ∨ False) ∧ (True ∨ p5)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
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
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_231925348307907539745515762345 : (((False ∨ p3) → p4) → ((True → (p5 ∧ False)) ∨ ((True → ((p4 ∨ p1) → True)) ∨ ((True → ((p1 ∧ p1) ∧ ((False ∧ p2) ∨ False))) ∨ p1)))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h2
  -- Implications on the right can always be decomposed.
  intro h3
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_48998699830721368267012372233 : ((((p5 ∨ ((False ∨ (p5 ∨ p2)) ∨ (p1 ∧ ((p1 ∨ False) → (p1 → (p5 → (p1 → (False ∨ p5)))))))) ∨ True) ∨ (True ∧ (True ∨ p1))) ∨ p4) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_752303029349460828378130895092 : (((False ∧ (((((p1 → (p4 → True)) ∧ (p1 ∧ ((p1 ∧ (p4 → False)) ∨ (((p2 ∨ (p5 ∧ p2)) → p4) ∨ p4)))) ∨ False) ∧ p4) ∧ p1)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_114883658649774477267937059163 : (((True ∧ ((False ∨ (((p5 → ((p2 ∨ p2) ∨ False)) ∧ False) ∧ True)) ∧ False)) ∨ ((p3 → (p5 → (True ∨ (p3 → p3)))) ∨ p4)) ∨ (p4 → p4)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_793492806928372520060358638476 : (((True → (p1 ∨ (((((p3 ∨ p3) → ((p3 ∨ p4) → False)) → (False ∧ p3)) ∧ ((False → ((False ∧ p1) ∨ (p2 ∨ p1))) ∧ p1)) ∨ False))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_303534213311748175993127582397 : (p1 ∨ (((p4 → (False ∨ (p3 ∧ True))) → (p4 → ((p5 ∧ (p5 ∧ (p2 ∨ (((True ∨ p1) ∧ p3) → False)))) ∨ ((p5 → p3) ∧ p4)))) ∧ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h3
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h4 : p4 := by
    -- One of the premise coincides with the conclusion.
    exact h2
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h5 := h1 h4
  -- Disjunctions on the left can always be decomposed.
  cases h5
  case inl h6 =>
    -- False on the left can always be used.
    apply False.elim h6
  case inr h7 =>
    -- Conjunctions on the left can always be decomposed.
    let h8 := h7.left
    let h9 := h7.right
    -- One of the premise coincides with the conclusion.
    exact h8
  -- One of the premise coincides with the conclusion.
  exact h2
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_257692205038866490079572996479 : ((p3 ∨ p3) → ((((p1 ∨ ((p4 ∧ (p1 ∨ True)) ∨ p2)) ∨ (p5 ∨ (p2 ∨ p5))) → False) → (p3 ∧ ((p2 ∨ ((p5 ∨ p5) ∧ True)) → False)))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h3 =>
    -- One of the premise coincides with the conclusion.
    exact h3
  case inr h4 =>
    -- One of the premise coincides with the conclusion.
    exact h4
  -- Implications on the right can always be decomposed.
  intro h5
  -- Disjunctions on the left can always be decomposed.
  cases h5
  case inl h6 =>
    -- Disjunctions on the left can always be decomposed.
    cases h1
    case inl h7 =>
      -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
      have h8 : ((p1 ∨ ((p4 ∧ (p1 ∨ True)) ∨ p2)) ∨ (p5 ∨ (p2 ∨ p5))) := by
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- One of the premise coincides with the conclusion.
        exact h6
      -- We have shown the premise of h2, we can now drive its conclusion.
      let h9 := h2 h8
      -- False on the left can always be used.
      apply False.elim h9
    case inr h10 =>
      -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
      have h11 : ((p1 ∨ ((p4 ∧ (p1 ∨ True)) ∨ p2)) ∨ (p5 ∨ (p2 ∨ p5))) := by
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- One of the premise coincides with the conclusion.
        exact h6
      -- We have shown the premise of h2, we can now drive its conclusion.
      let h12 := h2 h11
      -- False on the left can always be used.
      apply False.elim h12
  case inr h13 =>
    -- Conjunctions on the left can always be decomposed.
    let h14 := h13.left
    let h15 := h13.right
    -- Disjunctions on the left can always be decomposed.
    cases h14
    case inl h16 =>
      -- Disjunctions on the left can always be decomposed.
      cases h1
      case inl h17 =>
        -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
        have h18 : ((p1 ∨ ((p4 ∧ (p1 ∨ True)) ∨ p2)) ∨ (p5 ∨ (p2 ∨ p5))) := by
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- Show the left disjunct based on <expert-advice>.
          apply Or.inl
          -- One of the premise coincides with the conclusion.
          exact h16
        -- We have shown the premise of h2, we can now drive its conclusion.
        let h19 := h2 h18
        -- False on the left can always be used.
        apply False.elim h19
      case inr h20 =>
        -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
        have h21 : ((p1 ∨ ((p4 ∧ (p1 ∨ True)) ∨ p2)) ∨ (p5 ∨ (p2 ∨ p5))) := by
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- Show the left disjunct based on <expert-advice>.
          apply Or.inl
          -- One of the premise coincides with the conclusion.
          exact h16
        -- We have shown the premise of h2, we can now drive its conclusion.
        let h22 := h2 h21
        -- False on the left can always be used.
        apply False.elim h22
    case inr h23 =>
      -- Disjunctions on the left can always be decomposed.
      cases h1
      case inl h24 =>
        -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
        have h25 : ((p1 ∨ ((p4 ∧ (p1 ∨ True)) ∨ p2)) ∨ (p5 ∨ (p2 ∨ p5))) := by
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- Show the left disjunct based on <expert-advice>.
          apply Or.inl
          -- One of the premise coincides with the conclusion.
          exact h23
        -- We have shown the premise of h2, we can now drive its conclusion.
        let h26 := h2 h25
        -- False on the left can always be used.
        apply False.elim h26
      case inr h27 =>
        -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
        have h28 : ((p1 ∨ ((p4 ∧ (p1 ∨ True)) ∨ p2)) ∨ (p5 ∨ (p2 ∨ p5))) := by
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- Show the left disjunct based on <expert-advice>.
          apply Or.inl
          -- One of the premise coincides with the conclusion.
          exact h23
        -- We have shown the premise of h2, we can now drive its conclusion.
        let h29 := h2 h28
        -- False on the left can always be used.
        apply False.elim h29



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_165752741777046813253238621848 : (((p4 ∧ ((p5 → p1) ∧ p5)) ∨ ((p5 ∧ p1) ∨ (p1 ∨ ((p4 ∨ p2) ∨ (False ∨ True))))) ∨ ((p3 → ((p5 ∨ p2) → (p1 ∨ p5))) ∧ p5)) := by
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
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_111866411955335222857078888481 : (((((True ∨ (p5 ∧ (p2 ∨ (p4 ∧ (p4 ∧ (((p5 ∧ p2) ∧ p4) → p4)))))) ∧ p4) ∨ ((p4 ∧ (False ∨ p4)) ∨ p5)) ∨ p3) ∨ (True ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_180506971176074793190427867590 : (((True ∨ ((((p4 ∨ p2) ∧ p2) ∨ p2) ∨ p5)) ∧ ((p1 ∧ p4) ∨ p5)) → (True ∧ (p4 ∨ (p1 ∨ ((True ∨ p4) → (p1 → (True ∧ True))))))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- Disjunctions on the left can always be decomposed.
  cases h2
  case inl h4 =>
    -- Disjunctions on the left can always be decomposed.
    cases h3
    case inl h5 =>
      -- Conjunctions on the left can always be decomposed.
      let h6 := h5.left
      let h7 := h5.right
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- One of the premise coincides with the conclusion.
      exact h7
    case inr h8 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Implications on the right can always be decomposed.
      intro h9
      -- Implications on the right can always be decomposed.
      intro h10
      -- Conjunctions on the right can always be decomposed.
      apply And.intro
      -- True on the right can always be proven directly.
      apply True.intro
      -- True on the right can always be proven directly.
      apply True.intro
  case inr h11 =>
    -- Disjunctions on the left can always be decomposed.
    cases h11
    case inl h12 =>
      -- Disjunctions on the left can always be decomposed.
      cases h12
      case inl h13 =>
        -- Conjunctions on the left can always be decomposed.
        let h14 := h13.left
        let h15 := h13.right
        -- Disjunctions on the left can always be decomposed.
        cases h14
        case inl h16 =>
          -- Disjunctions on the left can always be decomposed.
          cases h3
          case inl h17 =>
            -- Conjunctions on the left can always be decomposed.
            let h18 := h17.left
            let h19 := h17.right
            -- Show the left disjunct based on <expert-advice>.
            apply Or.inl
            -- One of the premise coincides with the conclusion.
            exact h19
          case inr h20 =>
            -- Show the left disjunct based on <expert-advice>.
            apply Or.inl
            -- One of the premise coincides with the conclusion.
            exact h16
        case inr h21 =>
          -- Disjunctions on the left can always be decomposed.
          cases h3
          case inl h22 =>
            -- Conjunctions on the left can always be decomposed.
            let h23 := h22.left
            let h24 := h22.right
            -- Show the left disjunct based on <expert-advice>.
            apply Or.inl
            -- One of the premise coincides with the conclusion.
            exact h24
          case inr h25 =>
            -- Show the right disjunct based on <expert-advice>.
            apply Or.inr
            -- Show the right disjunct based on <expert-advice>.
            apply Or.inr
            -- Implications on the right can always be decomposed.
            intro h26
            -- Implications on the right can always be decomposed.
            intro h27
            -- Conjunctions on the right can always be decomposed.
            apply And.intro
            -- True on the right can always be proven directly.
            apply True.intro
            -- True on the right can always be proven directly.
            apply True.intro
      case inr h28 =>
        -- Disjunctions on the left can always be decomposed.
        cases h3
        case inl h29 =>
          -- Conjunctions on the left can always be decomposed.
          let h30 := h29.left
          let h31 := h29.right
          -- Show the left disjunct based on <expert-advice>.
          apply Or.inl
          -- One of the premise coincides with the conclusion.
          exact h31
        case inr h32 =>
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- Implications on the right can always be decomposed.
          intro h33
          -- Implications on the right can always be decomposed.
          intro h34
          -- Conjunctions on the right can always be decomposed.
          apply And.intro
          -- True on the right can always be proven directly.
          apply True.intro
          -- True on the right can always be proven directly.
          apply True.intro
    case inr h35 =>
      -- Disjunctions on the left can always be decomposed.
      cases h3
      case inl h36 =>
        -- Conjunctions on the left can always be decomposed.
        let h37 := h36.left
        let h38 := h36.right
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- One of the premise coincides with the conclusion.
        exact h38
      case inr h39 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- Implications on the right can always be decomposed.
        intro h40
        -- Implications on the right can always be decomposed.
        intro h41
        -- Conjunctions on the right can always be decomposed.
        apply And.intro
        -- True on the right can always be proven directly.
        apply True.intro
        -- True on the right can always be proven directly.
        apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_207019908735925371173829497471 : ((((p2 → p5) ∨ (True ∧ p4)) ∧ p1) → (((True → p4) ∨ (p5 ∨ (p5 → True))) ∧ (((p2 → False) ∨ ((p3 ∨ p4) ∨ p3)) ∨ (p1 ∧ p1)))) := by
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
    -- Implications on the right can always be decomposed.
    intro h5
    -- True on the right can always be proven directly.
    apply True.intro
  case inr h6 =>
    -- Conjunctions on the left can always be decomposed.
    let h7 := h6.left
    let h8 := h6.right
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h9
    -- True on the right can always be proven directly.
    apply True.intro
  -- Conjunctions on the left can always be decomposed.
  let h10 := h1.left
  let h11 := h1.right
  -- Disjunctions on the left can always be decomposed.
  cases h10
  case inl h12 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Conjunctions on the right can always be decomposed.
    apply And.intro
    -- One of the premise coincides with the conclusion.
    exact h11
    -- One of the premise coincides with the conclusion.
    exact h11
  case inr h13 =>
    -- Conjunctions on the left can always be decomposed.
    let h14 := h13.left
    let h15 := h13.right
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Conjunctions on the right can always be decomposed.
    apply And.intro
    -- One of the premise coincides with the conclusion.
    exact h11
    -- One of the premise coincides with the conclusion.
    exact h11



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_207664463627522715599248622601 : ((((False ∨ p3) ∨ (False → p3)) → True) → (p5 → ((((p5 ∧ p1) ∨ (p1 → False)) → p4) ∨ (True ∨ (p1 ∨ (False ∧ (p1 → (p2 ∨ False)))))))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_199921953159233540698448111354 : ((((False ∧ False) ∨ (p2 ∧ p2)) ∨ (True ∧ p4)) → ((p5 ∨ ((((p2 → ((False ∨ p5) ∨ p4)) ∧ (False ∨ p4)) ∨ p1) ∨ (p2 ∧ True))) ∨ p3)) := by
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
      -- False on the left can always be used.
      apply False.elim h4
    case inr h6 =>
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
      exact h8
      -- True on the right can always be proven directly.
      apply True.intro
  case inr h9 =>
    -- Conjunctions on the left can always be decomposed.
    let h10 := h9.left
    let h11 := h9.right
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Conjunctions on the right can always be decomposed.
    apply And.intro
    -- Implications on the right can always be decomposed.
    intro h12
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h11
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h11



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_227954481289109901183426031911 : ((p3 ∧ (p4 ∧ p3)) ∨ (((p5 → ((((p5 ∧ (p3 ∨ p3)) → True) ∧ (p3 ∨ p4)) ∨ p3)) ∧ p1) ∨ ((p5 ∧ (p4 ∨ (False ∨ p5))) ∨ True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_342269472801439417312623708365 : (p2 → ((((((p4 ∧ p4) ∧ (p3 ∨ p3)) ∨ (((True ∧ True) → p5) → (p4 → p3))) ∨ True) ∧ p2) ∨ ((True ∧ p4) ∨ (p3 → (p2 ∨ p5))))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_351836426686573205958939311752 : (p4 → ((((((p3 → True) → (True → p1)) ∧ (p5 ∧ p1)) → p1) ∧ p3) → ((((p4 → False) ∨ p1) ∨ (p3 ∨ (p1 ∨ True))) ∨ (p1 ∧ False)))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Conjunctions on the left can always be decomposed.
  let h3 := h2.left
  let h4 := h2.right
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- One of the premise coincides with the conclusion.
  exact h4



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_51168702663097831193783244641 : ((((((p1 ∧ (False ∧ (p5 ∨ p5))) ∧ (p5 → ((p3 ∨ True) ∧ False))) ∨ p2) ∨ (p5 ∧ False)) ∨ ((p3 ∨ p3) → (p1 → (p3 ∨ p1)))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_61982234130299304605544948880 : ((p2 ∧ ((False ∧ (((False → (True → False)) ∧ p4) → False)) ∨ (((False ∨ p3) ∨ (p1 ∨ (p3 → p1))) ∨ (((p3 → p4) → p5) → p3)))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_8570762439859709812817567011 : (((((True → (p2 → ((((((p4 ∧ (p3 ∧ p4)) ∨ p4) ∨ p4) → p5) → (p4 ∨ (p1 ∨ p5))) ∨ p4))) ∧ p2) ∨ (True → True)) ∨ False) ∧ True) := by
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
theorem thm_5_vars_56888121910350969351008101976 : (((p3 ∧ (p1 ∧ True)) ∧ ((p2 → ((p2 ∧ (False ∨ (p4 ∧ ((p1 ∨ (p2 → p3)) ∧ True)))) ∨ p3)) ∧ ((p4 → (p4 ∨ False)) ∨ p2))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_260601204300542188722330733878 : ((p3 → p2) → ((((p4 → p5) ∨ (True → ((p4 ∨ (((True ∧ (True ∨ True)) ∨ True) ∨ p4)) ∧ (p5 ∧ p4)))) → False) ∨ ((p5 ∨ True) ∨ p3))) := by
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
theorem thm_5_vars_740720761055194392363502032596 : ((((p2 ∨ p4) ∨ ((((((False ∧ ((p2 ∨ p4) ∨ p5)) ∨ p4) ∨ (p3 ∨ p2)) ∨ p2) ∨ True) ∨ ((p3 → p1) → (False → (p3 ∨ False))))) ∨ p3) ∧ True) := by
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
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_317609373409480228250725556796 : (p4 ∨ (((True → (True ∧ (p3 ∧ (((((p2 ∨ True) ∧ p4) ∧ True) ∧ p1) ∧ (p3 ∨ ((p3 ∨ ((p1 → p1) → p2)) ∨ p4)))))) ∧ True) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_59011142062255510493654036056 : (((p3 ∧ p3) ∨ (p3 ∧ (False ∨ (((p1 ∧ (((p2 ∧ (p2 → p1)) ∨ p4) ∨ (p5 → (p3 ∧ p4)))) → (p3 ∨ (p4 ∨ p5))) ∧ p2)))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_338890482039499925515000877560 : (p1 → ((p2 ∧ p3) → (((p5 ∨ (p2 ∧ False)) → ((False ∨ ((p4 → p5) → p4)) ∨ True)) ∧ (((p2 ∨ p5) → False) ∨ (True ∨ (p1 ∧ p3)))))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h3
  -- Disjunctions on the left can always be decomposed.
  cases h3
  case inl h4 =>
    -- Conjunctions on the left can always be decomposed.
    let h5 := h2.left
    let h6 := h2.right
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro
  case inr h7 =>
    -- Conjunctions on the left can always be decomposed.
    let h8 := h7.left
    let h9 := h7.right
    -- False on the left can always be used.
    apply False.elim h9
  -- Conjunctions on the left can always be decomposed.
  let h10 := h2.left
  let h11 := h2.right
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_343600823116389016920997864910 : (p2 → ((p4 → False) → (((p2 → ((False → ((p2 → p5) → (p5 ∧ p1))) ∨ (p1 ∧ p3))) → (p3 ∧ (p3 → ((p3 → p3) → p5)))) ∨ True))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_139477622061835256970161401598 : ((((p4 ∨ ((p4 → p1) ∨ ((p1 ∧ (((p1 → p5) ∧ (True ∨ p4)) ∧ ((p5 → p2) ∨ True))) → p1))) ∨ p2) → False) → (p4 ∧ (p1 → True))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h2 : ((p4 ∨ ((p4 → p1) ∨ ((p1 ∧ (((p1 → p5) ∧ (True ∨ p4)) ∧ ((p5 → p2) ∨ True))) → p1))) ∨ p2) := by
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
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
    -- Conjunctions on the left can always be decomposed.
    let h8 := h6.left
    let h9 := h6.right
    -- Disjunctions on the left can always be decomposed.
    cases h9
    case inl h10 =>
      -- Disjunctions on the left can always be decomposed.
      cases h7
      case inl h11 =>
        -- One of the premise coincides with the conclusion.
        exact h4
      case inr h12 =>
        -- One of the premise coincides with the conclusion.
        exact h4
    case inr h13 =>
      -- Disjunctions on the left can always be decomposed.
      cases h7
      case inl h14 =>
        -- One of the premise coincides with the conclusion.
        exact h4
      case inr h15 =>
        -- One of the premise coincides with the conclusion.
        exact h4
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h16 := h1 h2
  -- False on the left can always be used.
  apply False.elim h16
  -- Implications on the right can always be decomposed.
  intro h17
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_658746976505516827407649822610 : ((((p5 ∨ ((((((((True ∨ (False → ((p2 ∨ True) ∧ True))) ∨ p5) ∨ p2) → p4) → (p4 ∨ p3)) ∨ p5) → p2) → p3)) ∨ (p3 ∨ p4)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_44805180501653835490870253926 : (((((p3 → False) → p5) ∧ ((((False ∨ p4) ∨ (p4 → ((p5 ∨ False) → p4))) → (False ∨ (p5 ∧ p2))) ∨ ((False ∧ True) ∧ p3))) → False) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_354888603354981053053817938508 : (p5 → ((p3 ∧ (((p5 ∨ p5) ∨ (p3 → ((((False ∨ (p4 → ((True ∧ p3) ∨ (p2 → p2)))) → True) → p5) ∨ (p2 ∧ True)))) → False)) ∨ p5)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_613950957661628866184145176405 : ((((((((p3 ∧ ((((True → p1) ∧ p3) → True) ∧ p3)) ∨ False) → (p3 → p5)) → ((p2 ∧ p1) ∨ True)) ∨ ((p4 ∧ p1) ∨ p1)) ∨ False) ∨ p5) ∧ True) := by
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
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_261132558238132216650395736257 : ((p4 → p4) → (((((p5 ∧ (((True → (p3 ∧ ((p4 ∧ p4) ∧ False))) ∨ False) → (False → (p4 ∨ p2)))) ∨ p4) ∧ p1) → (p3 ∨ p4)) ∨ True)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_323475139647067328526672609233 : (p5 ∨ ((((((p4 ∧ ((p4 ∨ (p5 ∨ p4)) → p5)) ∨ ((p5 ∧ p3) ∧ (p4 ∧ p5))) ∧ p4) ∨ (True ∨ False)) ∨ False) ∨ (p4 ∨ (True → p4)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
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



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_57046554492913490689718926154 : (((p3 → (p1 ∨ p5)) ∧ (((p2 ∨ p3) → (p4 ∨ False)) ∧ ((((p4 ∧ False) ∧ (True ∨ p4)) ∨ (p2 ∧ p4)) ∧ ((p1 ∧ True) ∧ p1)))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_111964842684331793086013766727 : ((((True → (p2 → ((p3 ∧ (p2 ∧ True)) ∨ p3))) → (((True ∧ p5) ∨ ((p3 ∨ False) → p2)) ∨ ((p1 → p4) ∧ False))) ∨ True) ∨ (p5 ∨ p1)) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_671656727251673735448942200632 : (((((((((False → (p2 ∧ p3)) ∧ ((False → p5) ∧ p2)) ∧ p4) ∨ (p3 ∧ (p3 ∨ (True ∧ p4)))) ∨ False) ∧ p5) → (p3 ∧ (p4 → p1))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_738104439450004573300906505275 : ((((False ∧ False) ∨ (p4 → ((p3 → ((True ∧ p2) ∧ (True → ((False ∧ (False ∨ p1)) ∧ ((False ∧ p4) ∧ False))))) ∨ ((p3 ∧ p4) ∨ p4)))) ∨ False) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_136447569583706755963950916525 : (((p3 ∧ (p1 → (p4 → p5))) → (((p5 ∨ ((((p5 ∧ (p1 ∨ p2)) ∧ p4) → p4) → (p2 → True))) ∨ p5) ∧ p2)) ∨ (False ∨ (True ∨ p4))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_89203902083757352922252525960 : ((((p5 → p5) → False) ∧ (p3 ∨ (False → (((p1 ∨ ((True → p3) ∨ (p1 ∨ p3))) → p2) ∨ (((True ∨ p1) ∨ (p3 ∨ True)) ∨ p1))))) → p5) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- Disjunctions on the left can always be decomposed.
  cases h3
  case inl h4 =>
    -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
    have h5 : (p5 → p5) := by
      -- Implications on the right can always be decomposed.
      intro h6
      -- One of the premise coincides with the conclusion.
      exact h6
    -- We have shown the premise of h2, we can now drive its conclusion.
    let h7 := h2 h5
    -- False on the left can always be used.
    apply False.elim h7
  case inr h8 =>
    -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
    have h9 : (p5 → p5) := by
      -- Implications on the right can always be decomposed.
      intro h10
      -- One of the premise coincides with the conclusion.
      exact h10
    -- We have shown the premise of h2, we can now drive its conclusion.
    let h11 := h2 h9
    -- False on the left can always be used.
    apply False.elim h11



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_719685368530715589953866359836 : ((((True → (p5 ∨ (p3 ∨ p5))) ∨ ((p4 ∨ p4) ∨ ((p4 ∧ (True ∨ ((p5 ∨ (p3 ∨ (p4 ∨ p3))) → (False → (p5 ∧ p4))))) ∨ p4))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_147785041481152674985217215292 : ((((p4 ∨ p4) → (True ∧ ((p4 ∧ ((True ∧ (p2 ∧ False)) → p1)) ∨ (((p4 ∧ p2) ∧ p3) → p5)))) → p4) ∨ ((False → p3) ∨ (p5 ∨ p5))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_309368673779247474529882276528 : (p2 ∨ (((p2 ∧ (True → p1)) ∨ (True ∧ (((p2 ∨ ((((p5 ∧ p4) ∨ (p2 ∨ (p3 → True))) ∨ False) ∨ p3)) ∨ p5) ∨ p4))) ∨ (p1 ∨ p2))) := by
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
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
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
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_338483882585615140186481932403 : (p1 → ((p1 ∨ (False → p4)) ∧ ((p1 → ((((((p1 ∨ p1) → p2) ∧ p2) ∧ (p5 ∨ ((p1 ∨ p2) ∨ False))) ∧ (p5 ∧ p3)) ∨ p5)) ∨ True))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- One of the premise coincides with the conclusion.
  exact h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_66437659527919871496832523437 : ((True → ((((p2 ∨ p3) ∨ (((True → (p4 ∨ p3)) → (p4 → p2)) ∧ (((False → (p2 ∨ False)) → (True ∧ p2)) → p2))) ∨ p5) ∧ p5)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_196932360042859410745151201060 : ((((p3 ∨ (p5 → (p2 ∨ p3))) ∧ p5) ∨ p5) ∨ ((((p1 → ((p3 ∧ p5) ∧ (True ∨ True))) ∨ True) ∨ (p2 ∧ (p3 → (True → False)))) ∨ p3)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_242809930486417652898311951291 : ((p3 → p3) ∧ (((((p1 → True) → p1) ∧ (p2 ∧ p4)) → (((((False ∨ p5) → p3) ∧ False) ∧ True) ∧ p1)) ∨ (((p1 ∧ False) → False) → True))) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h1
  -- One of the premise coincides with the conclusion.
  exact h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h2
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_253144693732715369089936005582 : ((True ∧ p5) → ((((False ∨ p5) → p5) ∨ True) → ((p5 ∧ (((True → True) → (((p4 → (p4 → p5)) → p1) → p1)) → (False ∧ False))) ∨ True))) := by
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
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro
  case inr h6 =>
    -- Conjunctions on the left can always be decomposed.
    let h7 := h1.left
    let h8 := h1.right
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_206192296333613463097572262124 : ((p5 ∧ (p3 → ((p1 ∧ p3) → False))) ∨ ((((((p4 ∧ (((p1 ∧ p5) ∨ p4) → ((True ∧ False) ∨ p2))) ∧ p5) ∧ True) ∧ False) ∨ p4) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_259982568576431274041331734341 : ((p2 → True) → (((((p4 ∨ (p1 ∨ ((p1 → False) → p5))) ∧ (p2 ∨ (p5 ∨ (((p5 → p3) ∧ p4) → (True → p5))))) → p1) ∧ p5) → p1)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Conjunctions on the left can always be decomposed.
  let h3 := h2.left
  let h4 := h2.right
  -- We want to use the implication h3 based on <expert-advice>. So we show its premise.
  have h5 : ((p4 ∨ (p1 ∨ ((p1 → False) → p5))) ∧ (p2 ∨ (p5 ∨ (((p5 → p3) ∧ p4) → (True → p5))))) := by
    -- Conjunctions on the right can always be decomposed.
    apply And.intro
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h6
    -- One of the premise coincides with the conclusion.
    exact h4
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- One of the premise coincides with the conclusion.
    exact h4
  -- We have shown the premise of h3, we can now drive its conclusion.
  let h7 := h3 h5
  -- One of the premise coincides with the conclusion.
  exact h7



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_116428510631631462535436560603 : (((True → (p1 ∨ True)) → ((p4 → ((((((True ∧ p2) ∨ p2) ∧ p4) ∧ p3) → (p2 → (p4 → p4))) ∨ p4)) ∧ (p1 ∨ p3))) ∨ (p4 → p4)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_177904554735643071615934632760 : ((((p1 ∨ (p4 ∨ (((p1 ∨ p3) → p3) → p1))) ∨ (p2 ∨ p1)) ∨ True) ∨ (p3 ∨ (((p5 ∧ (p1 ∨ True)) ∧ (p5 ∧ True)) → (False → p5)))) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_244686602305639756203708976657 : ((p1 ∧ True) ∨ (((p1 ∨ (p3 ∧ ((p1 ∧ p1) ∨ False))) ∧ ((True ∨ ((p5 ∧ (p1 ∨ (p1 ∨ False))) ∨ (False ∨ p3))) → p1)) ∨ (p3 → True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_338509052364878015859836070216 : (p1 → (((True → False) ∧ p2) ∨ ((((p5 ∨ p4) ∨ (True → p4)) ∨ (((((p5 → ((True ∨ p3) ∨ p3)) ∧ p3) ∨ True) → p2) ∨ p4)) ∨ p1))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_134686520978512391063051733055 : (((((False ∨ p2) ∨ (p1 ∨ (p2 ∧ p2))) ∨ (((p2 ∧ (p3 → False)) ∧ ((p3 → p4) ∨ (p2 → p1))) ∧ p3)) → p1) ∨ (p4 ∨ (False → p2))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_192933215319139985352563637734 : (((((p1 ∨ p2) ∨ p3) ∧ (p4 ∧ False)) ∨ (p5 → p3)) → ((p3 ∧ p4) → ((True → (p3 ∨ True)) → ((True → (False ∨ (p2 ∨ p1))) ∨ p3)))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Implications on the right can always be decomposed.
  intro h3
  -- Conjunctions on the left can always be decomposed.
  let h4 := h2.left
  let h5 := h2.right
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h6 =>
    -- Conjunctions on the left can always be decomposed.
    let h7 := h6.left
    let h8 := h6.right
    -- Disjunctions on the left can always be decomposed.
    cases h7
    case inl h9 =>
      -- Disjunctions on the left can always be decomposed.
      cases h9
      case inl h10 =>
        -- Conjunctions on the left can always be decomposed.
        let h11 := h8.left
        let h12 := h8.right
        -- False on the left can always be used.
        apply False.elim h12
      case inr h13 =>
        -- Conjunctions on the left can always be decomposed.
        let h14 := h8.left
        let h15 := h8.right
        -- False on the left can always be used.
        apply False.elim h15
    case inr h16 =>
      -- Conjunctions on the left can always be decomposed.
      let h17 := h8.left
      let h18 := h8.right
      -- False on the left can always be used.
      apply False.elim h18
  case inr h19 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h4



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_995000508289948583167146860493 : (((p5 ∧ (((p3 ∨ (((((p4 ∨ False) ∧ p1) ∧ p2) ∨ p5) → True)) → ((False ∧ p1) ∧ True)) ∧ (p3 → (((p1 ∧ p5) → p1) → p5)))) → p3) ∧ True) := by
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
  -- We want to use the implication h4 based on <expert-advice>. So we show its premise.
  have h6 : (p3 ∨ (((((p4 ∨ False) ∧ p1) ∧ p2) ∨ p5) → True)) := by
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h7
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h4, we can now drive its conclusion.
  let h8 := h4 h6
  -- We need to get the left conjuct of h8 based on <expert-advice>.
  let h9 := h8.left
  -- We need to get the left conjuct of h9 based on <expert-advice>.
  let h10 := h9.left
  -- False on the left can always be used.
  apply False.elim h10
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_603932690000843583217113357620 : ((((p5 ∨ ((p1 ∨ (((p1 ∨ (p5 → ((p1 → p2) → p2))) ∨ p1) ∨ (((p4 → p2) ∨ (p5 ∨ (False ∧ p1))) ∧ False))) ∧ True)) ∧ p5) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_129345982888779561271347199926 : (((True ∧ (((p2 ∧ (p5 ∨ ((((p3 ∧ p3) ∨ True) ∨ ((p5 ∧ p1) ∧ (False ∨ p2))) → p3))) ∧ p3) ∨ True)) ∨ p4) ∧ (p5 → (p2 → True))) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
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
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_44767528482975528604617310907 : (((((p4 → False) ∧ (p3 ∧ False)) → ((p2 ∧ ((True ∨ True) ∨ ((True ∨ ((p5 → p1) ∧ p5)) ∧ p3))) → (p2 ∨ (p5 → True)))) → p1) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_230567290428185563672481551063 : (((p1 → False) ∧ p1) → ((((p2 → (False ∧ p2)) → (p3 ∨ ((True → (((p4 ∧ (True → p1)) ∨ p1) → p2)) ∧ p3))) ∨ (False → True)) ∧ p5)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h4
  -- True on the right can always be proven directly.
  apply True.intro
  -- Conjunctions on the left can always be decomposed.
  let h5 := h1.left
  let h6 := h1.right
  -- We want to use the implication h5 based on <expert-advice>. So we show its premise.
  have h7 : p1 := by
    -- One of the premise coincides with the conclusion.
    exact h6
  -- We have shown the premise of h5, we can now drive its conclusion.
  let h8 := h5 h7
  -- False on the left can always be used.
  apply False.elim h8



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_300098241101924345971038590641 : (False ∨ (((p1 ∨ ((p1 ∨ (p3 ∧ ((p3 ∨ ((False → False) ∧ p5)) ∧ p5))) ∨ (False → False))) ∧ (p3 ∨ (False ∨ (True ∨ p2)))) ∨ (p4 ∨ p2))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- False on the left can always be used.
  apply False.elim h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_320050466187443822832213350057 : (p4 ∨ ((p4 ∧ (False ∧ p3)) ∨ ((((((p3 → p1) → False) → (False → False)) → (p4 ∧ p2)) ∨ True) ∨ ((p2 ∧ p3) ∧ ((p2 ∨ True) → p2))))) := by
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
theorem thm_5_vars_184263391790662395335917720154 : ((((((False → (p1 ∨ p5)) → p3) ∨ p1) ∨ (p3 → p4)) → p5) ∨ (((p2 → (p3 ∨ (p1 → True))) → True) ∨ (p1 ∨ (p2 ∨ (p4 → p2))))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



