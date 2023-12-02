variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_38854089683500956919025607748 : (((((p4 → p2) → p1) ∧ ((True → (p4 ∨ p1)) ∨ ((True ∧ (p1 ∧ True)) → (p2 → (p3 ∧ (((p1 ∨ False) → p3) ∨ p4)))))) ∧ p4) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_352333784530548275862114207905 : (p4 → (((p5 ∨ p3) → True) ∧ (p3 ∨ (((((p3 ∧ p5) ∧ p1) ∨ (((p5 → (True ∨ p4)) ∧ p1) ∧ (True ∧ p1))) ∨ True) ∨ (p5 ∨ p5))))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
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
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_263786425613072419382440381811 : (True ∧ ((((p2 ∨ p5) ∨ (((((p5 ∨ p1) → (True → p3)) ∧ p5) → True) → p5)) ∧ p2) ∨ (True ∨ ((p1 ∧ (p5 ∧ (p5 ∨ p5))) ∧ p5)))) := by
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



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_157090619342535622146463362033 : (((True → ((((p4 ∨ p5) → False) → ((((p2 ∧ p2) ∧ p1) → p5) ∨ p5)) ∧ (False ∨ p1))) ∨ True) ∨ (False → (p4 → ((p4 → True) ∨ p3)))) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_354693542393586411640712427354 : (p5 → (((((p2 → p2) → p3) ∨ (((((False ∨ True) → (False ∨ p1)) → (p2 ∨ (p1 ∧ False))) ∨ (p2 ∧ True)) ∨ p4)) ∨ (p4 ∨ p4)) ∨ True)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_219551877141868168894905711974 : ((True → ((True ∨ True) ∧ p2)) → (((p4 ∨ ((p2 → (p1 → p2)) ∧ (p1 → ((False ∧ (p3 ∨ (p3 ∧ p2))) ∧ (p5 ∧ p1))))) → p1) ∨ p2)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h2 : True := by
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h3 := h1 h2
  -- We need to get the right conjuct of h3 based on <expert-advice>.
  let h4 := h3.right
  -- One of the premise coincides with the conclusion.
  exact h4



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_135541803763804027897439978888 : ((((False ∧ ((p1 ∧ (p3 → True)) ∧ False)) ∧ (False ∨ (p4 ∨ ((True ∨ p5) ∧ p1)))) ∧ (((p2 ∨ p2) ∨ p1) ∧ p2)) ∨ ((p3 ∧ p5) → True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_454259782617076101983205284760 : (((((p1 ∧ (p3 ∨ False)) ∧ (p3 → (False ∨ (((False → True) ∨ False) → ((True ∨ (p4 ∧ p4)) ∧ False))))) → (p4 ∧ (p5 ∧ (p3 → p4)))) ∧ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
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
  -- Disjunctions on the left can always be decomposed.
  cases h5
  case inl h6 =>
    -- We want to use the implication h3 based on <expert-advice>. So we show its premise.
    have h7 : p3 := by
      -- One of the premise coincides with the conclusion.
      exact h6
    -- We have shown the premise of h3, we can now drive its conclusion.
    let h8 := h3 h7
    -- Disjunctions on the left can always be decomposed.
    cases h8
    case inl h9 =>
      -- False on the left can always be used.
      apply False.elim h9
    case inr h10 =>
      -- We want to use the implication h10 based on <expert-advice>. So we show its premise.
      have h11 : ((False → True) ∨ False) := by
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- Implications on the right can always be decomposed.
        intro h12
        -- True on the right can always be proven directly.
        apply True.intro
      -- We have shown the premise of h10, we can now drive its conclusion.
      let h13 := h10 h11
      -- We need to get the right conjuct of h13 based on <expert-advice>.
      let h14 := h13.right
      -- False on the left can always be used.
      apply False.elim h14
  case inr h15 =>
    -- False on the left can always be used.
    apply False.elim h15
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Conjunctions on the left can always be decomposed.
  let h16 := h1.left
  let h17 := h1.right
  -- Conjunctions on the left can always be decomposed.
  let h18 := h16.left
  let h19 := h16.right
  -- Disjunctions on the left can always be decomposed.
  cases h19
  case inl h20 =>
    -- We want to use the implication h17 based on <expert-advice>. So we show its premise.
    have h21 : p3 := by
      -- One of the premise coincides with the conclusion.
      exact h20
    -- We have shown the premise of h17, we can now drive its conclusion.
    let h22 := h17 h21
    -- Disjunctions on the left can always be decomposed.
    cases h22
    case inl h23 =>
      -- False on the left can always be used.
      apply False.elim h23
    case inr h24 =>
      -- We want to use the implication h24 based on <expert-advice>. So we show its premise.
      have h25 : ((False → True) ∨ False) := by
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- Implications on the right can always be decomposed.
        intro h26
        -- True on the right can always be proven directly.
        apply True.intro
      -- We have shown the premise of h24, we can now drive its conclusion.
      let h27 := h24 h25
      -- We need to get the right conjuct of h27 based on <expert-advice>.
      let h28 := h27.right
      -- False on the left can always be used.
      apply False.elim h28
  case inr h29 =>
    -- False on the left can always be used.
    apply False.elim h29
  -- Implications on the right can always be decomposed.
  intro h30
  -- Conjunctions on the left can always be decomposed.
  let h31 := h1.left
  let h32 := h1.right
  -- Conjunctions on the left can always be decomposed.
  let h33 := h31.left
  let h34 := h31.right
  -- Disjunctions on the left can always be decomposed.
  cases h34
  case inl h35 =>
    -- We want to use the implication h32 based on <expert-advice>. So we show its premise.
    have h36 : p3 := by
      -- One of the premise coincides with the conclusion.
      exact h35
    -- We have shown the premise of h32, we can now drive its conclusion.
    let h37 := h32 h36
    -- Disjunctions on the left can always be decomposed.
    cases h37
    case inl h38 =>
      -- False on the left can always be used.
      apply False.elim h38
    case inr h39 =>
      -- We want to use the implication h39 based on <expert-advice>. So we show its premise.
      have h40 : ((False → True) ∨ False) := by
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- Implications on the right can always be decomposed.
        intro h41
        -- True on the right can always be proven directly.
        apply True.intro
      -- We have shown the premise of h39, we can now drive its conclusion.
      let h42 := h39 h40
      -- We need to get the right conjuct of h42 based on <expert-advice>.
      let h43 := h42.right
      -- False on the left can always be used.
      apply False.elim h43
  case inr h44 =>
    -- False on the left can always be used.
    apply False.elim h44
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_609323385812787468354161902076 : ((((((p2 → p5) ∧ (((p1 ∧ False) ∨ (((p4 ∨ ((False → False) ∨ p5)) ∧ ((False → p2) ∨ False)) ∧ p3)) ∨ (False ∧ p1))) ∨ p3) ∨ True) ∨ p5) ∧ True) := by
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
theorem thm_5_vars_193640123010808902674904750197 : ((True ∧ (p4 → ((((p2 ∧ True) ∧ p2) ∨ p1) → p5))) → (((p5 ∧ (p3 → False)) ∨ ((((p4 ∧ (p1 → p3)) ∧ p1) ∨ p3) ∧ p4)) ∨ True)) := by
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
theorem thm_5_vars_909387896534552390904265712710 : (((((True ∨ (True → p1)) → (((p4 → True) → (False ∧ (False ∧ (p2 ∧ p4)))) ∧ (p4 ∨ p1))) ∧ (((p1 → p3) ∨ p2) ∨ (p2 → True))) → False) ∧ True) := by
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
    -- Disjunctions on the left can always be decomposed.
    cases h4
    case inl h5 =>
      -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
      have h6 : (True ∨ (True → p1)) := by
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- True on the right can always be proven directly.
        apply True.intro
      -- We have shown the premise of h2, we can now drive its conclusion.
      let h7 := h2 h6
      -- We need to get the left conjuct of h7 based on <expert-advice>.
      let h8 := h7.left
      -- We want to use the implication h8 based on <expert-advice>. So we show its premise.
      have h9 : (p4 → True) := by
        -- Implications on the right can always be decomposed.
        intro h10
        -- True on the right can always be proven directly.
        apply True.intro
      -- We have shown the premise of h8, we can now drive its conclusion.
      let h11 := h8 h9
      -- We need to get the left conjuct of h11 based on <expert-advice>.
      let h12 := h11.left
      -- False on the left can always be used.
      apply False.elim h12
    case inr h13 =>
      -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
      have h14 : (True ∨ (True → p1)) := by
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- True on the right can always be proven directly.
        apply True.intro
      -- We have shown the premise of h2, we can now drive its conclusion.
      let h15 := h2 h14
      -- We need to get the left conjuct of h15 based on <expert-advice>.
      let h16 := h15.left
      -- We want to use the implication h16 based on <expert-advice>. So we show its premise.
      have h17 : (p4 → True) := by
        -- Implications on the right can always be decomposed.
        intro h18
        -- True on the right can always be proven directly.
        apply True.intro
      -- We have shown the premise of h16, we can now drive its conclusion.
      let h19 := h16 h17
      -- We need to get the left conjuct of h19 based on <expert-advice>.
      let h20 := h19.left
      -- False on the left can always be used.
      apply False.elim h20
  case inr h21 =>
    -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
    have h22 : (True ∨ (True → p1)) := by
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- True on the right can always be proven directly.
      apply True.intro
    -- We have shown the premise of h2, we can now drive its conclusion.
    let h23 := h2 h22
    -- We need to get the left conjuct of h23 based on <expert-advice>.
    let h24 := h23.left
    -- We want to use the implication h24 based on <expert-advice>. So we show its premise.
    have h25 : (p4 → True) := by
      -- Implications on the right can always be decomposed.
      intro h26
      -- True on the right can always be proven directly.
      apply True.intro
    -- We have shown the premise of h24, we can now drive its conclusion.
    let h27 := h24 h25
    -- We need to get the left conjuct of h27 based on <expert-advice>.
    let h28 := h27.left
    -- False on the left can always be used.
    apply False.elim h28
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_66206186630364024029845562855 : ((p5 ∨ ((False ∨ ((((((p3 ∨ p4) ∨ p1) → p5) → False) ∧ p3) → (p5 ∧ p3))) ∨ (p5 ∨ (p1 ∨ (((True → p2) ∧ p5) → p2))))) ∨ p1) := by
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
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
  have h4 : True := by
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h2, we can now drive its conclusion.
  let h5 := h2 h4
  -- One of the premise coincides with the conclusion.
  exact h5



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_748951082025323021934332734456 : ((((p4 → p3) → (((p5 ∧ False) ∨ ((p4 ∨ p1) ∧ p5)) ∧ (p4 → (p3 ∨ (p5 → (True ∧ (p5 → ((p1 → (p5 ∨ p4)) → p5)))))))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_112901140397652035459599392073 : ((((True ∧ p2) ∨ (True ∧ (((p1 ∧ (False ∧ (False ∨ p3))) → (p2 ∨ p4)) ∨ (p3 ∨ (((p5 ∨ p1) ∨ p2) → p2))))) → False) ∨ (p4 → p4)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_42616559377295383458935583977 : (((p3 ∨ (((p1 ∧ False) ∨ ((((p1 ∨ (p4 ∧ (False ∨ (p4 ∧ True)))) ∨ (p4 ∨ (p5 → p5))) ∨ p5) → p3)) ∨ (p1 ∨ p3))) ∨ p5) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_184443293561785169922689801115 : (((True ∧ (p5 ∧ ((p2 ∨ p2) ∧ (p3 ∨ p2)))) ∧ (p3 ∧ False)) ∨ ((((p3 → p1) → (p5 → (p2 ∨ (True ∨ p2)))) ∧ p4) ∨ (False ∨ True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_345420521200047921364690611322 : (p3 → (((p2 ∧ ((p4 ∧ ((False → p4) ∧ p4)) ∧ ((((p1 ∨ p2) ∨ (True ∧ p5)) ∧ (p1 ∨ p1)) → ((p5 → True) ∧ True)))) → False) ∨ True)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_123923480236269778788288144216 : ((((((p5 → (p3 ∧ p2)) ∨ p2) ∨ p5) ∧ ((p2 ∨ p2) → p1)) ∧ ((p2 ∨ p5) → ((p5 → p3) ∨ (p1 ∧ (p4 ∧ p3))))) → (p3 ∨ True)) := by
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



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_230110169980933736991650812367 : (((p3 ∧ p2) ∧ p5) → (p4 → (((((p1 ∧ p4) → (((p4 ∧ p2) ∧ p4) ∨ p4)) ∨ False) ∨ (p3 → True)) → ((p3 → p1) → (p2 → p1))))) := by
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
  -- Disjunctions on the left can always be decomposed.
  cases h3
  case inl h6 =>
    -- Disjunctions on the left can always be decomposed.
    cases h6
    case inl h7 =>
      -- Conjunctions on the left can always be decomposed.
      let h8 := h1.left
      let h9 := h1.right
      -- Conjunctions on the left can always be decomposed.
      let h10 := h8.left
      let h11 := h8.right
      -- We want to use the implication h4 based on <expert-advice>. So we show its premise.
      have h12 : p3 := by
        -- One of the premise coincides with the conclusion.
        exact h10
      -- We have shown the premise of h4, we can now drive its conclusion.
      let h13 := h4 h12
      -- One of the premise coincides with the conclusion.
      exact h13
    case inr h14 =>
      -- False on the left can always be used.
      apply False.elim h14
  case inr h15 =>
    -- Conjunctions on the left can always be decomposed.
    let h16 := h1.left
    let h17 := h1.right
    -- Conjunctions on the left can always be decomposed.
    let h18 := h16.left
    let h19 := h16.right
    -- We want to use the implication h4 based on <expert-advice>. So we show its premise.
    have h20 : p3 := by
      -- One of the premise coincides with the conclusion.
      exact h18
    -- We have shown the premise of h4, we can now drive its conclusion.
    let h21 := h4 h20
    -- One of the premise coincides with the conclusion.
    exact h21



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_171655217170282225793317961663 : (((False ∧ (p3 → (((p3 ∧ ((p1 → p1) ∧ p1)) ∨ p5) ∨ (False ∧ True)))) ∨ p4) ∨ ((p2 ∧ ((p4 ∧ ((p5 ∨ p5) ∨ p4)) ∨ p4)) → p4)) := by
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
    -- Conjunctions on the left can always be decomposed.
    let h5 := h4.left
    let h6 := h4.right
    -- Disjunctions on the left can always be decomposed.
    cases h6
    case inl h7 =>
      -- Disjunctions on the left can always be decomposed.
      cases h7
      case inl h8 =>
        -- One of the premise coincides with the conclusion.
        exact h5
      case inr h9 =>
        -- One of the premise coincides with the conclusion.
        exact h5
    case inr h10 =>
      -- One of the premise coincides with the conclusion.
      exact h10
  case inr h11 =>
    -- One of the premise coincides with the conclusion.
    exact h11



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_190768473076228558388673549513 : ((((True ∧ ((p1 ∨ False) ∨ p2)) ∧ p5) ∨ (p5 ∧ p1)) ∨ (((p2 ∧ (p3 ∧ ((False → (p4 ∨ p4)) → p5))) ∧ p4) ∨ ((True ∨ p5) ∨ p3))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_179139214824708362385606217360 : ((p1 ∧ (p4 ∧ (True ∧ ((((False → p5) ∨ (p4 ∧ True)) → False) ∧ p2)))) ∨ (False ∨ (((p5 ∧ (((p1 ∧ p2) ∨ p5) ∨ False)) → True) ∧ True))) := by
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
theorem thm_5_vars_229414214088022200920937497850 : ((p1 → (p5 ∨ False)) ∨ (((p1 ∧ False) ∧ p3) ∨ (((True ∨ (p3 ∧ (p4 → (((False → ((p3 ∨ p2) ∨ p2)) → p4) → p2)))) ∧ p4) → p4))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
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
    -- One of the premise coincides with the conclusion.
    exact h3
  case inr h5 =>
    -- Conjunctions on the left can always be decomposed.
    let h6 := h5.left
    let h7 := h5.right
    -- One of the premise coincides with the conclusion.
    exact h3



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_184314023553261558920165100442 : ((((True → p3) ∧ ((p4 ∨ True) ∨ (False → (p1 → p3)))) → p4) ∨ (((((False → (p3 → p3)) ∨ True) → ((p5 ∧ p4) ∧ p4)) ∨ True) ∨ p4)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_218140061049691658661161114403 : (((p4 → False) ∧ (p5 ∨ p5)) → (((p1 ∨ ((p4 ∨ p4) ∨ p5)) ∨ p4) ∨ ((p3 ∧ ((p4 → True) → ((p2 → p1) ∧ (p4 → p1)))) → p1))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- Disjunctions on the left can always be decomposed.
  cases h3
  case inl h4 =>
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h4
  case inr h5 =>
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h5



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_669300055871737139068304241394 : (((((((((p3 ∨ p4) ∨ p2) ∨ ((True ∧ True) ∧ (((True → p1) → p5) ∧ False))) ∨ False) ∨ p4) ∧ (p5 → p3)) ∨ ((p4 ∧ p5) ∨ p3)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_117397172337560244344603877128 : ((p1 ∧ (((p4 → (True ∧ p3)) ∧ ((((p3 ∧ p2) → False) ∨ ((p2 ∧ (p1 ∧ (p1 ∧ p3))) → p3)) → (p1 → False))) ∨ p3)) ∨ (True ∨ p2)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_191794433508391535226108336188 : ((p2 ∨ ((p5 → (((p4 ∨ False) ∧ p4) ∨ p2)) ∧ True)) ∨ ((((False ∨ True) ∧ (False ∨ ((p3 ∧ p1) → (p4 ∧ (p1 → p2))))) → True) ∨ p2)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_112646288809230256838923769040 : ((((((p5 → ((True ∧ ((p2 ∧ p4) → ((p2 ∨ p3) ∨ p2))) ∧ p3)) ∧ (True → p2)) ∧ p5) ∧ ((p5 ∨ p3) ∨ p2)) → False) ∨ (p2 → p2)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_44987797078611813337038203937 : ((((p4 → p4) ∧ ((p5 ∧ (((p4 ∧ (p5 ∧ p1)) → ((p4 → (p3 ∧ p4)) ∨ p5)) ∧ True)) → (p4 → ((True → True) ∧ p5)))) → p5) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_352638091854812396543237639249 : (p4 → ((p2 ∧ True) ∨ ((True → (((p4 ∧ True) ∧ (((p1 ∧ p1) ∨ p1) ∨ False)) ∨ ((p5 ∨ p3) → ((False ∨ (p2 ∧ p3)) → p5)))) ∨ True))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_237951367707647905805893394499 : ((True ∨ False) ∧ (((((p3 → ((p3 ∧ (p2 ∧ (p4 ∧ p1))) ∨ p5)) ∨ False) ∨ (p4 ∧ (p5 → False))) → False) ∨ ((p2 → (p3 ∧ p3)) → True))) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_172209387186239120566858567502 : (((((p2 ∨ p2) ∧ p4) ∨ (((True → p2) ∧ p4) ∧ p4)) → (False ∨ (False ∨ p2))) ∨ (p4 ∧ ((p4 ∧ (p4 ∧ p5)) ∨ (True ∨ (True ∨ True))))) := by
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
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- One of the premise coincides with the conclusion.
      exact h5
    case inr h6 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- One of the premise coincides with the conclusion.
      exact h6
  case inr h7 =>
    -- Conjunctions on the left can always be decomposed.
    let h8 := h7.left
    let h9 := h7.right
    -- Conjunctions on the left can always be decomposed.
    let h10 := h8.left
    let h11 := h8.right
    -- We want to use the implication h10 based on <expert-advice>. So we show its premise.
    have h12 : True := by
      -- True on the right can always be proven directly.
      apply True.intro
    -- We have shown the premise of h10, we can now drive its conclusion.
    let h13 := h10 h12
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h13



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_762894722072098450491281024792 : (((p3 ∧ (((((p1 ∨ False) ∨ p3) ∧ p5) ∧ p1) → ((False → (True ∧ ((True ∧ p1) → p5))) → ((p1 ∨ ((p5 ∧ p2) → p4)) → p4)))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_116479050545651818481335188969 : (((p1 ∧ p4) ∧ (((((p4 ∨ p1) → (((((p5 ∧ True) → p1) ∨ (p5 → (False ∨ False))) ∧ p4) ∧ p5)) ∧ p3) ∨ p4) ∨ False)) ∨ (True ∨ False)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_56458412738806178215408173412 : ((((p5 → p2) ∨ (p1 → p5)) → ((p3 ∨ (p4 → ((True ∨ (p3 ∧ (p4 ∧ False))) ∨ ((p4 ∨ (p1 ∧ True)) → p5)))) ∧ (p2 → p3))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_83263281923696051444835959477 : ((((((True ∨ True) ∧ (p5 → (p1 ∧ p5))) ∧ (p4 ∧ ((p5 ∨ False) ∨ p1))) ∧ (p5 ∨ p1)) ∧ ((p4 → True) ∧ ((p5 ∨ p4) ∧ p4))) → p1) := by
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
  let h8 := h6.left
  let h9 := h6.right
  -- Disjunctions on the left can always be decomposed.
  cases h8
  case inl h10 =>
    -- Conjunctions on the left can always be decomposed.
    let h11 := h7.left
    let h12 := h7.right
    -- Disjunctions on the left can always be decomposed.
    cases h12
    case inl h13 =>
      -- Disjunctions on the left can always be decomposed.
      cases h13
      case inl h14 =>
        -- Disjunctions on the left can always be decomposed.
        cases h5
        case inl h15 =>
          -- Conjunctions on the left can always be decomposed.
          let h16 := h3.left
          let h17 := h3.right
          -- Conjunctions on the left can always be decomposed.
          let h18 := h17.left
          let h19 := h17.right
          -- Disjunctions on the left can always be decomposed.
          cases h18
          case inl h20 =>
            -- We want to use the implication h9 based on <expert-advice>. So we show its premise.
            have h21 : p5 := by
              -- One of the premise coincides with the conclusion.
              exact h20
            -- We have shown the premise of h9, we can now drive its conclusion.
            let h22 := h9 h21
            -- We need to get the left conjuct of h22 based on <expert-advice>.
            let h23 := h22.left
            -- One of the premise coincides with the conclusion.
            exact h23
          case inr h24 =>
            -- We want to use the implication h9 based on <expert-advice>. So we show its premise.
            have h25 : p5 := by
              -- One of the premise coincides with the conclusion.
              exact h15
            -- We have shown the premise of h9, we can now drive its conclusion.
            let h26 := h9 h25
            -- We need to get the left conjuct of h26 based on <expert-advice>.
            let h27 := h26.left
            -- One of the premise coincides with the conclusion.
            exact h27
        case inr h28 =>
          -- Conjunctions on the left can always be decomposed.
          let h29 := h3.left
          let h30 := h3.right
          -- Conjunctions on the left can always be decomposed.
          let h31 := h30.left
          let h32 := h30.right
          -- Disjunctions on the left can always be decomposed.
          cases h31
          case inl h33 =>
            -- One of the premise coincides with the conclusion.
            exact h28
          case inr h34 =>
            -- One of the premise coincides with the conclusion.
            exact h28
      case inr h35 =>
        -- False on the left can always be used.
        apply False.elim h35
    case inr h36 =>
      -- Disjunctions on the left can always be decomposed.
      cases h5
      case inl h37 =>
        -- Conjunctions on the left can always be decomposed.
        let h38 := h3.left
        let h39 := h3.right
        -- Conjunctions on the left can always be decomposed.
        let h40 := h39.left
        let h41 := h39.right
        -- Disjunctions on the left can always be decomposed.
        cases h40
        case inl h42 =>
          -- One of the premise coincides with the conclusion.
          exact h36
        case inr h43 =>
          -- One of the premise coincides with the conclusion.
          exact h36
      case inr h44 =>
        -- Conjunctions on the left can always be decomposed.
        let h45 := h3.left
        let h46 := h3.right
        -- Conjunctions on the left can always be decomposed.
        let h47 := h46.left
        let h48 := h46.right
        -- Disjunctions on the left can always be decomposed.
        cases h47
        case inl h49 =>
          -- One of the premise coincides with the conclusion.
          exact h44
        case inr h50 =>
          -- One of the premise coincides with the conclusion.
          exact h44
  case inr h51 =>
    -- Conjunctions on the left can always be decomposed.
    let h52 := h7.left
    let h53 := h7.right
    -- Disjunctions on the left can always be decomposed.
    cases h53
    case inl h54 =>
      -- Disjunctions on the left can always be decomposed.
      cases h54
      case inl h55 =>
        -- Disjunctions on the left can always be decomposed.
        cases h5
        case inl h56 =>
          -- Conjunctions on the left can always be decomposed.
          let h57 := h3.left
          let h58 := h3.right
          -- Conjunctions on the left can always be decomposed.
          let h59 := h58.left
          let h60 := h58.right
          -- Disjunctions on the left can always be decomposed.
          cases h59
          case inl h61 =>
            -- We want to use the implication h9 based on <expert-advice>. So we show its premise.
            have h62 : p5 := by
              -- One of the premise coincides with the conclusion.
              exact h61
            -- We have shown the premise of h9, we can now drive its conclusion.
            let h63 := h9 h62
            -- We need to get the left conjuct of h63 based on <expert-advice>.
            let h64 := h63.left
            -- One of the premise coincides with the conclusion.
            exact h64
          case inr h65 =>
            -- We want to use the implication h9 based on <expert-advice>. So we show its premise.
            have h66 : p5 := by
              -- One of the premise coincides with the conclusion.
              exact h56
            -- We have shown the premise of h9, we can now drive its conclusion.
            let h67 := h9 h66
            -- We need to get the left conjuct of h67 based on <expert-advice>.
            let h68 := h67.left
            -- One of the premise coincides with the conclusion.
            exact h68
        case inr h69 =>
          -- Conjunctions on the left can always be decomposed.
          let h70 := h3.left
          let h71 := h3.right
          -- Conjunctions on the left can always be decomposed.
          let h72 := h71.left
          let h73 := h71.right
          -- Disjunctions on the left can always be decomposed.
          cases h72
          case inl h74 =>
            -- One of the premise coincides with the conclusion.
            exact h69
          case inr h75 =>
            -- One of the premise coincides with the conclusion.
            exact h69
      case inr h76 =>
        -- False on the left can always be used.
        apply False.elim h76
    case inr h77 =>
      -- Disjunctions on the left can always be decomposed.
      cases h5
      case inl h78 =>
        -- Conjunctions on the left can always be decomposed.
        let h79 := h3.left
        let h80 := h3.right
        -- Conjunctions on the left can always be decomposed.
        let h81 := h80.left
        let h82 := h80.right
        -- Disjunctions on the left can always be decomposed.
        cases h81
        case inl h83 =>
          -- One of the premise coincides with the conclusion.
          exact h77
        case inr h84 =>
          -- One of the premise coincides with the conclusion.
          exact h77
      case inr h85 =>
        -- Conjunctions on the left can always be decomposed.
        let h86 := h3.left
        let h87 := h3.right
        -- Conjunctions on the left can always be decomposed.
        let h88 := h87.left
        let h89 := h87.right
        -- Disjunctions on the left can always be decomposed.
        cases h88
        case inl h90 =>
          -- One of the premise coincides with the conclusion.
          exact h85
        case inr h91 =>
          -- One of the premise coincides with the conclusion.
          exact h85



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_184919927767691388471508795916 : (((False ∧ (p4 ∨ p2)) ∨ ((p2 → (p4 ∨ (False ∧ False))) ∨ True)) ∨ ((p2 ∧ (((True → ((p5 ∧ False) ∧ (p2 ∨ p1))) ∧ p5) ∧ p3)) ∧ p2)) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_142511311359327435035048259777 : ((True ∨ (((True → (((((p1 → p4) → (((p2 ∨ p1) → p4) ∧ p4)) ∧ p4) → p5) → (p1 ∨ p1))) → p4) ∨ p5)) → ((p5 ∧ p4) → p5)) := by
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
    exact h3
  case inr h6 =>
    -- Disjunctions on the left can always be decomposed.
    cases h6
    case inl h7 =>
      -- One of the premise coincides with the conclusion.
      exact h3
    case inr h8 =>
      -- One of the premise coincides with the conclusion.
      exact h8



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_612480359551195024772358695107 : ((((((p2 ∧ (True ∧ ((((p4 ∧ ((p5 ∨ (((p2 ∨ p1) ∧ p2) ∧ p2)) ∨ p3)) ∧ True) ∨ p1) → p2))) ∧ p3) ∨ (False → p2)) ∨ p5) ∨ p2) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
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
theorem thm_5_vars_118320107464667976744278533698 : ((p1 ∨ (p3 → ((p2 ∨ ((p1 ∧ ((p4 ∧ p4) ∨ (p5 → False))) → (p3 ∨ (p1 ∧ p2)))) ∧ (p4 ∧ (p5 ∧ (True → p5)))))) ∨ (False ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_734170334222603630874730083582 : ((((False ∨ True) ∧ (((p5 → (((p1 ∧ ((((p1 → True) ∧ p2) → True) ∧ p4)) ∨ p4) ∧ (p2 ∨ (p2 → p3)))) ∨ (p4 ∧ p4)) ∧ p3)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_196921228599920412663108538288 : (((((False ∧ p1) ∨ (p2 ∨ True)) ∧ p5) ∨ p5) ∨ ((p1 → ((p4 ∨ p4) ∨ (p4 ∨ ((p3 ∧ (p5 ∨ True)) ∧ (p3 ∧ p2))))) → (True ∧ True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_59521725640300281009814418324 : (((p2 → p3) ∨ ((((p3 ∨ p2) ∨ p3) ∧ p1) → (False ∨ ((p4 ∧ ((p3 → ((p3 ∧ p5) ∧ p1)) ∨ (p2 ∨ (p1 ∨ True)))) ∨ p1)))) ∨ p4) := by
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
    -- Disjunctions on the left can always be decomposed.
    cases h4
    case inl h5 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- One of the premise coincides with the conclusion.
      exact h3
    case inr h6 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- One of the premise coincides with the conclusion.
      exact h3
  case inr h7 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h3



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_806148908416857997942193943889 : (((p4 → (((((p5 → (False ∨ (p5 → (((False → False) → (p4 ∨ p3)) ∧ p4)))) → False) ∧ ((p5 ∧ False) ∨ (p2 ∧ True))) ∧ False) ∨ True)) ∨ p4) ∧ True) := by
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
theorem thm_5_vars_18138016026291794482478653087 : ((((((p4 → (p2 ∧ ((p4 → (((p1 ∨ (p5 → p3)) ∧ p3) → p2)) → p4))) ∨ p1) ∨ p5) ∧ p4) → ((p4 → p5) ∨ (p4 ∨ p5))) ∧ True) := by
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
    -- Disjunctions on the left can always be decomposed.
    cases h4
    case inl h5 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- One of the premise coincides with the conclusion.
      exact h3
    case inr h6 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- One of the premise coincides with the conclusion.
      exact h3
  case inr h7 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- One of the premise coincides with the conclusion.
    exact h3
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_311018588576363586684875313540 : (p2 ∨ ((True ∧ p5) ∨ (((((p1 ∨ p3) ∨ p4) → (p1 → p5)) ∧ (True ∧ (((p4 ∧ ((p2 → p5) ∧ p2)) ∨ (True ∨ p4)) ∨ p1))) ∨ True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_677620462355062475296305208909 : ((((((p5 ∨ (p1 ∧ ((False ∧ False) ∨ (((False ∧ (p5 ∧ p3)) → p2) ∨ (p4 ∧ p2))))) ∨ p4) → p4) ∨ (False ∧ (p2 ∨ (p5 ∧ p2)))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_264018902727679706725782906473 : (True ∧ ((p1 ∧ (((p3 ∧ ((False ∧ p1) ∧ (p5 ∨ p5))) → p3) ∧ True)) → ((((True ∧ True) ∧ False) ∨ ((p5 → (p5 ∧ p5)) → False)) ∨ True))) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- Conjunctions on the left can always be decomposed.
  let h4 := h3.left
  let h5 := h3.right
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_159649012361271655104767714841 : ((((p1 → (((((p5 → ((p3 ∧ p1) ∨ (False ∨ True))) ∨ p2) → p5) ∧ True) ∧ p5)) ∨ p3) ∨ p3) → (False ∨ (p5 ∨ ((p1 → p5) ∨ p3)))) := by
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
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- Implications on the right can always be decomposed.
      intro h4
      -- We want to use the implication h3 based on <expert-advice>. So we show its premise.
      have h5 : p1 := by
        -- One of the premise coincides with the conclusion.
        exact h4
      -- We have shown the premise of h3, we can now drive its conclusion.
      let h6 := h3 h5
      -- We need to get the right conjuct of h6 based on <expert-advice>.
      let h7 := h6.right
      -- One of the premise coincides with the conclusion.
      exact h7
    case inr h8 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- One of the premise coincides with the conclusion.
      exact h8
  case inr h9 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h9



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_594777395474657845916815314056 : (((((False → ((p3 ∨ ((((p3 ∨ p1) ∧ p4) ∧ p3) ∧ True)) ∧ (p5 → (p3 ∧ False)))) → (((p5 ∨ p2) ∧ p5) ∧ (p1 → p2))) ∧ True) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_310114212383361590128076044915 : (p2 ∨ (((((p1 ∧ (p5 ∨ p2)) ∧ p4) ∨ (p4 → ((False → p4) ∧ p4))) ∨ p4) ∨ (p2 ∨ (((p1 ∧ (p5 ∨ (p2 → p1))) ∨ False) ∧ False)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
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
  -- Implications on the right can always be decomposed.
  intro h2
  -- False on the left can always be used.
  apply False.elim h2
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_313235922592053358420389854127 : (p3 ∨ (((False ∧ p1) ∨ (((p3 ∨ p3) → (p3 → ((p3 ∧ ((p2 ∨ p5) → ((p3 → p4) → p2))) ∧ (p2 ∧ (p4 ∧ True))))) ∨ True)) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_56034043874020641138511199853 : ((((p2 ∨ (p1 → p5)) ∨ p1) ∨ ((((((p1 ∨ (p1 → False)) ∨ True) ∨ p1) → p2) ∨ (((False ∧ p2) → False) → (p1 ∨ p5))) ∧ p4)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_157731974137552995951142751041 : (((p4 ∨ (p1 ∧ (((True ∨ (p4 → (p5 ∨ (True ∨ p3)))) ∨ True) ∧ True))) → (p5 → (p1 → p4))) ∨ ((p4 → p4) ∧ ((True ∨ p2) ∨ p4))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h1
  -- One of the premise coincides with the conclusion.
  exact h1
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_305491408104661439748872462743 : (p1 ∨ (((((True ∧ p1) ∧ p5) → ((p5 ∨ (True ∨ p1)) → (False ∧ False))) ∨ p3) ∨ ((p2 → True) ∨ (p5 → (p2 → ((p3 ∧ p5) → p1)))))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_40943102049671454337117173845 : (((((((((p5 ∨ p4) ∨ p3) → ((False ∧ (p3 ∧ True)) → p2)) → p5) ∨ (((p1 ∧ p2) ∧ p5) ∧ p2)) → False) ∨ (p4 → p5)) ∨ p5) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_353857947283057199737938573603 : (p4 → (p1 → ((p4 ∨ (((p3 ∨ (p2 → True)) → ((p5 ∧ (p5 ∨ p3)) ∧ p1)) → p4)) → ((p5 ∧ p2) ∨ (False → ((True → p5) ∧ p2)))))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Implications on the right can always be decomposed.
  intro h3
  -- Disjunctions on the left can always be decomposed.
  cases h3
  case inl h4 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h5
    -- Conjunctions on the right can always be decomposed.
    apply And.intro
    -- Implications on the right can always be decomposed.
    intro h6
    -- False on the left can always be used.
    apply False.elim h5
    -- False on the left can always be used.
    apply False.elim h5
  case inr h7 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h8
    -- Conjunctions on the right can always be decomposed.
    apply And.intro
    -- Implications on the right can always be decomposed.
    intro h9
    -- False on the left can always be used.
    apply False.elim h8
    -- False on the left can always be used.
    apply False.elim h8



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_116617554228943656546235331537 : (((False → p1) ∧ ((p2 ∧ ((p3 → p2) → ((p1 ∨ (False ∧ p5)) ∧ ((False ∨ ((p5 ∨ True) ∨ False)) ∨ (p5 ∧ True))))) ∧ p3)) ∨ (p4 → True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_803410609693264293989272846331 : (((p3 → ((p5 ∨ ((((True ∨ p1) ∨ True) ∧ (p2 ∨ True)) ∧ (((((p4 ∨ True) ∧ (p3 ∨ False)) ∧ p5) → True) → (p3 → False)))) ∨ True)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_112985981363941796301909520278 : (((p2 ∧ (p4 ∧ ((p2 ∨ ((((False ∨ p1) → p5) ∧ p1) ∧ p3)) ∨ ((True ∧ p2) ∨ (((False → False) ∧ p5) ∨ p5))))) → False) ∨ (p3 ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_314419392079624354887514812540 : (p3 ∨ (((((((True ∨ p2) → p2) ∧ (p4 → (p1 ∨ p1))) → p1) ∨ p5) ∧ ((True → (p5 → p5)) → p3)) ∨ ((p4 ∧ False) → (p2 ∨ p3)))) := by
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
theorem thm_5_vars_39224931220109397151473311486 : (((True ∧ (p1 ∧ (p4 ∨ ((p2 → ((True → (p2 ∧ (p4 → p4))) → ((p2 ∨ p2) ∨ (p2 ∧ (True → (p5 ∨ p1)))))) → False)))) ∧ p5) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_321048784026362147805622422962 : (p4 ∨ (p1 ∨ (((((p2 ∨ ((False ∧ False) → ((p4 ∧ (False → True)) → (((True ∨ False) ∧ p2) ∨ p4)))) ∧ p1) ∧ (p1 → p2)) ∨ p5) ∨ True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_204406693377011895076247857497 : (((p2 → ((p3 → p4) → p2)) ∧ p5) ∨ (((p4 ∨ p3) ∨ (p5 ∧ ((p5 ∨ ((p1 ∨ p5) → (p5 ∨ ((p5 → p1) ∧ p1)))) → p4))) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_148109206641953542590474874263 : (((((p3 → (p4 → (p5 → p3))) ∧ ((p1 ∨ p3) ∧ p3)) ∧ ((p3 ∨ (True ∨ p1)) ∨ p5)) → (p2 ∨ p2)) ∨ (p2 ∨ ((p2 → p2) ∨ True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_117413898459736950534802665550 : ((p1 ∧ ((((((((p3 → p1) → False) ∧ p5) → p2) ∧ p2) ∧ (p5 ∨ p3)) ∨ (True ∨ ((True ∧ p3) → p2))) ∧ (p4 ∨ p1))) ∨ (False → True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_350162077129642791213956870352 : (p4 → (((p3 ∨ ((p1 ∨ p1) ∨ (p3 ∨ (p2 ∧ p4)))) ∨ ((((((True ∨ p4) ∧ p3) ∧ p2) ∨ p1) → (False ∨ (False ∨ p1))) ∧ p3)) ∨ True)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_198353216762964953689346995623 : ((p2 ∧ (p2 ∧ (p1 ∧ ((p4 ∨ p1) → p4)))) ∨ (p4 ∨ (((((True ∧ (False ∧ p5)) → p1) ∨ False) ∧ p3) ∨ (False → (p4 → (True → p2)))))) := by
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
  -- Implications on the right can always be decomposed.
  intro h3
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_115099268894011521176480997199 : ((((((p3 ∧ (p2 ∨ p2)) → p5) ∧ (p3 → (False ∨ True))) ∧ p2) → ((p5 → (p2 ∧ (False ∨ p5))) ∧ (p5 → (p1 ∨ p2)))) ∨ (p2 ∧ p2)) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h2
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Conjunctions on the left can always be decomposed.
  let h3 := h1.left
  let h4 := h1.right
  -- Conjunctions on the left can always be decomposed.
  let h5 := h3.left
  let h6 := h3.right
  -- One of the premise coincides with the conclusion.
  exact h4
  -- Conjunctions on the left can always be decomposed.
  let h7 := h1.left
  let h8 := h1.right
  -- Conjunctions on the left can always be decomposed.
  let h9 := h7.left
  let h10 := h7.right
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h2
  -- Implications on the right can always be decomposed.
  intro h11
  -- Conjunctions on the left can always be decomposed.
  let h12 := h1.left
  let h13 := h1.right
  -- Conjunctions on the left can always be decomposed.
  let h14 := h12.left
  let h15 := h12.right
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h13



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_303067769340834738302234144123 : (False ∨ (p2 → ((p3 → (((p5 ∧ False) ∨ p5) ∧ (p2 ∧ (p1 ∧ p1)))) → (((p3 ∧ (p1 ∧ p3)) → (False ∧ (p4 ∨ p1))) ∨ (p3 → p3))))) := by
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
theorem thm_5_vars_140123057343615839431203345605 : ((((((p4 → p2) ∧ (((p4 ∨ False) ∧ False) → ((p4 ∧ True) ∨ (False ∧ (True → p5))))) → p5) ∧ False) → (p2 → p1)) → (p1 → (p2 ∨ True))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_179572568145505503586880773623 : ((p2 → ((p2 ∨ (p4 → p2)) → (p5 ∨ ((p3 ∨ (p3 → False)) ∨ True)))) ∨ (p2 ∨ ((False ∧ (((p2 ∨ (p3 ∧ p4)) ∧ p1) ∧ p5)) ∨ True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_140780192346333878106227295945 : ((((((False ∨ ((p5 ∧ p4) ∨ False)) → (p5 ∧ p2)) → False) → p5) ∧ (((p1 ∧ False) → ((p4 → p5) ∨ p4)) → p3)) → (True → (p2 → p2))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Implications on the right can always be decomposed.
  intro h3
  -- Conjunctions on the left can always be decomposed.
  let h4 := h1.left
  let h5 := h1.right
  -- One of the premise coincides with the conclusion.
  exact h3



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_230903121499334909837343310389 : (((p2 ∧ p4) ∨ True) → (((((((((True ∨ p4) ∨ p1) ∧ (p5 ∧ p4)) → False) → (p4 ∨ ((p1 ∨ p3) ∧ p4))) ∧ p5) ∧ p4) ∧ True) ∨ True)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h2 =>
    -- Conjunctions on the left can always be decomposed.
    let h3 := h2.left
    let h4 := h2.right
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro
  case inr h5 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_950041652455327212063884978048 : (((((True ∨ p1) → False) ∧ ((p1 ∨ (p1 ∨ p5)) ∨ (p2 ∧ ((((p2 → p2) ∧ (p1 → p1)) ∨ (True → p3)) → (p2 ∨ (p2 ∧ p5)))))) → False) ∧ True) := by
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
    -- Disjunctions on the left can always be decomposed.
    cases h4
    case inl h5 =>
      -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
      have h6 : (True ∨ p1) := by
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- True on the right can always be proven directly.
        apply True.intro
      -- We have shown the premise of h2, we can now drive its conclusion.
      let h7 := h2 h6
      -- False on the left can always be used.
      apply False.elim h7
    case inr h8 =>
      -- Disjunctions on the left can always be decomposed.
      cases h8
      case inl h9 =>
        -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
        have h10 : (True ∨ p1) := by
          -- Show the left disjunct based on <expert-advice>.
          apply Or.inl
          -- True on the right can always be proven directly.
          apply True.intro
        -- We have shown the premise of h2, we can now drive its conclusion.
        let h11 := h2 h10
        -- False on the left can always be used.
        apply False.elim h11
      case inr h12 =>
        -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
        have h13 : (True ∨ p1) := by
          -- Show the left disjunct based on <expert-advice>.
          apply Or.inl
          -- True on the right can always be proven directly.
          apply True.intro
        -- We have shown the premise of h2, we can now drive its conclusion.
        let h14 := h2 h13
        -- False on the left can always be used.
        apply False.elim h14
  case inr h15 =>
    -- Conjunctions on the left can always be decomposed.
    let h16 := h15.left
    let h17 := h15.right
    -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
    have h18 : (True ∨ p1) := by
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- True on the right can always be proven directly.
      apply True.intro
    -- We have shown the premise of h2, we can now drive its conclusion.
    let h19 := h2 h18
    -- False on the left can always be used.
    apply False.elim h19
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_247972598899566123253666770628 : ((p1 ∨ p4) ∨ ((((p4 → p4) → (False ∧ p1)) ∧ (p1 ∨ (True → ((False → ((p5 ∨ False) ∧ False)) ∧ False)))) → (p5 ∧ (p4 ∨ (False → True))))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- Disjunctions on the left can always be decomposed.
  cases h3
  case inl h4 =>
    -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
    have h5 : (p4 → p4) := by
      -- Implications on the right can always be decomposed.
      intro h6
      -- One of the premise coincides with the conclusion.
      exact h6
    -- We have shown the premise of h2, we can now drive its conclusion.
    let h7 := h2 h5
    -- We need to get the left conjuct of h7 based on <expert-advice>.
    let h8 := h7.left
    -- False on the left can always be used.
    apply False.elim h8
  case inr h9 =>
    -- We want to use the implication h9 based on <expert-advice>. So we show its premise.
    have h10 : True := by
      -- True on the right can always be proven directly.
      apply True.intro
    -- We have shown the premise of h9, we can now drive its conclusion.
    let h11 := h9 h10
    -- We need to get the right conjuct of h11 based on <expert-advice>.
    let h12 := h11.right
    -- False on the left can always be used.
    apply False.elim h12
  -- Conjunctions on the left can always be decomposed.
  let h13 := h1.left
  let h14 := h1.right
  -- Disjunctions on the left can always be decomposed.
  cases h14
  case inl h15 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h16
    -- True on the right can always be proven directly.
    apply True.intro
  case inr h17 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h18
    -- True on the right can always be proven directly.
    apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_171706533194282773831031450521 : (((p4 → (((p2 ∨ p3) ∨ ((p4 ∨ ((p1 ∧ p5) ∧ False)) ∧ p2)) ∧ True)) ∨ True) ∨ (((p4 → p5) → (p2 → ((p3 → True) ∧ True))) ∧ True)) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_300554526081343907367540714822 : (False ∨ (((((True ∧ p1) ∧ p1) → (p1 → (True ∨ p4))) → ((p1 ∨ p4) → ((p2 ∨ (p2 ∨ p1)) ∧ p5))) ∨ (p2 ∨ (True ∨ (p4 ∧ p2))))) := by
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
theorem thm_5_vars_58770076908771131098454733432 : (((p4 → p2) ∧ (True → ((((True → (p1 → p3)) ∧ p4) → p3) → ((((p1 ∨ (p2 → False)) ∧ (p5 ∧ p3)) ∧ (p2 → p2)) ∨ p5)))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_51276339228884804943279298539 : (((False ∧ ((p3 ∨ p5) ∨ (False ∧ ((p1 ∨ (p2 → ((p5 → p1) ∨ (p2 → p1)))) → p1)))) ∨ (((p3 ∧ (p1 → p1)) ∧ p4) → True)) ∨ p2) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_172411916816122070161719301461 : (((((False → p4) ∨ p3) ∨ p3) ∧ (((False ∧ p1) → True) → (p5 → (p2 ∧ p4)))) ∨ ((((p1 → p4) → p5) ∧ (p2 ∧ (p2 → p2))) → True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_325675410588214636295525194666 : (p5 ∨ (p1 ∨ ((p1 ∧ (False ∧ (((True ∨ ((p1 ∨ p1) ∧ (p2 ∧ False))) → ((((p5 ∧ (True ∨ p3)) ∧ p5) ∨ p1) → False)) → p3))) ∨ True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_830723564868789030089279866475 : ((((True → (((True ∧ ((p2 → ((True ∨ ((False ∧ p2) → (True → (p5 → p3)))) ∨ p1)) ∨ (p3 ∧ p1))) ∧ (True ∨ p4)) ∧ False)) ∧ p4) → p3) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
  have h4 : True := by
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h2, we can now drive its conclusion.
  let h5 := h2 h4
  -- We need to get the right conjuct of h5 based on <expert-advice>.
  let h6 := h5.right
  -- False on the left can always be used.
  apply False.elim h6
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_302786032366716369222113201833 : (False ∨ (p4 ∨ (p4 ∨ ((((p4 ∨ p3) ∨ True) ∨ ((p4 ∧ (((p4 ∧ (p1 → (True → (p3 → False)))) → p5) ∧ False)) → (p5 ∧ p2))) ∧ True)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
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
theorem thm_5_vars_204171385276485012373211286783 : ((((p3 ∧ (p4 ∧ p1)) ∨ False) ∧ p5) ∨ (((p1 → ((p4 ∧ True) ∧ p2)) → (p5 → ((((False → p3) ∧ (p5 ∨ False)) ∨ p2) ∧ True))) ∧ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
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
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- One of the premise coincides with the conclusion.
  exact h2
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_352503127849892021813616339670 : (p4 → ((True ∧ True) ∧ ((p4 ∧ (((p3 → ((False → (p4 → p3)) → (p5 ∨ (True ∧ False)))) ∨ p4) ∨ ((p2 → p2) ∨ (False ∨ p3)))) ∨ p2))) := by
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
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- One of the premise coincides with the conclusion.
  exact h1
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_767383043576913408700134158156 : (((p5 ∧ ((False ∧ (False ∨ (((p5 ∧ p5) ∧ (((True → p3) → (True ∧ False)) ∧ p1)) ∨ (p3 ∧ (((p3 ∨ p4) ∨ p5) ∧ False))))) ∧ p4)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_111253841021377996765887350716 : ((((p5 ∧ False) ∨ ((p3 ∨ ((p4 ∨ ((p4 → False) ∧ p5)) → (p4 ∧ p1))) → (((True ∨ p3) → p1) → (p1 → p1)))) ∧ p5) ∨ (True ∨ p1)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_600367589085430601077604941980 : ((((True ∧ (((p2 → ((((p3 → p4) ∨ False) ∨ (p1 ∧ False)) ∨ p3)) → (p3 → (p2 ∧ ((p1 ∧ (True ∧ p4)) → p3)))) ∨ True)) ∧ p1) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_593013236236030712340278806255 : ((((((((p2 ∨ p1) ∧ p1) ∧ ((((((p5 → p1) ∨ (p1 → p2)) ∨ p2) → p3) → p2) ∨ p3)) ∧ p1) ∨ ((p4 → True) → True)) ∧ True) ∨ p1) ∧ True) := by
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
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_205185633161772340568014574146 : (((p4 ∨ (False ∧ True)) ∧ (p1 ∧ p3)) ∨ (((p1 ∧ p1) ∧ ((p4 ∧ ((((False ∧ (False → True)) ∨ p5) ∨ p1) ∨ p3)) ∨ p4)) ∨ (True ∨ p4))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_776051625568666544861653733942 : (((False ∨ (p4 → ((False → (p3 → p4)) → (p5 → (((p1 ∧ p3) ∨ p5) ∧ (p3 ∨ (p3 ∨ ((p1 ∧ False) ∨ ((p1 ∨ p3) → p4))))))))) ∨ False) ∧ True) := by
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
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h3
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h4
  -- Disjunctions on the left can always be decomposed.
  cases h4
  case inl h5 =>
    -- One of the premise coincides with the conclusion.
    exact h1
  case inr h6 =>
    -- One of the premise coincides with the conclusion.
    exact h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_171835455887172970403067512872 : ((((p1 → (p3 → p2)) ∨ (((False → (p5 ∨ (p5 ∧ False))) ∧ True) ∧ p5)) → False) ∨ ((False → True) ∨ (p4 ∧ ((True ∧ p3) → (p4 ∨ True))))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_322570359590489906493701414073 : (p5 ∨ ((p3 ∨ (True → ((((p4 ∧ p5) ∧ ((p5 ∧ (p5 ∨ (p1 ∧ p4))) ∧ False)) ∧ p1) ∨ ((p3 ∨ p5) ∨ ((p4 ∧ p4) → False))))) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_42432131181829033053604423484 : (((p5 ∧ ((True → (False ∧ p1)) → ((p2 ∧ (p2 → (p5 ∧ (p3 → False)))) ∨ (p4 ∨ ((p2 ∨ p4) → (p4 ∨ (False ∧ p4))))))) ∨ True) ∨ p3) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_159918292697559902589159994351 : (((((((p5 ∨ (((True → p5) ∨ p1) ∨ p1)) → (p3 → True)) → (p4 ∧ True)) → p2) → p2) → False) → ((p3 ∧ (True → p2)) → (p5 ∧ True))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Conjunctions on the left can always be decomposed.
  let h3 := h2.left
  let h4 := h2.right
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h5 : (((((p5 ∨ (((True → p5) ∨ p1) ∨ p1)) → (p3 → True)) → (p4 ∧ True)) → p2) → p2) := by
    -- Implications on the right can always be decomposed.
    intro h6
    -- We want to use the implication h4 based on <expert-advice>. So we show its premise.
    have h7 : True := by
      -- True on the right can always be proven directly.
      apply True.intro
    -- We have shown the premise of h4, we can now drive its conclusion.
    let h8 := h4 h7
    -- One of the premise coincides with the conclusion.
    exact h8
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h9 := h1 h5
  -- False on the left can always be used.
  apply False.elim h9
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_49631592116117772819166666250 : ((((((p3 ∨ (p2 → True)) ∨ p2) ∧ p1) → ((False ∧ (p1 → (((p1 ∨ p4) → p3) ∨ p1))) → (p5 → p2))) → ((p4 ∧ p2) → p1)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_322411701674266721259515332035 : (p5 ∨ (((p1 → (((True → False) → p5) → ((True → False) → True))) ∧ (((p2 ∨ (True ∧ (p4 ∧ True))) ∨ ((p2 ∨ p5) ∧ p2)) ∧ False)) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_172935512772775327851165202283 : ((p3 ∧ (((p4 ∧ ((p1 ∧ (False → p1)) ∧ (True ∨ p3))) ∨ True) → (p3 ∧ p4))) ∨ (((True ∧ True) ∨ True) ∨ ((p3 → True) ∨ (False ∨ p4)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



