variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_197990738124642871607226090305 : (((p4 ∨ p3) ∧ (True ∧ ((p2 ∧ p4) ∨ p3))) ∨ ((((((p2 ∧ p3) ∨ (p1 → p1)) ∨ p2) → False) ∧ ((p1 ∧ p4) ∧ (p3 ∧ p1))) → p3)) := by
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
  let h6 := h4.left
  let h7 := h4.right
  -- Conjunctions on the left can always be decomposed.
  let h8 := h5.left
  let h9 := h5.right
  -- One of the premise coincides with the conclusion.
  exact h8



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_166253459203969987796739355920 : ((p3 ∧ ((((True ∨ p2) → (p2 ∨ (p4 → False))) ∨ ((True ∧ p3) ∧ True)) ∧ (p3 ∨ False))) ∨ ((p5 → (False ∧ (p4 → (p1 → p3)))) → True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_16800357398406854962315173800 : ((((((True ∨ True) ∧ p1) → (p3 ∨ p2)) ∧ ((p3 → p3) → (((p3 ∨ (p5 → p3)) → True) → (p2 ∧ p4)))) ∨ (True ∨ (False ∧ p5))) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_300234469968759186757981110329 : (False ∨ ((((p1 → (p1 ∧ False)) → p5) ∧ (True → (p5 → ((False ∨ True) → (((p2 ∨ (True ∧ p5)) ∧ False) ∧ (True ∨ p1)))))) → (p5 → p1))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Conjunctions on the left can always be decomposed.
  let h3 := h1.left
  let h4 := h1.right
  -- We want to use the implication h4 based on <expert-advice>. So we show its premise.
  have h5 : True := by
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h4, we can now drive its conclusion.
  let h6 := h4 h5
  -- We want to use the implication h6 based on <expert-advice>. So we show its premise.
  have h7 : p5 := by
    -- One of the premise coincides with the conclusion.
    exact h2
  -- We have shown the premise of h6, we can now drive its conclusion.
  let h8 := h6 h7
  -- We want to use the implication h8 based on <expert-advice>. So we show its premise.
  have h9 : (False ∨ True) := by
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h8, we can now drive its conclusion.
  let h10 := h8 h9
  -- We need to get the left conjuct of h10 based on <expert-advice>.
  let h11 := h10.left
  -- We need to get the right conjuct of h11 based on <expert-advice>.
  let h12 := h11.right
  -- False on the left can always be used.
  apply False.elim h12



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_151296859837126285450217483767 : (((False ∨ (((p1 ∧ ((False ∧ p4) ∧ (((True ∧ (p5 ∨ p3)) → p3) → True))) ∧ (p5 ∨ p2)) → p2)) → False) → (((False ∧ False) ∧ p5) ∧ p3)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h2 : (False ∨ (((p1 ∧ ((False ∧ p4) ∧ (((True ∧ (p5 ∨ p3)) → p3) → True))) ∧ (p5 ∨ p2)) → p2)) := by
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
    -- Conjunctions on the left can always be decomposed.
    let h8 := h7.left
    let h9 := h7.right
    -- Conjunctions on the left can always be decomposed.
    let h10 := h8.left
    let h11 := h8.right
    -- False on the left can always be used.
    apply False.elim h10
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h12 := h1 h2
  -- False on the left can always be used.
  apply False.elim h12
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h13 : (False ∨ (((p1 ∧ ((False ∧ p4) ∧ (((True ∧ (p5 ∨ p3)) → p3) → True))) ∧ (p5 ∨ p2)) → p2)) := by
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h14
    -- Conjunctions on the left can always be decomposed.
    let h15 := h14.left
    let h16 := h14.right
    -- Conjunctions on the left can always be decomposed.
    let h17 := h15.left
    let h18 := h15.right
    -- Conjunctions on the left can always be decomposed.
    let h19 := h18.left
    let h20 := h18.right
    -- Conjunctions on the left can always be decomposed.
    let h21 := h19.left
    let h22 := h19.right
    -- False on the left can always be used.
    apply False.elim h21
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h23 := h1 h13
  -- False on the left can always be used.
  apply False.elim h23
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h24 : (False ∨ (((p1 ∧ ((False ∧ p4) ∧ (((True ∧ (p5 ∨ p3)) → p3) → True))) ∧ (p5 ∨ p2)) → p2)) := by
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h25
    -- Conjunctions on the left can always be decomposed.
    let h26 := h25.left
    let h27 := h25.right
    -- Conjunctions on the left can always be decomposed.
    let h28 := h26.left
    let h29 := h26.right
    -- Conjunctions on the left can always be decomposed.
    let h30 := h29.left
    let h31 := h29.right
    -- Conjunctions on the left can always be decomposed.
    let h32 := h30.left
    let h33 := h30.right
    -- False on the left can always be used.
    apply False.elim h32
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h34 := h1 h24
  -- False on the left can always be used.
  apply False.elim h34
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h35 : (False ∨ (((p1 ∧ ((False ∧ p4) ∧ (((True ∧ (p5 ∨ p3)) → p3) → True))) ∧ (p5 ∨ p2)) → p2)) := by
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h36
    -- Conjunctions on the left can always be decomposed.
    let h37 := h36.left
    let h38 := h36.right
    -- Conjunctions on the left can always be decomposed.
    let h39 := h37.left
    let h40 := h37.right
    -- Conjunctions on the left can always be decomposed.
    let h41 := h40.left
    let h42 := h40.right
    -- Conjunctions on the left can always be decomposed.
    let h43 := h41.left
    let h44 := h41.right
    -- False on the left can always be used.
    apply False.elim h43
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h45 := h1 h35
  -- False on the left can always be used.
  apply False.elim h45



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_159313599734255423361154619474 : ((p5 → (((((p5 ∧ p4) → (p2 → False)) ∧ (False ∨ p1)) ∨ (p2 ∧ (p4 → p2))) ∨ (p2 ∧ p1))) ∨ (((p1 → p4) ∨ (p1 → p2)) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_148982621243491183426223589028 : (((p4 ∧ (p4 ∧ True)) ∧ ((True ∧ p3) → (p3 ∧ ((((p2 ∨ (p1 → p5)) → True) ∧ p1) ∧ (p5 → p2))))) ∨ (((False ∧ p1) ∨ p5) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_752147181462211405174953052264 : (((True ∧ (p2 → (((p3 ∧ (((p1 ∨ p5) ∧ (p5 ∧ (p5 ∧ p3))) ∧ p4)) ∨ ((p5 → (True ∧ (p1 → p5))) ∨ (p5 ∧ True))) ∨ True))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_324521118556598323568861344046 : (p5 ∨ ((((p1 ∨ p3) ∨ False) ∧ p1) → (((False → p5) → ((((((False → True) → p2) → False) ∨ False) ∨ p4) ∨ (p2 → p1))) ∨ (False ∨ p4)))) := by
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
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- Implications on the right can always be decomposed.
      intro h6
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Implications on the right can always be decomposed.
      intro h7
      -- One of the premise coincides with the conclusion.
      exact h3
    case inr h8 =>
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- Implications on the right can always be decomposed.
      intro h9
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Implications on the right can always be decomposed.
      intro h10
      -- One of the premise coincides with the conclusion.
      exact h3
  case inr h11 =>
    -- False on the left can always be used.
    apply False.elim h11



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_119327603107701111919713335677 : ((p3 → (((p2 ∧ (((p3 ∨ (p1 → p5)) → p4) ∨ p1)) ∨ p1) ∨ (((p5 → False) ∨ ((p1 ∨ (p5 → p2)) ∧ p4)) ∧ p2))) ∨ (p1 ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_48508689968456951530748803821 : (((((True → (p4 ∧ ((p3 ∨ p5) ∧ (p4 ∧ ((True ∨ False) → (((p3 → p5) ∧ p3) → p3)))))) → p5) ∨ p1) ∧ (p3 ∧ (p3 ∨ p2))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_137617298965137343736442989446 : ((False ∨ (((p4 → (False ∧ ((False ∧ p2) ∨ ((p3 → (p5 → ((p2 → p3) → (p5 → p2)))) ∨ p5)))) ∨ False) ∨ True)) ∨ (p4 → (p4 → p4))) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_453229996111022930735289698666 : (((((((False ∨ ((p2 → True) ∨ p2)) ∨ (p2 ∧ True)) → ((p4 ∧ (True ∧ (p4 → p3))) ∧ True)) ∨ p3) → ((p3 ∨ p4) ∧ (p3 ∨ p4))) ∧ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h2 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
    have h3 : ((False ∨ ((p2 → True) ∨ p2)) ∨ (p2 ∧ True)) := by
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- Implications on the right can always be decomposed.
      intro h4
      -- True on the right can always be proven directly.
      apply True.intro
    -- We have shown the premise of h2, we can now drive its conclusion.
    let h5 := h2 h3
    -- We need to get the left conjuct of h5 based on <expert-advice>.
    let h6 := h5.left
    -- We need to get the left conjuct of h6 based on <expert-advice>.
    let h7 := h6.left
    -- One of the premise coincides with the conclusion.
    exact h7
  case inr h8 =>
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- One of the premise coincides with the conclusion.
    exact h8
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h9 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- We want to use the implication h9 based on <expert-advice>. So we show its premise.
    have h10 : ((False ∨ ((p2 → True) ∨ p2)) ∨ (p2 ∧ True)) := by
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- Implications on the right can always be decomposed.
      intro h11
      -- True on the right can always be proven directly.
      apply True.intro
    -- We have shown the premise of h9, we can now drive its conclusion.
    let h12 := h9 h10
    -- We need to get the left conjuct of h12 based on <expert-advice>.
    let h13 := h12.left
    -- We need to get the left conjuct of h13 based on <expert-advice>.
    let h14 := h13.left
    -- One of the premise coincides with the conclusion.
    exact h14
  case inr h15 =>
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- One of the premise coincides with the conclusion.
    exact h15
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_136591929749249026199809982094 : (((False ∨ (p1 → p3)) ∨ ((((p2 → False) → p4) ∧ ((((p5 ∧ p2) ∧ p3) ∧ False) ∨ ((p5 → False) → p5))) ∧ p5)) ∨ ((p4 → p4) ∨ p4)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_197228365733341219422505416806 : ((((p2 → ((p2 ∨ p4) → p5)) ∨ True) → p2) ∨ ((((((False → ((p1 → p4) ∨ False)) ∧ p1) ∨ p5) ∨ True) → (True ∨ False)) ∨ (p4 ∨ False))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
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
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- True on the right can always be proven directly.
      apply True.intro
    case inr h6 =>
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- True on the right can always be proven directly.
      apply True.intro
  case inr h7 =>
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- True on the right can always be proven directly.
    apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_117638004684816771128181066903 : ((p3 ∧ ((((((((((p3 ∧ p3) ∧ False) ∨ p4) ∨ p3) → (p1 → p3)) ∨ p5) ∧ (p4 ∨ p5)) ∧ (p3 ∨ p4)) ∧ True) → False)) ∨ (False → p1)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_134290620510603898774557378577 : ((((p2 → p5) ∨ ((p2 ∨ ((p3 ∧ False) ∨ (p2 ∧ ((((p4 → p4) → p4) ∨ p1) → (p1 ∨ p5))))) ∧ p1)) ∨ p2) ∨ (True ∨ (True → False))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_134836010674807915488161050931 : (((p2 ∨ (p1 → (False → ((True → p5) ∧ ((p3 ∧ ((True ∧ ((p2 → p3) ∨ p4)) → (p4 ∧ False))) ∧ p5))))) → p2) ∨ (p4 → (False ∨ p4))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_117397357359602056318807934216 : ((p1 ∧ ((((p2 ∧ p4) ∧ p4) → (p5 ∨ ((p5 → p1) → (((p1 ∧ (True ∨ (p4 ∧ (p5 ∨ p4)))) ∧ True) ∧ False)))) ∨ p2)) ∨ (False → p3)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_805220771985578175121703434465 : (((p3 → (p3 ∧ ((p3 → p2) ∨ (p5 → (p1 ∨ (True ∧ (p2 ∧ (p3 ∧ (p1 ∨ (True ∧ ((((False ∧ p5) ∨ False) → p1) → p1))))))))))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_47435081233314713711364736750 : (((p2 ∧ ((p3 ∧ p3) ∧ ((p2 ∧ p4) ∧ ((((p2 ∨ ((p4 → p5) ∧ True)) → (p5 ∨ p2)) ∨ True) ∨ (p1 → p1))))) ∨ (p2 → True)) ∨ p3) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_912800131231855012972329008498 : ((((((p1 ∧ p5) ∧ ((p1 ∧ p4) ∧ (p1 ∧ p4))) ∨ ((p3 ∧ (p3 → p1)) → (p1 ∨ False))) → ((p5 → ((p1 ∧ p3) ∧ p2)) ∧ False)) → p5) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h1
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h2 : (((p1 ∧ p5) ∧ ((p1 ∧ p4) ∧ (p1 ∧ p4))) ∨ ((p3 ∧ (p3 → p1)) → (p1 ∨ False))) := by
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h3
    -- Conjunctions on the left can always be decomposed.
    let h4 := h3.left
    let h5 := h3.right
    -- We want to use the implication h5 based on <expert-advice>. So we show its premise.
    have h6 : p3 := by
      -- One of the premise coincides with the conclusion.
      exact h4
    -- We have shown the premise of h5, we can now drive its conclusion.
    let h7 := h5 h6
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- One of the premise coincides with the conclusion.
    exact h7
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h8 := h1 h2
  -- We need to get the right conjuct of h8 based on <expert-advice>.
  let h9 := h8.right
  -- False on the left can always be used.
  apply False.elim h9
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_137235594930027596508307723108 : ((p1 ∧ ((((False → (((p3 ∧ p4) ∨ (p4 → (False → ((p1 ∧ p2) ∧ p5)))) ∨ False)) → p2) ∨ p4) → (False ∧ False))) ∨ (False → (p5 ∨ p4))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_323266402865183888109987198040 : (p5 ∨ ((p2 ∨ (((False → False) ∨ True) → ((False ∨ (p2 ∧ p5)) → (((p4 ∨ False) → (False ∧ p4)) → (p4 → (p5 ∧ False)))))) ∨ (p3 ∨ p3))) := by
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
  -- Implications on the right can always be decomposed.
  intro h3
  -- Implications on the right can always be decomposed.
  intro h4
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Disjunctions on the left can always be decomposed.
  cases h2
  case inl h5 =>
    -- False on the left can always be used.
    apply False.elim h5
  case inr h6 =>
    -- Conjunctions on the left can always be decomposed.
    let h7 := h6.left
    let h8 := h6.right
    -- Disjunctions on the left can always be decomposed.
    cases h1
    case inl h9 =>
      -- One of the premise coincides with the conclusion.
      exact h8
    case inr h10 =>
      -- One of the premise coincides with the conclusion.
      exact h8
  -- Disjunctions on the left can always be decomposed.
  cases h2
  case inl h11 =>
    -- False on the left can always be used.
    apply False.elim h11
  case inr h12 =>
    -- Conjunctions on the left can always be decomposed.
    let h13 := h12.left
    let h14 := h12.right
    -- Disjunctions on the left can always be decomposed.
    cases h1
    case inl h15 =>
      -- We want to use the implication h3 based on <expert-advice>. So we show its premise.
      have h16 : (p4 ∨ False) := by
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- One of the premise coincides with the conclusion.
        exact h4
      -- We have shown the premise of h3, we can now drive its conclusion.
      let h17 := h3 h16
      -- We need to get the left conjuct of h17 based on <expert-advice>.
      let h18 := h17.left
      -- False on the left can always be used.
      apply False.elim h18
    case inr h19 =>
      -- We want to use the implication h3 based on <expert-advice>. So we show its premise.
      have h20 : (p4 ∨ False) := by
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- One of the premise coincides with the conclusion.
        exact h4
      -- We have shown the premise of h3, we can now drive its conclusion.
      let h21 := h3 h20
      -- We need to get the left conjuct of h21 based on <expert-advice>.
      let h22 := h21.left
      -- False on the left can always be used.
      apply False.elim h22



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_40127999146645834637564001667 : (((((p3 ∧ ((p2 ∨ p4) ∨ (((((p5 → (p4 ∨ (p3 ∨ True))) ∧ p2) → True) ∧ p5) ∧ False))) ∨ (False ∧ (p5 ∨ p4))) ∧ False) ∨ True) ∨ p1) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_115082406135360928965474030846 : (((p4 ∧ (p4 ∧ (((p4 → p5) ∧ p2) → (p4 ∨ (p2 ∨ p5))))) ∨ (p5 ∧ ((((p3 ∧ p2) ∨ False) ∧ (p5 ∨ p3)) ∧ p2))) ∨ (True ∨ False)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_42243159073549713318535514426 : (((False ∧ (False ∨ (p5 ∧ (p4 → (((True ∨ (False ∨ (p2 → ((False ∧ p1) ∨ False)))) ∨ (p2 ∨ (p3 ∧ (False ∨ p1)))) → p3))))) ∨ True) ∨ p1) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_174743648181077078982225140129 : (((p4 ∧ (False → p4)) → ((p3 ∨ ((False → p3) → p2)) ∨ ((False ∨ p4) ∨ p3))) → ((False → False) → ((p2 ∧ False) ∨ (False → (p3 ∧ True))))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h3
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- False on the left can always be used.
  apply False.elim h3
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_45680156695583275300197770441 : (((p5 ∨ ((((p5 → False) ∧ (p2 → p2)) ∨ p4) → (False ∨ ((p2 ∨ p4) ∧ (((p1 ∨ (p5 ∨ p3)) → (False ∨ True)) → p1))))) → p2) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_193860196826153952965889287311 : ((True ∨ (p4 ∧ ((p3 → (p5 → True)) ∧ (p3 → p2)))) → ((p5 ∧ p2) → (((p3 ∧ (p1 → (p3 → (p5 → p2)))) ∨ p2) ∨ (True ∧ True)))) := by
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
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Conjunctions on the right can always be decomposed.
    apply And.intro
    -- True on the right can always be proven directly.
    apply True.intro
    -- True on the right can always be proven directly.
    apply True.intro
  case inr h6 =>
    -- Conjunctions on the left can always be decomposed.
    let h7 := h6.left
    let h8 := h6.right
    -- Conjunctions on the left can always be decomposed.
    let h9 := h8.left
    let h10 := h8.right
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Conjunctions on the right can always be decomposed.
    apply And.intro
    -- True on the right can always be proven directly.
    apply True.intro
    -- True on the right can always be proven directly.
    apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_343634035041449436434453415255 : (p2 → (True ∧ (((((False ∨ p4) → (((p2 ∨ p2) ∧ p4) ∧ p2)) ∨ (p2 ∧ p3)) → ((True ∨ (True ∧ True)) → p4)) ∨ ((p3 ∨ p5) ∨ p2)))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_214202268976655181153035508201 : ((((True → p4) → p5) → p2) ∨ ((p1 ∨ (((False ∧ (p3 ∨ ((p2 ∧ p5) ∨ p2))) ∨ (p1 → (True ∧ True))) → (p2 ∨ p2))) ∨ (p3 ∨ True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_67331868386392185793632871036 : ((p1 → (((p1 → ((p3 → ((True ∨ (p3 → (p1 ∨ True))) ∧ (True → (p2 ∧ (p3 ∧ p3))))) ∧ ((p4 ∧ p1) ∨ p5))) → p4) ∨ p5)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_64189990042503061997659117423 : ((False ∨ (True ∧ (((((p3 ∨ (p2 ∧ p2)) ∧ p4) ∧ ((True ∧ p4) ∧ ((p5 ∨ (p5 ∧ True)) → False))) ∨ True) ∨ ((True ∨ p1) ∧ p3)))) ∨ p4) := by
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
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_692018191200109253590948106304 : ((((((p2 → (((p3 ∨ (False → (p3 → p1))) → p5) → p3)) ∨ p2) ∧ p3) ∧ (((p4 ∨ (p3 ∧ (p5 ∧ p4))) ∧ (p4 → False)) ∧ p2)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_134528415857948246160716836661 : ((((((p5 ∧ (((p3 → p2) ∨ (p3 → p1)) ∧ (p3 ∧ (False ∨ (p3 ∧ p4))))) ∧ (True → p5)) ∨ True) → p2) → p2) ∨ ((True → False) → p3)) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h2 : (((p5 ∧ (((p3 → p2) ∨ (p3 → p1)) ∧ (p3 ∧ (False ∨ (p3 ∧ p4))))) ∧ (True → p5)) ∨ True) := by
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h3 := h1 h2
  -- One of the premise coincides with the conclusion.
  exact h3



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_207562046282486305910282758337 : (((((p2 ∧ True) → p3) ∨ p4) → False) → ((p3 ∨ p3) → (((p2 → (False ∧ ((False → p1) ∧ p1))) ∧ (p5 → (p2 ∧ (False ∨ p5)))) ∧ p4))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h3
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Disjunctions on the left can always be decomposed.
  cases h2
  case inl h4 =>
    -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
    have h5 : (((p2 ∧ True) → p3) ∨ p4) := by
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- Implications on the right can always be decomposed.
      intro h6
      -- Conjunctions on the left can always be decomposed.
      let h7 := h6.left
      let h8 := h6.right
      -- One of the premise coincides with the conclusion.
      exact h4
    -- We have shown the premise of h1, we can now drive its conclusion.
    let h9 := h1 h5
    -- False on the left can always be used.
    apply False.elim h9
  case inr h10 =>
    -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
    have h11 : (((p2 ∧ True) → p3) ∨ p4) := by
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- Implications on the right can always be decomposed.
      intro h12
      -- Conjunctions on the left can always be decomposed.
      let h13 := h12.left
      let h14 := h12.right
      -- One of the premise coincides with the conclusion.
      exact h10
    -- We have shown the premise of h1, we can now drive its conclusion.
    let h15 := h1 h11
    -- False on the left can always be used.
    apply False.elim h15
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h16
  -- False on the left can always be used.
  apply False.elim h16
  -- Disjunctions on the left can always be decomposed.
  cases h2
  case inl h17 =>
    -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
    have h18 : (((p2 ∧ True) → p3) ∨ p4) := by
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- Implications on the right can always be decomposed.
      intro h19
      -- Conjunctions on the left can always be decomposed.
      let h20 := h19.left
      let h21 := h19.right
      -- One of the premise coincides with the conclusion.
      exact h17
    -- We have shown the premise of h1, we can now drive its conclusion.
    let h22 := h1 h18
    -- False on the left can always be used.
    apply False.elim h22
  case inr h23 =>
    -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
    have h24 : (((p2 ∧ True) → p3) ∨ p4) := by
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- Implications on the right can always be decomposed.
      intro h25
      -- Conjunctions on the left can always be decomposed.
      let h26 := h25.left
      let h27 := h25.right
      -- One of the premise coincides with the conclusion.
      exact h23
    -- We have shown the premise of h1, we can now drive its conclusion.
    let h28 := h1 h24
    -- False on the left can always be used.
    apply False.elim h28
  -- Implications on the right can always be decomposed.
  intro h29
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Disjunctions on the left can always be decomposed.
  cases h2
  case inl h30 =>
    -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
    have h31 : (((p2 ∧ True) → p3) ∨ p4) := by
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- Implications on the right can always be decomposed.
      intro h32
      -- Conjunctions on the left can always be decomposed.
      let h33 := h32.left
      let h34 := h32.right
      -- One of the premise coincides with the conclusion.
      exact h30
    -- We have shown the premise of h1, we can now drive its conclusion.
    let h35 := h1 h31
    -- False on the left can always be used.
    apply False.elim h35
  case inr h36 =>
    -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
    have h37 : (((p2 ∧ True) → p3) ∨ p4) := by
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- Implications on the right can always be decomposed.
      intro h38
      -- Conjunctions on the left can always be decomposed.
      let h39 := h38.left
      let h40 := h38.right
      -- One of the premise coincides with the conclusion.
      exact h36
    -- We have shown the premise of h1, we can now drive its conclusion.
    let h41 := h1 h37
    -- False on the left can always be used.
    apply False.elim h41
  -- Disjunctions on the left can always be decomposed.
  cases h2
  case inl h42 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h29
  case inr h43 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h29
  -- Disjunctions on the left can always be decomposed.
  cases h2
  case inl h44 =>
    -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
    have h45 : (((p2 ∧ True) → p3) ∨ p4) := by
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- Implications on the right can always be decomposed.
      intro h46
      -- Conjunctions on the left can always be decomposed.
      let h47 := h46.left
      let h48 := h46.right
      -- One of the premise coincides with the conclusion.
      exact h44
    -- We have shown the premise of h1, we can now drive its conclusion.
    let h49 := h1 h45
    -- False on the left can always be used.
    apply False.elim h49
  case inr h50 =>
    -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
    have h51 : (((p2 ∧ True) → p3) ∨ p4) := by
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- Implications on the right can always be decomposed.
      intro h52
      -- Conjunctions on the left can always be decomposed.
      let h53 := h52.left
      let h54 := h52.right
      -- One of the premise coincides with the conclusion.
      exact h50
    -- We have shown the premise of h1, we can now drive its conclusion.
    let h55 := h1 h51
    -- False on the left can always be used.
    apply False.elim h55



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_112782313787834800716935549201 : (((((False ∨ (p2 ∧ False)) → (p1 ∨ (p3 → False))) ∨ (True → (((p5 ∧ (p1 ∨ True)) ∧ ((p2 ∧ p3) ∧ True)) → p4))) → p2) ∨ (False → False)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_676642247747133183008149554604 : ((((p3 ∧ (p4 ∨ ((((((p5 → (False ∨ p5)) → p3) ∧ (True ∨ True)) ∧ (False ∨ p5)) ∧ True) ∧ p2))) ∧ ((False → p3) ∨ (True ∨ p1))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_152222391632559548074757375572 : ((((p5 → p1) → (False ∧ (p2 ∨ p3))) ∧ ((p4 ∨ ((True → (p2 ∧ p3)) → False)) ∨ ((p2 ∧ p2) ∧ p4))) → (True ∧ ((p1 ∨ p1) → p3))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- Implications on the right can always be decomposed.
  intro h2
  -- Disjunctions on the left can always be decomposed.
  cases h2
  case inl h3 =>
    -- Conjunctions on the left can always be decomposed.
    let h4 := h1.left
    let h5 := h1.right
    -- Disjunctions on the left can always be decomposed.
    cases h5
    case inl h6 =>
      -- Disjunctions on the left can always be decomposed.
      cases h6
      case inl h7 =>
        -- We want to use the implication h4 based on <expert-advice>. So we show its premise.
        have h8 : (p5 → p1) := by
          -- Implications on the right can always be decomposed.
          intro h9
          -- One of the premise coincides with the conclusion.
          exact h3
        -- We have shown the premise of h4, we can now drive its conclusion.
        let h10 := h4 h8
        -- We need to get the left conjuct of h10 based on <expert-advice>.
        let h11 := h10.left
        -- False on the left can always be used.
        apply False.elim h11
      case inr h12 =>
        -- We want to use the implication h4 based on <expert-advice>. So we show its premise.
        have h13 : (p5 → p1) := by
          -- Implications on the right can always be decomposed.
          intro h14
          -- One of the premise coincides with the conclusion.
          exact h3
        -- We have shown the premise of h4, we can now drive its conclusion.
        let h15 := h4 h13
        -- We need to get the left conjuct of h15 based on <expert-advice>.
        let h16 := h15.left
        -- False on the left can always be used.
        apply False.elim h16
    case inr h17 =>
      -- Conjunctions on the left can always be decomposed.
      let h18 := h17.left
      let h19 := h17.right
      -- Conjunctions on the left can always be decomposed.
      let h20 := h18.left
      let h21 := h18.right
      -- We want to use the implication h4 based on <expert-advice>. So we show its premise.
      have h22 : (p5 → p1) := by
        -- Implications on the right can always be decomposed.
        intro h23
        -- One of the premise coincides with the conclusion.
        exact h3
      -- We have shown the premise of h4, we can now drive its conclusion.
      let h24 := h4 h22
      -- We need to get the left conjuct of h24 based on <expert-advice>.
      let h25 := h24.left
      -- False on the left can always be used.
      apply False.elim h25
  case inr h26 =>
    -- Conjunctions on the left can always be decomposed.
    let h27 := h1.left
    let h28 := h1.right
    -- Disjunctions on the left can always be decomposed.
    cases h28
    case inl h29 =>
      -- Disjunctions on the left can always be decomposed.
      cases h29
      case inl h30 =>
        -- We want to use the implication h27 based on <expert-advice>. So we show its premise.
        have h31 : (p5 → p1) := by
          -- Implications on the right can always be decomposed.
          intro h32
          -- One of the premise coincides with the conclusion.
          exact h26
        -- We have shown the premise of h27, we can now drive its conclusion.
        let h33 := h27 h31
        -- We need to get the left conjuct of h33 based on <expert-advice>.
        let h34 := h33.left
        -- False on the left can always be used.
        apply False.elim h34
      case inr h35 =>
        -- We want to use the implication h27 based on <expert-advice>. So we show its premise.
        have h36 : (p5 → p1) := by
          -- Implications on the right can always be decomposed.
          intro h37
          -- One of the premise coincides with the conclusion.
          exact h26
        -- We have shown the premise of h27, we can now drive its conclusion.
        let h38 := h27 h36
        -- We need to get the left conjuct of h38 based on <expert-advice>.
        let h39 := h38.left
        -- False on the left can always be used.
        apply False.elim h39
    case inr h40 =>
      -- Conjunctions on the left can always be decomposed.
      let h41 := h40.left
      let h42 := h40.right
      -- Conjunctions on the left can always be decomposed.
      let h43 := h41.left
      let h44 := h41.right
      -- We want to use the implication h27 based on <expert-advice>. So we show its premise.
      have h45 : (p5 → p1) := by
        -- Implications on the right can always be decomposed.
        intro h46
        -- One of the premise coincides with the conclusion.
        exact h26
      -- We have shown the premise of h27, we can now drive its conclusion.
      let h47 := h27 h45
      -- We need to get the left conjuct of h47 based on <expert-advice>.
      let h48 := h47.left
      -- False on the left can always be used.
      apply False.elim h48



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_116490463947423362386574235232 : (((p2 ∧ p4) ∧ (((p5 → (p1 ∧ p5)) ∨ (((False ∨ p5) → ((False ∨ p1) ∧ ((p1 → p3) → True))) ∨ True)) → (p5 → False))) ∨ (True ∨ p1)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_219563743712227743699674535550 : ((True → ((False ∨ p3) ∨ p4)) → (((((True ∧ p2) → p2) → ((p5 → ((p1 ∧ (False ∨ p4)) ∨ p5)) → p4)) ∨ ((p2 → p2) ∨ False)) ∧ True)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h2
  -- One of the premise coincides with the conclusion.
  exact h2
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_65021088061015482799682263215 : ((p2 ∨ ((p1 ∨ p3) ∨ ((((p1 → p3) ∧ p3) ∨ (((p3 ∧ ((p3 → p4) ∧ (p1 → ((p3 → p5) → p2)))) ∧ True) → p2)) → p4))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_312958465266675125774286891516 : (p3 ∨ ((((((((p4 ∧ p2) ∨ p4) ∧ ((p3 ∨ p1) ∧ p5)) ∧ (p4 ∧ ((p5 → p1) ∧ (p1 ∨ (p1 ∧ False))))) → p5) → p1) ∧ True) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_173220696019210682092555839247 : ((p5 ∨ (p4 ∨ ((((p3 ∧ p3) ∧ False) ∧ ((False ∨ (True ∧ p2)) → True)) ∧ p1))) ∨ (p2 → ((p2 ∧ ((p5 → False) ∨ True)) ∨ (False → True)))) := by
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
theorem thm_5_vars_325872816219651730909404113034 : (p5 ∨ (p4 ∨ ((((p5 ∧ p1) ∧ (p5 ∨ (((p4 → p1) ∧ ((False ∨ p5) ∧ p3)) → True))) ∧ (p3 ∧ p2)) ∨ (True ∧ ((p4 ∧ p3) → p4))))) := by
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
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- One of the premise coincides with the conclusion.
  exact h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_197432244822965304392357842949 : (((((p2 ∧ p1) ∨ p4) ∧ p3) ∧ (p2 ∨ True)) ∨ (((p1 → False) ∨ ((((False ∨ ((False → False) ∧ True)) → p1) ∧ (p4 ∧ p1)) → True)) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_349584612655706615952954697450 : (p4 → (((True → ((False ∧ (p5 ∧ (((True ∧ p4) → (False ∧ (((p5 ∨ p2) ∧ ((p1 ∨ p5) ∧ p2)) ∨ p5))) ∨ p4))) ∧ p5)) ∨ p4) ∧ p4)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h1
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_197131005356881424047995256714 : (((p4 ∨ (p1 ∧ ((p2 ∧ p5) ∨ p4))) ∨ p1) ∨ ((((p1 ∧ (p3 ∨ (True ∧ True))) ∧ ((p2 ∨ p5) ∨ p4)) ∧ (p3 ∧ False)) → (p3 ∧ p1))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
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
  cases h7
  case inl h8 =>
    -- Disjunctions on the left can always be decomposed.
    cases h5
    case inl h9 =>
      -- Disjunctions on the left can always be decomposed.
      cases h9
      case inl h10 =>
        -- Conjunctions on the left can always be decomposed.
        let h11 := h3.left
        let h12 := h3.right
        -- False on the left can always be used.
        apply False.elim h12
      case inr h13 =>
        -- Conjunctions on the left can always be decomposed.
        let h14 := h3.left
        let h15 := h3.right
        -- False on the left can always be used.
        apply False.elim h15
    case inr h16 =>
      -- Conjunctions on the left can always be decomposed.
      let h17 := h3.left
      let h18 := h3.right
      -- False on the left can always be used.
      apply False.elim h18
  case inr h19 =>
    -- Conjunctions on the left can always be decomposed.
    let h20 := h19.left
    let h21 := h19.right
    -- Disjunctions on the left can always be decomposed.
    cases h5
    case inl h22 =>
      -- Disjunctions on the left can always be decomposed.
      cases h22
      case inl h23 =>
        -- Conjunctions on the left can always be decomposed.
        let h24 := h3.left
        let h25 := h3.right
        -- False on the left can always be used.
        apply False.elim h25
      case inr h26 =>
        -- Conjunctions on the left can always be decomposed.
        let h27 := h3.left
        let h28 := h3.right
        -- False on the left can always be used.
        apply False.elim h28
    case inr h29 =>
      -- Conjunctions on the left can always be decomposed.
      let h30 := h3.left
      let h31 := h3.right
      -- False on the left can always be used.
      apply False.elim h31
  -- Conjunctions on the left can always be decomposed.
  let h32 := h1.left
  let h33 := h1.right
  -- Conjunctions on the left can always be decomposed.
  let h34 := h32.left
  let h35 := h32.right
  -- Conjunctions on the left can always be decomposed.
  let h36 := h34.left
  let h37 := h34.right
  -- Disjunctions on the left can always be decomposed.
  cases h37
  case inl h38 =>
    -- Disjunctions on the left can always be decomposed.
    cases h35
    case inl h39 =>
      -- Disjunctions on the left can always be decomposed.
      cases h39
      case inl h40 =>
        -- Conjunctions on the left can always be decomposed.
        let h41 := h33.left
        let h42 := h33.right
        -- False on the left can always be used.
        apply False.elim h42
      case inr h43 =>
        -- Conjunctions on the left can always be decomposed.
        let h44 := h33.left
        let h45 := h33.right
        -- False on the left can always be used.
        apply False.elim h45
    case inr h46 =>
      -- Conjunctions on the left can always be decomposed.
      let h47 := h33.left
      let h48 := h33.right
      -- False on the left can always be used.
      apply False.elim h48
  case inr h49 =>
    -- Conjunctions on the left can always be decomposed.
    let h50 := h49.left
    let h51 := h49.right
    -- Disjunctions on the left can always be decomposed.
    cases h35
    case inl h52 =>
      -- Disjunctions on the left can always be decomposed.
      cases h52
      case inl h53 =>
        -- Conjunctions on the left can always be decomposed.
        let h54 := h33.left
        let h55 := h33.right
        -- False on the left can always be used.
        apply False.elim h55
      case inr h56 =>
        -- Conjunctions on the left can always be decomposed.
        let h57 := h33.left
        let h58 := h33.right
        -- False on the left can always be used.
        apply False.elim h58
    case inr h59 =>
      -- Conjunctions on the left can always be decomposed.
      let h60 := h33.left
      let h61 := h33.right
      -- False on the left can always be used.
      apply False.elim h61



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_137797952617262519828669248668 : ((p2 ∨ (p1 ∨ ((p2 ∨ (p1 → (p1 ∧ ((((p4 → p5) → (p4 ∧ False)) ∧ p1) ∨ p4)))) ∨ (p3 ∧ (p5 → p2))))) ∨ (p4 → (p2 → p2))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- One of the premise coincides with the conclusion.
  exact h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_323259537040090803741529596850 : (p5 ∨ ((p5 ∧ ((True ∨ (((p4 ∧ (((True ∨ True) ∨ ((False ∧ False) → (p1 → (p3 → p2)))) ∧ p2)) → False) ∨ p5)) → p5)) ∨ (p4 → p4))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_263803997143205186780347868694 : (True ∧ ((((p5 → p2) ∨ p2) → (p4 ∨ (((p4 ∨ (p3 → p2)) ∧ p4) ∨ (True ∨ p2)))) ∨ (p3 ∨ ((((p2 → p2) ∨ p3) ∨ True) ∧ p4)))) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h2 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- True on the right can always be proven directly.
    apply True.intro
  case inr h3 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- True on the right can always be proven directly.
    apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_88100619841714409519233962273 : (((((p5 → p4) → True) → False) ∧ (((p4 ∨ (p3 ∨ (p1 → p1))) ∧ (p5 ∧ (p1 → p4))) ∨ (p1 ∧ (((True ∧ p5) ∧ p5) → False)))) → p3) := by
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
    cases h5
    case inl h7 =>
      -- Conjunctions on the left can always be decomposed.
      let h8 := h6.left
      let h9 := h6.right
      -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
      have h10 : ((p5 → p4) → True) := by
        -- Implications on the right can always be decomposed.
        intro h11
        -- True on the right can always be proven directly.
        apply True.intro
      -- We have shown the premise of h2, we can now drive its conclusion.
      let h12 := h2 h10
      -- False on the left can always be used.
      apply False.elim h12
    case inr h13 =>
      -- Disjunctions on the left can always be decomposed.
      cases h13
      case inl h14 =>
        -- Conjunctions on the left can always be decomposed.
        let h15 := h6.left
        let h16 := h6.right
        -- One of the premise coincides with the conclusion.
        exact h14
      case inr h17 =>
        -- Conjunctions on the left can always be decomposed.
        let h18 := h6.left
        let h19 := h6.right
        -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
        have h20 : ((p5 → p4) → True) := by
          -- Implications on the right can always be decomposed.
          intro h21
          -- True on the right can always be proven directly.
          apply True.intro
        -- We have shown the premise of h2, we can now drive its conclusion.
        let h22 := h2 h20
        -- False on the left can always be used.
        apply False.elim h22
  case inr h23 =>
    -- Conjunctions on the left can always be decomposed.
    let h24 := h23.left
    let h25 := h23.right
    -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
    have h26 : ((p5 → p4) → True) := by
      -- Implications on the right can always be decomposed.
      intro h27
      -- True on the right can always be proven directly.
      apply True.intro
    -- We have shown the premise of h2, we can now drive its conclusion.
    let h28 := h2 h26
    -- False on the left can always be used.
    apply False.elim h28



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_68255610251911141218075562765 : ((p3 → (((p4 ∨ (p4 ∧ ((p3 ∨ (True ∨ True)) ∧ p1))) ∧ ((p4 ∧ ((p2 → (True ∧ (p3 ∨ p3))) ∧ p3)) ∨ p4)) ∧ (p4 → p4))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_213698602369131367029845743236 : ((((p2 ∧ p4) → False) ∨ p3) ∨ (True ∧ (((p2 ∨ (((p3 ∨ p1) → p5) → p4)) ∧ (p1 ∧ (p1 ∧ p4))) ∨ ((p3 → (p2 ∨ p3)) ∨ p5)))) := by
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
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_721126041516250914645224339440 : (((((True → False) ∨ (p2 ∧ p4)) → (((p1 ∨ (p2 → (p4 → True))) ∧ p4) ∨ (p3 ∨ ((((False ∨ (p5 ∨ p1)) ∧ p2) ∨ p1) ∨ p3)))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_357486575104948941608553175522 : (p5 → (True ∧ (((((p5 ∧ (p2 ∧ p3)) → (((p2 ∧ ((p5 ∨ (p1 → p4)) ∧ p5)) → (p3 → p5)) → (True ∧ False))) → p1) ∨ p5) ∨ p5))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_314945022198977815401634905031 : (p3 ∨ ((((True ∨ ((p5 ∨ p4) ∧ p3)) ∨ (p2 ∧ p1)) ∨ p4) → (True → (p1 ∨ (False ∨ (True → (((False ∨ (p1 ∧ False)) → p1) ∨ p3))))))) := by
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
      -- Disjunctions on the left can always be decomposed.
      cases h4
      case inl h5 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- Implications on the right can always be decomposed.
        intro h6
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- Implications on the right can always be decomposed.
        intro h7
        -- Disjunctions on the left can always be decomposed.
        cases h7
        case inl h8 =>
          -- False on the left can always be used.
          apply False.elim h8
        case inr h9 =>
          -- Conjunctions on the left can always be decomposed.
          let h10 := h9.left
          let h11 := h9.right
          -- False on the left can always be used.
          apply False.elim h11
      case inr h12 =>
        -- Conjunctions on the left can always be decomposed.
        let h13 := h12.left
        let h14 := h12.right
        -- Disjunctions on the left can always be decomposed.
        cases h13
        case inl h15 =>
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- Implications on the right can always be decomposed.
          intro h16
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- One of the premise coincides with the conclusion.
          exact h14
        case inr h17 =>
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- Implications on the right can always be decomposed.
          intro h18
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- One of the premise coincides with the conclusion.
          exact h14
    case inr h19 =>
      -- Conjunctions on the left can always be decomposed.
      let h20 := h19.left
      let h21 := h19.right
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- One of the premise coincides with the conclusion.
      exact h21
  case inr h22 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h23
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Implications on the right can always be decomposed.
    intro h24
    -- Disjunctions on the left can always be decomposed.
    cases h24
    case inl h25 =>
      -- False on the left can always be used.
      apply False.elim h25
    case inr h26 =>
      -- Conjunctions on the left can always be decomposed.
      let h27 := h26.left
      let h28 := h26.right
      -- False on the left can always be used.
      apply False.elim h28



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_40942627870611703056533715719 : ((((((p2 → (p5 ∧ (((p1 ∨ p1) ∧ ((p2 → True) ∨ (p3 ∧ (p4 → p4)))) ∧ False))) → (p5 → p3)) → False) ∨ (True ∧ False)) ∨ True) ∨ p2) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_158280026432386289670036960762 : (((p4 → (p2 ∧ p1)) ∨ ((((p3 ∧ (False ∧ ((p4 ∨ p5) ∧ p4))) ∧ p3) ∨ (False → False)) ∨ False)) ∨ ((((False → True) → p5) → p5) ∧ p4)) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
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
theorem thm_5_vars_324393538560664257062037205624 : (p5 ∨ ((((True ∧ (True ∨ True)) ∧ p2) ∨ p2) → ((p3 ∧ (p3 ∧ (p4 → True))) ∨ (((p2 → True) ∨ p2) ∨ (((p3 ∨ p2) → p5) ∧ False))))) := by
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
    -- Conjunctions on the left can always be decomposed.
    let h5 := h3.left
    let h6 := h3.right
    -- Disjunctions on the left can always be decomposed.
    cases h6
    case inl h7 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- One of the premise coincides with the conclusion.
      exact h4
    case inr h8 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- One of the premise coincides with the conclusion.
      exact h4
  case inr h9 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h9



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_38929511366415251109912783630 : (((((p5 ∧ p1) ∨ p5) → (((False ∧ False) ∨ (p3 ∧ ((((p1 ∧ (False → (p3 ∨ p2))) → False) ∨ p3) ∨ (p1 ∧ p3)))) → p2)) ∧ p1) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_161147845198929677023634985992 : (((p5 → p2) ∧ (p4 ∨ ((p1 → p3) ∨ (p3 ∧ ((((False → (p5 → p4)) ∨ p3) ∨ p2) → p1))))) → (p2 ∨ (p3 ∨ (True ∧ (True ∨ p5))))) := by
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
    -- Conjunctions on the right can always be decomposed.
    apply And.intro
    -- True on the right can always be proven directly.
    apply True.intro
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
    case inr h7 =>
      -- Conjunctions on the left can always be decomposed.
      let h8 := h7.left
      let h9 := h7.right
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
theorem thm_5_vars_605924472348723187173538283854 : ((((p5 → (((((True ∨ (p5 ∧ p5)) ∧ p1) ∧ ((((p2 → p4) → p4) → ((p5 → True) ∧ p4)) → p1)) ∧ p4) ∨ (True ∧ p1))) ∧ False) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_753012741336751983573538028886 : (((False ∧ ((((p5 → p4) ∧ (p5 ∧ p2)) → ((p1 ∨ ((p3 ∧ p5) ∧ p5)) → (((p4 → ((p2 ∨ p2) → p1)) ∧ p1) ∨ p1))) → p3)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_1779860240218249816875200521 : (((((((p4 → (((((p5 → p3) ∧ True) ∧ p2) → True) → False)) ∨ p4) ∧ p5) ∨ True) → False) → (p5 ∧ p3)) ∨ (True → (p2 ∨ p1))) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h2 : ((((p4 → (((((p5 → p3) ∧ True) ∧ p2) → True) → False)) ∨ p4) ∧ p5) ∨ True) := by
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h3 := h1 h2
  -- False on the left can always be used.
  apply False.elim h3
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h4 : ((((p4 → (((((p5 → p3) ∧ True) ∧ p2) → True) → False)) ∨ p4) ∧ p5) ∨ True) := by
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h5 := h1 h4
  -- False on the left can always be used.
  apply False.elim h5



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_173113304426583817629998665637 : ((p2 ∨ ((p1 → (((((p3 → True) ∨ p5) → p3) → (p3 → p3)) ∨ p1)) → p2)) ∨ (((p1 ∧ (((False ∧ True) → p2) ∧ p3)) → p1) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_689207393880821375664891239516 : ((((((p5 ∧ (p2 ∨ p1)) ∧ (((p2 → True) ∧ p4) ∧ ((p1 → p4) ∨ p1))) → p2) ∨ ((p3 → (((p4 → True) → p5) ∨ True)) ∧ True)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_138363104236581295825725675682 : ((p4 → ((False ∧ ((p4 ∨ ((p1 ∨ ((p1 ∧ True) ∧ ((p4 ∨ p5) ∨ p4))) → True)) → p2)) ∨ (p4 → (p2 → p1)))) ∨ (False → (True ∧ p5))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_313310874979321944523649621225 : (p3 ∨ ((p1 ∨ (((p5 ∧ ((p1 ∨ p1) → p2)) → (p3 → p2)) → ((((p1 → False) → (p5 ∧ p1)) ∧ (p3 → False)) → (p2 ∨ True)))) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_155024836538446258632833744955 : (((((((p1 ∧ (True ∨ p5)) ∧ p5) → p1) → (False ∧ p3)) ∧ True) ∨ ((False ∨ False) → (p2 ∨ p3))) ∧ (False → (((p1 ∧ p5) → p3) → p4))) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
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
    -- False on the left can always be used.
    apply False.elim h3
  -- Implications on the right can always be decomposed.
  intro h4
  -- Implications on the right can always be decomposed.
  intro h5
  -- False on the left can always be used.
  apply False.elim h4



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_787967473330874737248280689169 : (((p4 ∨ (p4 → (p3 → (((p3 → False) ∧ ((p4 → p1) → (((p2 ∧ True) → ((p5 ∧ p5) ∧ True)) ∧ True))) ∧ (False ∨ (p5 ∨ p1)))))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_310936993098384308480010724678 : (p2 ∨ ((True ∨ p1) ∧ (((p2 → p2) ∧ (True ∨ True)) ∧ (p3 → ((((p1 ∧ p5) ∨ p4) → ((False ∨ p2) ∧ (p5 → (p3 ∨ p3)))) ∨ True))))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h1
  -- One of the premise coincides with the conclusion.
  exact h1
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro
  -- Implications on the right can always be decomposed.
  intro h2
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_247541393877393552750087407560 : ((False ∨ p4) ∨ ((p1 ∨ (False ∨ ((p2 ∧ False) ∧ (p1 ∧ ((p5 ∨ (p5 → False)) ∧ (p4 ∨ ((p3 ∨ (p1 → p1)) ∨ True))))))) ∨ (p1 ∨ True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_712460387529923958035152811244 : ((((((False ∨ p2) ∧ p4) ∨ (p1 ∨ p1)) ∨ ((p2 ∧ False) → (((False ∨ p1) ∧ (((False ∨ p3) → False) ∨ (True ∨ p5))) ∨ (False ∧ p3)))) ∨ p5) ∧ True) := by
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
  apply False.elim h3
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_264949230719524745516585787672 : (True ∧ ((False ∨ p2) → ((p3 ∨ p2) → ((((p3 ∨ (p4 ∨ ((p1 ∨ True) → (p5 → p5)))) ∨ (True → False)) → p5) ∨ ((False → True) ∨ p4))))) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- True on the right can always be proven directly.
  apply True.intro
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
      -- False on the left can always be used.
      apply False.elim h4
    case inr h5 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- Implications on the right can always be decomposed.
      intro h6
      -- True on the right can always be proven directly.
      apply True.intro
  case inr h7 =>
    -- Disjunctions on the left can always be decomposed.
    cases h1
    case inl h8 =>
      -- False on the left can always be used.
      apply False.elim h8
    case inr h9 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- Implications on the right can always be decomposed.
      intro h10
      -- True on the right can always be proven directly.
      apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_135516624986134359587361408028 : (((((((False → (p2 → ((p4 → p4) ∧ p5))) ∧ p4) → (True ∨ p5)) → p4) ∧ p3) ∧ (((p1 ∧ p1) ∧ p5) ∨ False)) ∨ ((p5 ∧ False) → p4)) := by
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
theorem thm_5_vars_184643848765832293492279710162 : ((((((False ∨ p3) ∨ False) ∨ False) ∧ p3) ∨ (p1 → (p3 ∨ True))) ∨ (((True → ((p4 ∧ ((p1 ∧ p5) → p4)) ∧ p4)) ∨ (True ∧ p1)) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_662784839756870086082519099449 : (((((p4 ∨ (p3 ∨ (p5 → False))) → (((p3 ∨ ((p4 ∨ (p3 → p1)) ∨ (p1 ∧ ((p3 → p4) ∨ p5)))) → p3) → p5)) → (p1 → p1)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_802261823641990189184935700164 : (((p2 → (p4 ∧ (((p1 ∧ (p2 ∨ (((True → (p1 → ((True ∧ True) ∧ (p5 ∧ p2)))) ∧ (False → False)) ∨ (p3 → False)))) → False) ∨ p3))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_307617460584494141368917850152 : (p1 ∨ (p1 → (((True ∨ ((p5 ∨ ((False ∨ (p1 ∧ p2)) ∨ (((p1 ∧ p1) → p4) → (False ∨ p1)))) → p1)) → (p1 ∧ p2)) ∨ (p4 ∨ p1)))) := by
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



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_217307181520583736264649589721 : (((p5 ∧ (True → True)) ∨ False) → (((True → (True ∧ ((((p5 ∧ p5) ∧ p1) → (True ∨ ((p4 → p4) ∨ (False → False)))) → p1))) ∨ p4) ∨ True)) := by
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
    -- False on the left can always be used.
    apply False.elim h5



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_72226890430400120303937165557 : (((p2 → (((p3 → ((((((p4 ∧ p5) ∨ (False → (p1 ∨ (p2 ∨ True)))) ∧ p4) ∧ p2) ∨ p2) ∧ True)) → (p1 → p2)) ∧ p5)) ∧ p2) → p5) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
  have h4 : p2 := by
    -- One of the premise coincides with the conclusion.
    exact h3
  -- We have shown the premise of h2, we can now drive its conclusion.
  let h5 := h2 h4
  -- We need to get the right conjuct of h5 based on <expert-advice>.
  let h6 := h5.right
  -- One of the premise coincides with the conclusion.
  exact h6



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_160410705334922833046083276720 : (((((True → (True ∨ (True ∨ p2))) ∨ (p2 ∨ (p3 ∧ p4))) ∨ (p3 ∨ p4)) ∨ (p4 ∨ (False → p1))) → (p1 ∨ ((p5 ∨ p4) → (p5 ∨ p4)))) := by
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
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- Implications on the right can always be decomposed.
        intro h5
        -- Disjunctions on the left can always be decomposed.
        cases h5
        case inl h6 =>
          -- Show the left disjunct based on <expert-advice>.
          apply Or.inl
          -- One of the premise coincides with the conclusion.
          exact h6
        case inr h7 =>
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- One of the premise coincides with the conclusion.
          exact h7
      case inr h8 =>
        -- Disjunctions on the left can always be decomposed.
        cases h8
        case inl h9 =>
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- Implications on the right can always be decomposed.
          intro h10
          -- Disjunctions on the left can always be decomposed.
          cases h10
          case inl h11 =>
            -- Show the left disjunct based on <expert-advice>.
            apply Or.inl
            -- One of the premise coincides with the conclusion.
            exact h11
          case inr h12 =>
            -- Show the right disjunct based on <expert-advice>.
            apply Or.inr
            -- One of the premise coincides with the conclusion.
            exact h12
        case inr h13 =>
          -- Conjunctions on the left can always be decomposed.
          let h14 := h13.left
          let h15 := h13.right
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- Implications on the right can always be decomposed.
          intro h16
          -- Disjunctions on the left can always be decomposed.
          cases h16
          case inl h17 =>
            -- Show the left disjunct based on <expert-advice>.
            apply Or.inl
            -- One of the premise coincides with the conclusion.
            exact h17
          case inr h18 =>
            -- Show the right disjunct based on <expert-advice>.
            apply Or.inr
            -- One of the premise coincides with the conclusion.
            exact h18
    case inr h19 =>
      -- Disjunctions on the left can always be decomposed.
      cases h19
      case inl h20 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- Implications on the right can always be decomposed.
        intro h21
        -- Disjunctions on the left can always be decomposed.
        cases h21
        case inl h22 =>
          -- Show the left disjunct based on <expert-advice>.
          apply Or.inl
          -- One of the premise coincides with the conclusion.
          exact h22
        case inr h23 =>
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- One of the premise coincides with the conclusion.
          exact h23
      case inr h24 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- Implications on the right can always be decomposed.
        intro h25
        -- Disjunctions on the left can always be decomposed.
        cases h25
        case inl h26 =>
          -- Show the left disjunct based on <expert-advice>.
          apply Or.inl
          -- One of the premise coincides with the conclusion.
          exact h26
        case inr h27 =>
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- One of the premise coincides with the conclusion.
          exact h27
  case inr h28 =>
    -- Disjunctions on the left can always be decomposed.
    cases h28
    case inl h29 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Implications on the right can always be decomposed.
      intro h30
      -- Disjunctions on the left can always be decomposed.
      cases h30
      case inl h31 =>
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- One of the premise coincides with the conclusion.
        exact h31
      case inr h32 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- One of the premise coincides with the conclusion.
        exact h32
    case inr h33 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Implications on the right can always be decomposed.
      intro h34
      -- Disjunctions on the left can always be decomposed.
      cases h34
      case inl h35 =>
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- One of the premise coincides with the conclusion.
        exact h35
      case inr h36 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- One of the premise coincides with the conclusion.
        exact h36



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_111075631748621810917625639234 : ((((((False ∧ p4) ∧ ((True → True) → p4)) → (((False ∨ False) → p2) ∨ True)) → ((p5 → p2) ∧ ((p1 ∧ True) → True))) ∧ p5) ∨ (True ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_323198999495025625013782216330 : (p5 ∨ (((((p5 → p2) → ((p5 ∨ (((p1 ∧ p4) ∨ p5) ∧ (True ∨ True))) → True)) → (False ∧ (p1 → p1))) ∧ (False ∨ False)) ∨ (p3 → True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_214367608341076768423840594579 : (((p4 ∨ (p4 → p5)) → p4) ∨ ((p4 ∧ ((p1 ∨ ((p5 ∨ p2) → (p3 → ((p2 ∨ (p4 → p4)) → (p1 ∧ p2))))) → (p1 ∨ p5))) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_41900868795860488111894650878 : (((((True → p3) ∧ p5) → ((p3 → p4) ∨ (True → ((((False ∨ ((False ∨ p1) ∧ p2)) ∨ (p5 ∨ False)) ∧ (p1 ∨ False)) ∨ p5)))) ∨ p1) ∨ p3) := by
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
  -- Implications on the right can always be decomposed.
  intro h4
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h3



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_45813479021541577112094631030 : (((p1 → (p1 → ((p3 ∧ True) → ((p1 ∧ ((p3 ∧ (p5 ∧ (p3 ∨ p4))) ∨ (p2 ∧ ((p4 ∧ (p3 ∧ p1)) → p1)))) → p3)))) → p2) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_165576267358932110770520603986 : ((((p5 → (p1 → p5)) ∧ ((False ∧ p2) ∨ p1)) ∨ ((p1 ∨ ((p1 → True) ∧ p4)) ∨ p1)) ∨ (p2 ∨ (p5 → ((False ∧ (p4 ∧ p1)) → p1)))) := by
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
  -- False on the left can always be used.
  apply False.elim h3



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_326876440743733159062544005840 : (True → ((((((p4 → p3) ∧ ((p4 ∨ (p3 ∧ (p1 → p3))) ∧ p4)) ∨ (p3 ∨ False)) ∨ ((True → p5) → (p3 ∧ (p2 ∨ p5)))) ∨ p3) ∨ True)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_50431233268860990726173370496 : (((p5 ∧ ((False → ((((p5 → p1) → p5) → p3) ∨ p1)) → (p4 ∧ ((p3 → p1) → (True ∨ p5))))) ∨ (((p1 ∨ p2) → p3) ∧ p4)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_136203851053333542113132713479 : (((p1 ∨ ((p4 ∨ (p3 → p4)) ∨ p3)) ∧ (((p3 → (p5 ∧ p2)) → (p5 ∨ p2)) → ((False → p4) ∧ (True ∧ False)))) ∨ (True → (False → p4))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- False on the left can always be used.
  apply False.elim h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_213327240575555175999801183791 : (((p1 ∧ (p3 ∨ p3)) ∧ p2) ∨ ((p2 ∧ True) → (p5 ∨ (((p1 → (p1 ∧ (((True ∨ (p3 ∧ (p1 ∧ p3))) ∨ p2) → p3))) ∨ True) ∧ p2)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- One of the premise coincides with the conclusion.
  exact h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_761625317233578955849369943678 : (((p3 ∧ ((((p3 ∨ (((p5 ∨ ((p2 ∨ (False ∧ p1)) ∨ p2)) ∧ p2) ∨ False)) ∨ p5) ∨ ((p1 ∨ False) → ((p5 ∨ False) ∨ p5))) ∨ p4)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_52186544795739217171966360353 : ((((False → (p3 → (p3 ∧ p1))) ∨ (((p4 ∧ p3) ∨ (p1 ∧ p1)) → (p1 ∨ True))) → (p3 ∨ (p2 → ((False ∨ False) ∨ (False ∨ p2))))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_930445757752931114849394526188 : (((((p5 ∧ (True ∧ ((p2 ∧ (False ∨ p2)) ∨ p5))) ∨ True) → (((p3 ∧ ((p3 ∨ (p3 ∨ p1)) → True)) ∨ ((p5 → True) → p3)) ∧ p3)) → p3) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h1
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h2 : ((p5 ∧ (True ∧ ((p2 ∧ (False ∨ p2)) ∨ p5))) ∨ True) := by
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h3 := h1 h2
  -- We need to get the right conjuct of h3 based on <expert-advice>.
  let h4 := h3.right
  -- One of the premise coincides with the conclusion.
  exact h4
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_113172642078532155067678873520 : (((p5 → (True ∧ (p3 ∧ (((p4 ∧ p2) ∧ ((True ∨ (p5 ∧ True)) → (False ∨ (p5 ∧ (p3 → p1))))) ∧ (p1 ∧ p3))))) → p3) ∨ (True ∨ p5)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_113863730146036893463497612017 : (((p3 → (p5 → (((p4 → False) ∨ (p4 → ((p3 ∨ (True → (p1 ∧ p3))) → p3))) ∨ ((p2 → p3) ∨ p3)))) → (p3 ∧ p3)) ∨ (p4 → True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_423999358261999964080006606005 : (((((((p2 ∧ ((p3 ∧ p2) ∧ p4)) ∨ p1) → (p1 → (True → p4))) ∨ ((False ∧ (p3 ∨ (p2 ∧ p3))) ∨ (p4 → True))) ∧ (p5 → p5)) ∧ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro
  -- Implications on the right can always be decomposed.
  intro h2
  -- One of the premise coincides with the conclusion.
  exact h2
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



