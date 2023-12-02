variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_51273513963613304713128224565 : (((True ∧ (p4 ∨ ((p3 ∧ (((p5 → p4) ∨ True) ∨ p1)) ∧ ((p2 → (p3 ∨ False)) ∧ p3)))) ∨ (((p2 ∧ True) ∨ True) ∧ (True ∨ False))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_59873321939124385076889249238 : (((p4 ∧ p3) → (((((True ∧ (((p1 ∧ (((p4 → p3) → p1) → p2)) → p5) ∨ (p4 ∨ p2))) ∨ (True ∨ p4)) ∨ p1) → p1) ∨ p4)) ∨ p2) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_151397456564837001742273739483 : ((((((p2 → (p1 ∧ p3)) ∨ (True ∧ True)) → False) ∧ (((p2 → (p5 ∨ True)) ∨ True) ∧ p1)) ∧ (p3 ∧ p1)) → (p5 ∧ ((p2 ∨ p4) ∧ p3))) := by
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
  let h6 := h5.left
  let h7 := h5.right
  -- Disjunctions on the left can always be decomposed.
  cases h6
  case inl h8 =>
    -- Conjunctions on the left can always be decomposed.
    let h9 := h3.left
    let h10 := h3.right
    -- We want to use the implication h4 based on <expert-advice>. So we show its premise.
    have h11 : ((p2 → (p1 ∧ p3)) ∨ (True ∧ True)) := by
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Conjunctions on the right can always be decomposed.
      apply And.intro
      -- True on the right can always be proven directly.
      apply True.intro
      -- True on the right can always be proven directly.
      apply True.intro
    -- We have shown the premise of h4, we can now drive its conclusion.
    let h12 := h4 h11
    -- False on the left can always be used.
    apply False.elim h12
  case inr h13 =>
    -- Conjunctions on the left can always be decomposed.
    let h14 := h3.left
    let h15 := h3.right
    -- We want to use the implication h4 based on <expert-advice>. So we show its premise.
    have h16 : ((p2 → (p1 ∧ p3)) ∨ (True ∧ True)) := by
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Conjunctions on the right can always be decomposed.
      apply And.intro
      -- True on the right can always be proven directly.
      apply True.intro
      -- True on the right can always be proven directly.
      apply True.intro
    -- We have shown the premise of h4, we can now drive its conclusion.
    let h17 := h4 h16
    -- False on the left can always be used.
    apply False.elim h17
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Conjunctions on the left can always be decomposed.
  let h18 := h1.left
  let h19 := h1.right
  -- Conjunctions on the left can always be decomposed.
  let h20 := h18.left
  let h21 := h18.right
  -- Conjunctions on the left can always be decomposed.
  let h22 := h21.left
  let h23 := h21.right
  -- Disjunctions on the left can always be decomposed.
  cases h22
  case inl h24 =>
    -- Conjunctions on the left can always be decomposed.
    let h25 := h19.left
    let h26 := h19.right
    -- We want to use the implication h20 based on <expert-advice>. So we show its premise.
    have h27 : ((p2 → (p1 ∧ p3)) ∨ (True ∧ True)) := by
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Conjunctions on the right can always be decomposed.
      apply And.intro
      -- True on the right can always be proven directly.
      apply True.intro
      -- True on the right can always be proven directly.
      apply True.intro
    -- We have shown the premise of h20, we can now drive its conclusion.
    let h28 := h20 h27
    -- False on the left can always be used.
    apply False.elim h28
  case inr h29 =>
    -- Conjunctions on the left can always be decomposed.
    let h30 := h19.left
    let h31 := h19.right
    -- We want to use the implication h20 based on <expert-advice>. So we show its premise.
    have h32 : ((p2 → (p1 ∧ p3)) ∨ (True ∧ True)) := by
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Conjunctions on the right can always be decomposed.
      apply And.intro
      -- True on the right can always be proven directly.
      apply True.intro
      -- True on the right can always be proven directly.
      apply True.intro
    -- We have shown the premise of h20, we can now drive its conclusion.
    let h33 := h20 h32
    -- False on the left can always be used.
    apply False.elim h33
  -- Conjunctions on the left can always be decomposed.
  let h34 := h1.left
  let h35 := h1.right
  -- Conjunctions on the left can always be decomposed.
  let h36 := h34.left
  let h37 := h34.right
  -- Conjunctions on the left can always be decomposed.
  let h38 := h37.left
  let h39 := h37.right
  -- Disjunctions on the left can always be decomposed.
  cases h38
  case inl h40 =>
    -- Conjunctions on the left can always be decomposed.
    let h41 := h35.left
    let h42 := h35.right
    -- One of the premise coincides with the conclusion.
    exact h41
  case inr h43 =>
    -- Conjunctions on the left can always be decomposed.
    let h44 := h35.left
    let h45 := h35.right
    -- One of the premise coincides with the conclusion.
    exact h44



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_263709342499459686818667709272 : (True ∧ ((p2 ∨ (p4 → ((p3 ∧ (((((p2 ∧ p4) → p2) → p5) → p3) ∨ (p2 ∨ False))) ∨ p1))) ∨ ((p1 → p4) → (p3 → (p3 ∧ p3))))) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- One of the premise coincides with the conclusion.
  exact h2
  -- One of the premise coincides with the conclusion.
  exact h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_347138016860793938147073694596 : (p3 → (((p5 ∧ ((p5 ∧ (p5 ∧ p1)) ∧ p1)) ∧ ((p5 ∧ (True ∧ False)) ∨ p3)) → ((((False ∧ False) ∧ p2) ∧ ((p3 → False) ∨ False)) ∨ p5))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Conjunctions on the left can always be decomposed.
  let h3 := h2.left
  let h4 := h2.right
  -- Conjunctions on the left can always be decomposed.
  let h5 := h3.left
  let h6 := h3.right
  -- Conjunctions on the left can always be decomposed.
  let h7 := h6.left
  let h8 := h6.right
  -- Conjunctions on the left can always be decomposed.
  let h9 := h7.left
  let h10 := h7.right
  -- Conjunctions on the left can always be decomposed.
  let h11 := h10.left
  let h12 := h10.right
  -- Disjunctions on the left can always be decomposed.
  cases h4
  case inl h13 =>
    -- Conjunctions on the left can always be decomposed.
    let h14 := h13.left
    let h15 := h13.right
    -- Conjunctions on the left can always be decomposed.
    let h16 := h15.left
    let h17 := h15.right
    -- False on the left can always be used.
    apply False.elim h17
  case inr h18 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h11



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_761212924082960327637847751024 : (((p2 ∧ (p5 → ((p4 ∨ p5) ∧ (((((p5 → ((p1 ∧ False) → p1)) ∨ True) ∧ p3) → ((p1 ∧ ((p1 ∨ False) ∨ p3)) ∨ True)) → p1)))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_134910515779461304033881974526 : ((((p2 → ((p4 ∧ ((p5 ∧ p2) ∧ False)) ∨ (((p4 ∨ (p3 → p1)) ∧ p2) ∨ (p4 → p3)))) ∧ p4) ∧ (False ∧ p3)) ∨ (p4 ∨ (False → p1))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_126476219956300440997460894696 : ((p2 ∧ ((False ∨ ((p1 ∨ (p5 ∧ (p3 ∧ (False ∧ (p3 → p1))))) ∨ (p3 ∨ (p2 ∨ p1)))) → ((p2 → p3) ∧ (False ∧ p2)))) → (p5 → p1)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Conjunctions on the left can always be decomposed.
  let h3 := h1.left
  let h4 := h1.right
  -- We want to use the implication h4 based on <expert-advice>. So we show its premise.
  have h5 : (False ∨ ((p1 ∨ (p5 ∧ (p3 ∧ (False ∧ (p3 → p1))))) ∨ (p3 ∨ (p2 ∨ p1)))) := by
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- One of the premise coincides with the conclusion.
    exact h3
  -- We have shown the premise of h4, we can now drive its conclusion.
  let h6 := h4 h5
  -- We need to get the right conjuct of h6 based on <expert-advice>.
  let h7 := h6.right
  -- We need to get the left conjuct of h7 based on <expert-advice>.
  let h8 := h7.left
  -- False on the left can always be used.
  apply False.elim h8



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_618802588625442944726837249479 : (((((p2 ∧ (p5 ∨ p3)) ∧ (((p3 ∨ ((((True → (True ∧ p4)) → (p4 ∨ p3)) ∨ False) → p2)) ∨ p4) ∧ ((False ∨ p5) → p5))) ∨ False) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_790608988986669824031998403193 : (((p5 ∨ (p3 ∨ (((p1 ∧ (True ∧ ((p1 → (True → p5)) ∨ (p3 → False)))) ∨ p5) ∨ ((p3 ∧ ((p2 ∨ p5) ∨ (True ∧ True))) ∨ p5)))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_356165792894774705990417304596 : (p5 → ((p1 ∧ (((True ∨ (p2 ∨ p3)) ∧ ((((p1 ∧ False) ∨ p1) ∧ (p5 ∧ False)) ∨ True)) → False)) ∨ (p2 ∨ (p1 → (p4 → (False ∨ p1)))))) := by
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
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_327821147281565830323086421376 : (True → ((((((((p5 → p3) ∧ (p2 → (True ∧ (p2 ∨ (p5 ∧ False))))) → p3) → p4) ∧ (p3 → p4)) ∨ False) ∧ (p4 ∧ p1)) ∨ (True ∨ p1))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_180856964938249654612761595528 : (((True ∧ (True ∨ p4)) ∨ ((p5 ∧ p5) ∨ ((False ∧ True) ∧ (True ∨ p5)))) → (p5 → (((p5 ∧ (((False ∧ p2) ∧ p4) ∨ True)) ∨ p2) ∨ p2))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h3 =>
    -- Conjunctions on the left can always be decomposed.
    let h4 := h3.left
    let h5 := h3.right
    -- Disjunctions on the left can always be decomposed.
    cases h5
    case inl h6 =>
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- Conjunctions on the right can always be decomposed.
      apply And.intro
      -- One of the premise coincides with the conclusion.
      exact h2
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- True on the right can always be proven directly.
      apply True.intro
    case inr h7 =>
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- Conjunctions on the right can always be decomposed.
      apply And.intro
      -- One of the premise coincides with the conclusion.
      exact h2
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- True on the right can always be proven directly.
      apply True.intro
  case inr h8 =>
    -- Disjunctions on the left can always be decomposed.
    cases h8
    case inl h9 =>
      -- Conjunctions on the left can always be decomposed.
      let h10 := h9.left
      let h11 := h9.right
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- Conjunctions on the right can always be decomposed.
      apply And.intro
      -- One of the premise coincides with the conclusion.
      exact h11
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- True on the right can always be proven directly.
      apply True.intro
    case inr h12 =>
      -- Conjunctions on the left can always be decomposed.
      let h13 := h12.left
      let h14 := h12.right
      -- Conjunctions on the left can always be decomposed.
      let h15 := h13.left
      let h16 := h13.right
      -- False on the left can always be used.
      apply False.elim h15



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_355608948463246939349719035711 : (p5 → (((True ∨ True) → (p5 → (((False ∨ True) ∨ (((False ∧ (False ∨ p2)) ∧ p5) → True)) → ((True → p4) → (p4 ∨ p4))))) ∨ (p3 → p1))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h2
  -- Implications on the right can always be decomposed.
  intro h3
  -- Implications on the right can always be decomposed.
  intro h4
  -- Implications on the right can always be decomposed.
  intro h5
  -- Disjunctions on the left can always be decomposed.
  cases h4
  case inl h6 =>
    -- Disjunctions on the left can always be decomposed.
    cases h6
    case inl h7 =>
      -- False on the left can always be used.
      apply False.elim h7
    case inr h8 =>
      -- Disjunctions on the left can always be decomposed.
      cases h2
      case inl h9 =>
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- We want to use the implication h5 based on <expert-advice>. So we show its premise.
        have h10 : True := by
          -- True on the right can always be proven directly.
          apply True.intro
        -- We have shown the premise of h5, we can now drive its conclusion.
        let h11 := h5 h10
        -- One of the premise coincides with the conclusion.
        exact h11
      case inr h12 =>
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- We want to use the implication h5 based on <expert-advice>. So we show its premise.
        have h13 : True := by
          -- True on the right can always be proven directly.
          apply True.intro
        -- We have shown the premise of h5, we can now drive its conclusion.
        let h14 := h5 h13
        -- One of the premise coincides with the conclusion.
        exact h14
  case inr h15 =>
    -- Disjunctions on the left can always be decomposed.
    cases h2
    case inl h16 =>
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- We want to use the implication h5 based on <expert-advice>. So we show its premise.
      have h17 : True := by
        -- True on the right can always be proven directly.
        apply True.intro
      -- We have shown the premise of h5, we can now drive its conclusion.
      let h18 := h5 h17
      -- One of the premise coincides with the conclusion.
      exact h18
    case inr h19 =>
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- We want to use the implication h5 based on <expert-advice>. So we show its premise.
      have h20 : True := by
        -- True on the right can always be proven directly.
        apply True.intro
      -- We have shown the premise of h5, we can now drive its conclusion.
      let h21 := h5 h20
      -- One of the premise coincides with the conclusion.
      exact h21



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_113769884942612498548525259961 : ((((((False ∧ True) → True) ∧ p4) ∨ (p3 ∨ (True → (p1 ∧ (((p5 → True) ∧ ((p3 ∧ p2) → False)) ∧ p5))))) → (p2 ∧ p1)) ∨ (False → p4)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_257265512846228126796002095990 : ((p2 ∨ p3) → ((True → ((((p1 ∧ (False ∧ ((p4 → False) → p5))) → p4) ∧ (p1 → p5)) → p4)) ∨ ((p5 ∧ (True ∨ p2)) → (True ∨ p4)))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h2 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h3
    -- Conjunctions on the left can always be decomposed.
    let h4 := h3.left
    let h5 := h3.right
    -- Disjunctions on the left can always be decomposed.
    cases h5
    case inl h6 =>
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- True on the right can always be proven directly.
      apply True.intro
    case inr h7 =>
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- True on the right can always be proven directly.
      apply True.intro
  case inr h8 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h9
    -- Conjunctions on the left can always be decomposed.
    let h10 := h9.left
    let h11 := h9.right
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



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_69181093578015595518083349366 : ((p5 → ((((p5 ∧ p4) ∨ p4) ∧ ((((p3 ∧ p1) ∧ p5) ∧ (p2 → p4)) ∨ p3)) ∨ (((False ∨ (p4 ∨ p4)) ∧ p1) → (p5 ∨ False)))) ∨ p2) := by
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
  -- Disjunctions on the left can always be decomposed.
  cases h3
  case inl h5 =>
    -- False on the left can always be used.
    apply False.elim h5
  case inr h6 =>
    -- Disjunctions on the left can always be decomposed.
    cases h6
    case inl h7 =>
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- One of the premise coincides with the conclusion.
      exact h1
    case inr h8 =>
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- One of the premise coincides with the conclusion.
      exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_52117254444099114986597597030 : ((((((p1 ∨ (False ∧ p1)) ∨ (p4 ∨ False)) ∨ ((p1 ∧ (True ∧ False)) ∧ p5)) → True) → ((((p5 ∨ True) → p5) ∧ (False ∨ False)) ∨ False)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_113822855585554260112164771074 : (((p4 ∧ (p3 ∨ (((p2 ∨ ((True ∧ (True ∨ p1)) ∧ p3)) ∨ ((True → (p2 → True)) ∨ True)) → (False ∨ p5)))) → (p5 → p2)) ∨ (False → p3)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_158761057857442015409741218095 : ((p4 ∧ ((False → ((False ∧ p3) ∨ p4)) ∧ (((p4 ∨ p4) ∧ False) ∧ (((False → p3) ∨ True) ∨ p4)))) ∨ ((p1 → False) ∨ (True ∧ (False → p1)))) := by
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
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_40887024591534079422048808139 : ((((((((p3 → p5) ∨ (p4 ∨ p2)) → p2) → p4) ∧ ((False ∧ p3) ∨ ((False ∨ ((p4 ∨ p3) ∨ p3)) → True))) ∧ (p1 ∨ p2)) ∨ False) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_314640845597318923704432711980 : (p3 ∨ (((p1 → ((p5 ∨ False) ∧ ((p1 ∨ (False ∨ (False ∨ (p5 ∧ p5)))) → False))) ∧ True) ∨ (p2 → (True ∨ (p5 ∨ ((p3 ∨ False) ∨ False)))))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_129404106148247886956233475043 : (((p1 ∨ (((p2 ∧ ((((True ∧ p3) → True) → p3) ∧ (True ∨ p5))) → p1) ∨ (p3 ∨ ((p2 ∨ p4) ∧ p3)))) ∨ True) ∧ ((p1 → True) ∨ p3)) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_231194627395348558390400293240 : (((p3 ∨ True) ∨ p4) → (p4 → (((True ∧ (((p1 ∧ False) ∧ (True ∨ p1)) ∧ (p2 ∨ p3))) ∧ (p4 ∧ ((True ∧ False) ∨ p2))) ∨ (False → p2)))) := by
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
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Implications on the right can always be decomposed.
      intro h5
      -- False on the left can always be used.
      apply False.elim h5
    case inr h6 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Implications on the right can always be decomposed.
      intro h7
      -- False on the left can always be used.
      apply False.elim h7
  case inr h8 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h9
    -- False on the left can always be used.
    apply False.elim h9



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_68264384508057122496134807841 : ((p3 → (((p4 ∧ ((p5 ∨ p5) ∨ (p1 ∧ ((True ∧ p4) ∨ (((False ∧ p5) ∨ False) ∨ (False → True)))))) ∧ (p3 ∨ p4)) ∨ (p4 ∨ p3))) ∨ False) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_732904917307702956103653287530 : ((((p2 ∧ p1) ∧ (p4 ∨ (((((True → (p2 → ((False ∨ True) ∨ p5))) ∨ p1) ∨ (p2 ∧ True)) ∨ (p5 → ((True → p4) → p1))) → p5))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_137225672439925077396593638200 : ((p1 ∧ ((((((p3 ∧ True) → (True → p2)) ∧ ((p5 ∨ p1) → (False ∨ ((p5 → p1) ∨ p4)))) ∨ p4) ∧ p4) → p5)) ∨ (p3 ∨ (False → p4))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_50492271715334902351225060178 : (((p5 → ((((((p4 ∧ p3) → True) ∨ p1) ∧ (((False ∧ (p1 ∨ p3)) ∧ p4) ∧ p5)) → p2) → False)) ∨ ((False ∧ (p5 ∧ False)) → p1)) ∨ p3) := by
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



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_53132082650135867241107140012 : ((((((p1 ∨ p4) → ((p1 ∧ p1) ∧ p2)) ∨ (False ∨ p5)) ∧ p5) ∨ ((True → (p4 → (p4 ∨ (p5 → ((True → True) ∨ p4))))) ∨ False)) ∨ p3) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- One of the premise coincides with the conclusion.
  exact h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_755984228895733281314363167703 : (((p1 ∧ (((((False ∧ p3) → False) ∧ p3) ∨ (((True ∧ ((p3 ∨ (p2 ∧ (p2 → (True ∧ (p4 ∨ p3))))) ∧ p1)) ∧ p1) → p4)) → p5)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_136861394264126594483397300866 : (((p5 ∧ p4) ∨ (((((True → ((p4 → False) ∨ p2)) ∧ True) ∧ True) → (p2 ∨ (p1 ∨ p4))) ∧ ((False ∧ p2) → p4))) ∨ ((p2 ∨ True) ∨ p2)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_55522197922159627943972518124 : ((((p2 → False) ∨ ((False ∧ p4) ∨ p1)) → (p5 ∨ (p5 ∨ ((p1 ∧ ((True ∧ (p2 → p3)) ∧ p1)) → (((p4 ∨ False) → p5) ∨ True))))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_219291269119696261160806935255 : ((p2 ∨ ((True → p2) ∧ p2)) → (((p4 ∧ (p4 ∨ p2)) ∧ p5) ∨ ((False ∧ (p2 ∨ ((((p3 ∨ p2) ∨ p5) ∧ False) ∨ p4))) → (False ∨ p5)))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h2 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h3
    -- Conjunctions on the left can always be decomposed.
    let h4 := h3.left
    let h5 := h3.right
    -- False on the left can always be used.
    apply False.elim h4
  case inr h6 =>
    -- Conjunctions on the left can always be decomposed.
    let h7 := h6.left
    let h8 := h6.right
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h9
    -- Conjunctions on the left can always be decomposed.
    let h10 := h9.left
    let h11 := h9.right
    -- False on the left can always be used.
    apply False.elim h10



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_164769303308820266476851463583 : ((((p1 ∧ (False ∧ (p2 ∧ (p2 ∨ (p1 → p4))))) ∧ (True → (p5 → (p2 ∧ p5)))) ∨ True) ∨ ((((p1 → (p4 ∧ True)) → p4) ∧ False) → p4)) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_640562654294168911404312837351 : (((((True ∨ p2) ∧ ((p3 ∨ (False → (p1 ∧ p1))) → (True ∧ ((p2 ∧ ((p3 ∨ (p1 ∨ p1)) ∧ p5)) ∨ ((p1 ∧ p3) → False))))) → False) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_103367749851342906536299457338 : (((p1 → (((((p4 ∨ p2) ∨ ((p2 ∧ p1) ∧ (((p4 ∨ p3) → p5) ∨ p2))) ∧ ((True ∨ False) → False)) ∧ True) ∨ False)) ∨ True) ∧ (p4 ∨ True)) := by
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
theorem thm_5_vars_901512252473492384605706671 : ((p4 → ((p5 ∨ (p1 ∨ (((p2 → p1) → ((False ∨ (False ∧ False)) ∧ ((((p2 → True) → False) ∧ p4) ∧ p3))) ∧ p3))) ∨ p4)) ∨ p5) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_923553183077630265491721945506 : (((((((p3 → True) → True) ∧ (p3 → p2)) ∨ ((p4 → p1) → p1)) ∧ (((p3 ∨ ((p4 ∨ (p3 ∨ False)) ∨ (p5 → p5))) → p3) ∧ True)) → p3) ∧ True) := by
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
    -- Conjunctions on the left can always be decomposed.
    let h7 := h3.left
    let h8 := h3.right
    -- We want to use the implication h7 based on <expert-advice>. So we show its premise.
    have h9 : (p3 ∨ ((p4 ∨ (p3 ∨ False)) ∨ (p5 → p5))) := by
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Implications on the right can always be decomposed.
      intro h10
      -- One of the premise coincides with the conclusion.
      exact h10
    -- We have shown the premise of h7, we can now drive its conclusion.
    let h11 := h7 h9
    -- One of the premise coincides with the conclusion.
    exact h11
  case inr h12 =>
    -- Conjunctions on the left can always be decomposed.
    let h13 := h3.left
    let h14 := h3.right
    -- We want to use the implication h13 based on <expert-advice>. So we show its premise.
    have h15 : (p3 ∨ ((p4 ∨ (p3 ∨ False)) ∨ (p5 → p5))) := by
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Implications on the right can always be decomposed.
      intro h16
      -- One of the premise coincides with the conclusion.
      exact h16
    -- We have shown the premise of h13, we can now drive its conclusion.
    let h17 := h13 h15
    -- One of the premise coincides with the conclusion.
    exact h17
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_139859631182964701551248730022 : ((((((((p3 ∨ p2) ∨ p2) → ((((p2 → True) ∨ (p1 → p3)) ∧ p3) ∧ False)) ∨ p5) ∨ False) ∧ p1) ∧ (p3 → p4)) → ((p4 ∧ True) → p4)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Conjunctions on the left can always be decomposed.
  let h3 := h2.left
  let h4 := h2.right
  -- Conjunctions on the left can always be decomposed.
  let h5 := h1.left
  let h6 := h1.right
  -- Conjunctions on the left can always be decomposed.
  let h7 := h5.left
  let h8 := h5.right
  -- Disjunctions on the left can always be decomposed.
  cases h7
  case inl h9 =>
    -- Disjunctions on the left can always be decomposed.
    cases h9
    case inl h10 =>
      -- One of the premise coincides with the conclusion.
      exact h3
    case inr h11 =>
      -- One of the premise coincides with the conclusion.
      exact h3
  case inr h12 =>
    -- False on the left can always be used.
    apply False.elim h12



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_342219834766550819930636773462 : (p2 → ((p1 ∧ ((True ∨ (p1 ∨ (False ∧ p1))) ∨ (((p4 → p2) → ((False ∧ p2) ∧ False)) ∨ (False → p1)))) → (((p5 ∧ p3) ∨ True) ∨ p4))) := by
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
    -- Disjunctions on the left can always be decomposed.
    cases h5
    case inl h6 =>
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- True on the right can always be proven directly.
      apply True.intro
    case inr h7 =>
      -- Disjunctions on the left can always be decomposed.
      cases h7
      case inl h8 =>
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- True on the right can always be proven directly.
        apply True.intro
      case inr h9 =>
        -- Conjunctions on the left can always be decomposed.
        let h10 := h9.left
        let h11 := h9.right
        -- False on the left can always be used.
        apply False.elim h10
  case inr h12 =>
    -- Disjunctions on the left can always be decomposed.
    cases h12
    case inl h13 =>
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- True on the right can always be proven directly.
      apply True.intro
    case inr h14 =>
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- True on the right can always be proven directly.
      apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_41423500364026929742073467824 : ((((p3 → (((False ∨ True) → False) → ((p5 ∧ ((p4 ∨ p2) → p2)) ∧ p2))) ∨ (p1 → ((p2 ∨ (p3 ∨ (True → p4))) ∨ p5))) ∨ p2) ∨ p3) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
  have h3 : (False ∨ True) := by
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h2, we can now drive its conclusion.
  let h4 := h2 h3
  -- False on the left can always be used.
  apply False.elim h4
  -- Implications on the right can always be decomposed.
  intro h5
  -- Disjunctions on the left can always be decomposed.
  cases h5
  case inl h6 =>
    -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
    have h7 : (False ∨ True) := by
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- True on the right can always be proven directly.
      apply True.intro
    -- We have shown the premise of h2, we can now drive its conclusion.
    let h8 := h2 h7
    -- False on the left can always be used.
    apply False.elim h8
  case inr h9 =>
    -- One of the premise coincides with the conclusion.
    exact h9
  -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
  have h10 : (False ∨ True) := by
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h2, we can now drive its conclusion.
  let h11 := h2 h10
  -- False on the left can always be used.
  apply False.elim h11



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_151595362267161643820817209834 : ((((False ∨ (p2 ∧ p2)) ∧ ((p3 → (p4 ∨ (p5 ∨ (True ∨ (p2 ∧ p5))))) ∧ (p4 ∧ False))) → (False ∧ p2)) → ((p2 ∧ (True → p3)) → p3)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Conjunctions on the left can always be decomposed.
  let h3 := h2.left
  let h4 := h2.right
  -- We want to use the implication h4 based on <expert-advice>. So we show its premise.
  have h5 : True := by
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h4, we can now drive its conclusion.
  let h6 := h4 h5
  -- One of the premise coincides with the conclusion.
  exact h6



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_774793573500669757303193503425 : (((False ∨ ((p3 ∨ ((p1 → p2) ∨ (p1 → p3))) ∨ ((p4 ∨ (p5 ∧ (True ∧ (True → (True → (p2 ∧ (p3 → False))))))) ∨ (p3 → p3)))) ∨ False) ∧ True) := by
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
  -- Implications on the right can always be decomposed.
  intro h1
  -- One of the premise coincides with the conclusion.
  exact h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_135087537940226368922484865052 : ((((((((p4 ∨ ((True ∨ p5) ∨ p1)) ∧ True) ∧ False) ∧ p3) → False) → (p5 ∧ ((p3 ∧ p3) ∨ True))) ∨ (p1 ∧ p1)) ∨ (p1 → (p2 → p1))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_160340612986946989641209684722 : (((p3 ∨ (((False → p2) ∧ (((p5 → False) ∨ p2) ∧ p4)) ∨ ((p1 ∨ p2) ∧ False))) → (p2 ∧ True)) → (((p3 ∨ (p2 ∨ p4)) ∧ p5) ∨ True)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_67998182020052703998054897116 : ((p2 → ((p4 ∨ False) ∨ (((p1 ∧ (p3 ∧ (((((((False ∨ True) ∧ False) → True) → p5) → (p4 ∨ True)) → p5) ∨ p4))) ∨ p3) ∨ p2))) ∨ p2) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_50184487500535044015281093174 : ((((((p2 ∧ p4) ∨ ((False ∨ p2) ∨ p1)) ∧ (p4 ∨ ((p4 ∨ ((False → p3) ∨ p5)) ∧ p1))) ∧ p5) ∨ ((p3 ∧ False) ∨ (True ∨ p2))) ∨ p2) := by
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
theorem thm_5_vars_216717086742084797082308373893 : ((((p5 ∧ p1) → p3) ∧ p3) → ((p2 ∨ (((True ∨ (p3 ∨ ((p4 → (((p3 ∧ p5) → p1) ∨ False)) ∨ p2))) → False) ∨ (True → True))) ∨ p4)) := by
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
  -- Implications on the right can always be decomposed.
  intro h4
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_172303814578086712236301176623 : (((((p2 → p2) → p2) ∧ ((p3 → True) → p3)) → ((p4 ∨ (p2 ∧ True)) ∨ p2)) ∨ (((p2 ∧ False) → ((p2 → p4) ∧ (p5 ∨ p4))) ∧ p3)) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
  have h4 : (p2 → p2) := by
    -- Implications on the right can always be decomposed.
    intro h5
    -- One of the premise coincides with the conclusion.
    exact h5
  -- We have shown the premise of h2, we can now drive its conclusion.
  let h6 := h2 h4
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h6



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_355547109515459513607690577622 : (p5 → (((True → (False ∨ ((p3 ∨ (p5 ∧ ((False ∧ ((((p2 ∨ p5) ∧ p2) ∨ p1) ∨ p3)) ∨ p5))) ∨ (p2 ∨ True)))) ∨ False) ∨ (p4 → p2))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h2
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_172986339725868111245291076766 : ((p5 ∧ (((p3 ∨ p4) ∧ ((p3 → p2) ∧ ((p4 ∨ p5) ∧ (p3 ∧ p5)))) ∧ True)) ∨ ((((p3 → p4) ∧ (True ∧ p5)) ∧ False) → (p1 ∨ p2))) := by
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
  -- Conjunctions on the left can always be decomposed.
  let h6 := h5.left
  let h7 := h5.right
  -- False on the left can always be used.
  apply False.elim h3



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_219574897732670102580705330544 : ((True → ((False ∨ p5) → p2)) → ((((p2 ∧ (p2 ∧ True)) ∧ False) ∧ (p5 ∧ ((True ∧ p2) ∨ (p3 ∧ False)))) ∨ (p5 → ((p4 ∧ False) ∨ p2)))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h2
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h3 : True := by
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h4 := h1 h3
  -- We want to use the implication h4 based on <expert-advice>. So we show its premise.
  have h5 : (False ∨ p5) := by
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h2
  -- We have shown the premise of h4, we can now drive its conclusion.
  let h6 := h4 h5
  -- One of the premise coincides with the conclusion.
  exact h6



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_357477213397038404613345282996 : (p5 → ((p5 → p2) → ((True ∧ ((p5 ∧ ((True ∧ (p5 ∨ (p4 ∧ p3))) → p1)) ∨ (p1 → ((p1 ∨ (p5 ∨ True)) → (p5 → p2))))) ∨ p2))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
  have h3 : p5 := by
    -- One of the premise coincides with the conclusion.
    exact h1
  -- We have shown the premise of h2, we can now drive its conclusion.
  let h4 := h2 h3
  -- One of the premise coincides with the conclusion.
  exact h4



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_732884642761446828474126078228 : ((((p2 ∧ p1) ∧ (((p1 ∨ (p2 → p5)) ∧ (p4 ∨ ((p4 ∨ (((False ∨ (p1 ∨ p4)) ∧ False) ∨ p1)) ∨ p1))) ∧ ((p4 ∨ p4) ∧ p5))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_609562017033599386504668725084 : (((((p4 ∧ ((((p3 ∧ p4) ∨ (p5 ∨ (p2 ∨ ((True ∧ p1) ∨ (((p4 ∨ p4) → p2) → False))))) ∨ (p4 ∨ p2)) ∧ p1)) ∨ p4) ∨ True) ∨ p2) ∧ True) := by
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
theorem thm_5_vars_185043161850475590541206839681 : (((p3 → False) ∧ (False ∨ ((p1 ∧ ((p2 ∧ p2) → False)) → False))) ∨ (((p2 ∧ p4) → p1) → ((p1 ∧ (p5 ∧ True)) → (p4 → (p4 ∨ False))))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Implications on the right can always be decomposed.
  intro h3
  -- Conjunctions on the left can always be decomposed.
  let h4 := h2.left
  let h5 := h2.right
  -- Conjunctions on the left can always be decomposed.
  let h6 := h5.left
  let h7 := h5.right
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- One of the premise coincides with the conclusion.
  exact h3



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_756970563035520281955402338569 : (((p1 ∧ (((False ∧ (p4 ∧ p1)) ∧ p2) ∧ (p2 ∨ (False ∧ ((((False → p3) ∨ p2) → (((p2 ∧ p1) ∧ p1) ∧ p5)) → (p3 → p2)))))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_214183937551141253645176006472 : ((((p1 ∨ p4) → p5) → p5) ∨ (False ∨ ((((p4 ∨ p3) → (((p3 ∧ p2) ∧ (p3 ∨ (False ∧ False))) → (p1 → p3))) ∧ (p1 ∨ False)) ∨ True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_110884820996860423381265554834 : (((((((p3 → True) ∧ (p2 ∧ p4)) → ((p1 ∧ (True ∧ p4)) → p5)) ∧ (p3 ∨ (p1 ∨ ((False → p5) ∨ p5)))) → False) ∧ True) ∨ (p4 → p4)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_138054150568986331747990278905 : ((True → (True ∧ ((((True ∧ p4) ∨ p5) ∨ (p4 ∧ (((False ∧ p2) ∧ (p3 ∨ p2)) ∧ (p3 ∧ (False ∧ p1))))) ∧ True))) ∨ (p3 → (True ∨ p2))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_184179781824011243741032792119 : (((p3 → ((False ∨ (p2 → (p2 → p2))) → (p2 ∧ False))) ∨ p1) ∨ (True ∧ ((p2 ∨ ((p4 ∧ True) ∨ (False → p3))) ∧ (p4 → (True ∨ False))))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- True on the right can always be proven directly.
  apply True.intro
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
  -- Implications on the right can always be decomposed.
  intro h2
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_867560486012172949769919567946 : (((((p3 ∧ p4) ∨ ((((True → p2) ∨ (((p2 ∧ (p3 ∧ p5)) → (p5 → ((False ∨ False) ∨ (p1 → p2)))) ∧ p5)) → p5) ∨ True)) → p3) → p3) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h1
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h2 : ((p3 ∧ p4) ∨ ((((True → p2) ∨ (((p2 ∧ (p3 ∧ p5)) → (p5 → ((False ∨ False) ∨ (p1 → p2)))) ∧ p5)) → p5) ∨ True)) := by
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
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_81149440906124880504435661537 : (((True ∧ (((True ∧ (p3 → p4)) ∨ ((True ∧ p3) → False)) ∧ ((((False → p3) → p1) → (p4 → p2)) ∨ p2))) ∧ ((True ∧ p2) ∧ p3)) → p4) := by
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
  cases h6
  case inl h8 =>
    -- Conjunctions on the left can always be decomposed.
    let h9 := h8.left
    let h10 := h8.right
    -- Disjunctions on the left can always be decomposed.
    cases h7
    case inl h11 =>
      -- Conjunctions on the left can always be decomposed.
      let h12 := h3.left
      let h13 := h3.right
      -- Conjunctions on the left can always be decomposed.
      let h14 := h12.left
      let h15 := h12.right
      -- We want to use the implication h10 based on <expert-advice>. So we show its premise.
      have h16 : p3 := by
        -- One of the premise coincides with the conclusion.
        exact h13
      -- We have shown the premise of h10, we can now drive its conclusion.
      let h17 := h10 h16
      -- One of the premise coincides with the conclusion.
      exact h17
    case inr h18 =>
      -- Conjunctions on the left can always be decomposed.
      let h19 := h3.left
      let h20 := h3.right
      -- Conjunctions on the left can always be decomposed.
      let h21 := h19.left
      let h22 := h19.right
      -- We want to use the implication h10 based on <expert-advice>. So we show its premise.
      have h23 : p3 := by
        -- One of the premise coincides with the conclusion.
        exact h20
      -- We have shown the premise of h10, we can now drive its conclusion.
      let h24 := h10 h23
      -- One of the premise coincides with the conclusion.
      exact h24
  case inr h25 =>
    -- Disjunctions on the left can always be decomposed.
    cases h7
    case inl h26 =>
      -- Conjunctions on the left can always be decomposed.
      let h27 := h3.left
      let h28 := h3.right
      -- Conjunctions on the left can always be decomposed.
      let h29 := h27.left
      let h30 := h27.right
      -- We want to use the implication h25 based on <expert-advice>. So we show its premise.
      have h31 : (True ∧ p3) := by
        -- Conjunctions on the right can always be decomposed.
        apply And.intro
        -- True on the right can always be proven directly.
        apply True.intro
        -- One of the premise coincides with the conclusion.
        exact h28
      -- We have shown the premise of h25, we can now drive its conclusion.
      let h32 := h25 h31
      -- False on the left can always be used.
      apply False.elim h32
    case inr h33 =>
      -- Conjunctions on the left can always be decomposed.
      let h34 := h3.left
      let h35 := h3.right
      -- Conjunctions on the left can always be decomposed.
      let h36 := h34.left
      let h37 := h34.right
      -- We want to use the implication h25 based on <expert-advice>. So we show its premise.
      have h38 : (True ∧ p3) := by
        -- Conjunctions on the right can always be decomposed.
        apply And.intro
        -- True on the right can always be proven directly.
        apply True.intro
        -- One of the premise coincides with the conclusion.
        exact h35
      -- We have shown the premise of h25, we can now drive its conclusion.
      let h39 := h25 h38
      -- False on the left can always be used.
      apply False.elim h39



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_41355587996965375455441976296 : ((((((p3 → (p5 ∧ (p4 ∨ (True ∧ (False ∨ p5))))) → (True ∧ (False ∨ p3))) ∧ p5) → (((p1 ∨ (True ∨ p3)) → p2) ∨ True)) ∨ p2) ∨ p5) := by
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



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_673890189672855842465693637660 : (((((p1 ∨ False) → (((((p1 ∧ (p1 → p5)) → (p1 ∨ (True ∧ ((p2 ∧ p3) → p5)))) ∨ False) → p3) ∧ p5)) → (p4 ∧ (p5 ∨ False))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_157515900240188639018594043050 : (((p1 ∨ (p1 ∧ (((((p3 ∧ True) ∧ p1) → (p3 ∨ p1)) → (p5 → p1)) → p3))) ∨ (p5 ∧ p4)) ∨ (((True ∨ p1) ∨ (False ∧ p1)) ∨ p3)) := by
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
theorem thm_5_vars_56651096560800882152452312201 : ((((p2 ∨ p4) ∧ p2) ∧ (((p3 ∨ (((p4 → ((True → p2) → (p1 ∨ p1))) ∧ p2) → (((p5 → p1) ∨ p4) → p1))) → p3) ∧ True)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_217854631069613782312745126566 : (((True → (True ∨ True)) → p5) → (((((p3 ∨ p5) → p4) ∧ False) ∨ (p1 ∨ (True → p5))) → (((p4 ∧ p1) ∨ (p5 → p5)) ∨ (p4 ∧ p3)))) := by
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
    -- False on the left can always be used.
    apply False.elim h5
  case inr h6 =>
    -- Disjunctions on the left can always be decomposed.
    cases h6
    case inl h7 =>
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Implications on the right can always be decomposed.
      intro h8
      -- One of the premise coincides with the conclusion.
      exact h8
    case inr h9 =>
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Implications on the right can always be decomposed.
      intro h10
      -- One of the premise coincides with the conclusion.
      exact h10



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_345557975278928593744731927199 : (p3 → (((((p2 ∧ p4) ∧ False) ∧ p3) ∨ ((p1 ∧ ((True ∧ (True → (True → (p5 ∨ p4)))) → ((True → (p3 ∧ True)) ∧ p4))) ∧ p2)) ∨ True)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_676417452608980986906068719156 : (((((p2 → p4) ∨ ((((p2 ∨ p2) ∨ True) → (((p2 → True) ∧ (p2 ∧ p1)) ∨ (p1 → False))) ∨ True)) ∧ (((p3 ∧ p2) → p3) ∨ p3)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_249475565666002380155332952021 : ((p5 ∨ p1) ∨ ((p4 ∨ ((((False ∨ p4) ∨ True) ∧ ((((p3 ∧ p1) → (p3 ∨ p2)) → p3) ∧ p3)) ∨ (((p1 ∧ p4) ∧ p3) → p4))) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_303745715581766471031510255046 : (p1 ∨ ((((((p4 ∨ p5) → p1) ∧ (((p5 ∨ ((True ∨ p2) ∨ (((False → (p1 → True)) ∨ p5) ∨ False))) → p3) → p3)) ∧ p4) ∨ True) ∨ p2)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_38485487666759067270638515983 : ((((True ∧ (((p3 → p3) ∨ p5) ∧ (p3 ∧ ((True → True) → p2)))) ∧ (((True → (p2 → (False ∧ (True ∨ False)))) ∧ True) → False)) ∧ p1) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_178969547011032146986063311209 : (((p4 ∨ p2) ∨ ((False ∨ p5) ∧ ((p3 ∨ p3) → (True → (p4 ∧ True))))) ∨ ((p1 ∧ p5) ∨ ((False ∧ p1) ∨ (True ∨ ((p2 ∧ p4) ∧ p1))))) := by
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
theorem thm_5_vars_41672108985458122452033957013 : ((((((p5 ∧ p2) ∨ (True ∨ p1)) → False) ∨ (True → (((p4 ∨ (p5 ∨ (((True ∨ p5) ∧ (p1 ∨ False)) ∨ True))) ∨ p4) ∨ False))) ∨ p2) ∨ p4) := by
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
theorem thm_5_vars_156839213979794933696100922329 : (((p2 → (((False ∧ ((p5 ∧ p3) ∨ p4)) ∧ (((False → p1) → p1) ∨ (p3 ∨ p2))) ∨ p5)) ∧ p4) ∨ ((p4 ∨ ((p1 ∧ True) ∧ True)) → True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_205437733847302360678202043607 : (((False ∨ (p5 → p4)) → (False ∧ p4)) ∨ (((False ∧ ((p2 ∧ p2) ∧ ((p2 ∧ (p4 ∧ True)) ∧ p4))) ∧ p4) ∨ (p4 ∨ (False ∨ (p1 → p1))))) := by
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
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_137118815632731752147323197987 : ((True ∧ (((p4 → p5) → (p1 ∧ p2)) ∨ (p1 ∨ (True → ((True → (p5 → p4)) → (((False ∨ p3) → p1) → False)))))) ∨ ((False ∧ p2) → False)) := by
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
theorem thm_5_vars_255850283658817418398947944335 : ((True ∨ p1) → ((((p5 ∨ ((p1 ∧ p5) ∨ p5)) → False) ∨ (((((p2 ∧ p1) → p4) → (p5 ∨ p2)) → True) ∧ ((p3 ∨ p1) ∨ p1))) ∨ True)) := by
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
theorem thm_5_vars_833820649850179828127958702630 : ((((((p3 → (False ∨ False)) ∧ ((p5 ∨ False) → (((p5 ∨ True) → ((p4 → p2) → ((True → p3) → (p1 → True)))) ∨ p1))) ∧ p3) ∨ False) → p2) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
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
    -- We want to use the implication h5 based on <expert-advice>. So we show its premise.
    have h7 : p3 := by
      -- One of the premise coincides with the conclusion.
      exact h4
    -- We have shown the premise of h5, we can now drive its conclusion.
    let h8 := h5 h7
    -- Disjunctions on the left can always be decomposed.
    cases h8
    case inl h9 =>
      -- False on the left can always be used.
      apply False.elim h9
    case inr h10 =>
      -- False on the left can always be used.
      apply False.elim h10
  case inr h11 =>
    -- False on the left can always be used.
    apply False.elim h11
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_305588732389124825492232058346 : (p1 ∨ ((((p2 ∨ (p4 ∧ p4)) ∨ (p4 → False)) ∨ ((p4 ∧ p4) → p2)) ∨ ((p3 ∨ p1) → ((p5 → (p4 ∨ ((True ∨ p3) ∨ p3))) ∨ p3)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h2 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h2
  case inr h3 =>
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Implications on the right can always be decomposed.
    intro h4
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- True on the right can always be proven directly.
    apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_671663736093607060849315973969 : (((((((p4 → p4) ∨ (p3 ∧ (False → (p4 → (((p5 ∨ p2) ∨ (True ∧ p3)) ∧ (True ∨ p4)))))) ∨ True) ∧ p3) → ((True → p2) ∨ True)) ∨ p4) ∧ True) := by
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
    -- Disjunctions on the left can always be decomposed.
    cases h4
    case inl h5 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- True on the right can always be proven directly.
      apply True.intro
    case inr h6 =>
      -- Conjunctions on the left can always be decomposed.
      let h7 := h6.left
      let h8 := h6.right
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- True on the right can always be proven directly.
      apply True.intro
  case inr h9 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_198902663655588579055940723813 : ((p3 → (((False ∧ True) ∧ False) ∨ (p4 ∧ p3))) ∨ ((((p1 → p2) ∨ p5) ∧ ((p1 ∧ p5) ∨ (p1 ∨ ((True → False) ∨ p2)))) → (p5 ∨ p2))) := by
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
      -- Disjunctions on the left can always be decomposed.
      cases h8
      case inl h9 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- We want to use the implication h4 based on <expert-advice>. So we show its premise.
        have h10 : p1 := by
          -- One of the premise coincides with the conclusion.
          exact h9
        -- We have shown the premise of h4, we can now drive its conclusion.
        let h11 := h4 h10
        -- One of the premise coincides with the conclusion.
        exact h11
      case inr h12 =>
        -- Disjunctions on the left can always be decomposed.
        cases h12
        case inl h13 =>
          -- We want to use the implication h13 based on <expert-advice>. So we show its premise.
          have h14 : True := by
            -- True on the right can always be proven directly.
            apply True.intro
          -- We have shown the premise of h13, we can now drive its conclusion.
          let h15 := h13 h14
          -- False on the left can always be used.
          apply False.elim h15
        case inr h16 =>
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- One of the premise coincides with the conclusion.
          exact h16
  case inr h17 =>
    -- Disjunctions on the left can always be decomposed.
    cases h3
    case inl h18 =>
      -- Conjunctions on the left can always be decomposed.
      let h19 := h18.left
      let h20 := h18.right
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- One of the premise coincides with the conclusion.
      exact h20
    case inr h21 =>
      -- Disjunctions on the left can always be decomposed.
      cases h21
      case inl h22 =>
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- One of the premise coincides with the conclusion.
        exact h17
      case inr h23 =>
        -- Disjunctions on the left can always be decomposed.
        cases h23
        case inl h24 =>
          -- Show the left disjunct based on <expert-advice>.
          apply Or.inl
          -- One of the premise coincides with the conclusion.
          exact h17
        case inr h25 =>
          -- Show the left disjunct based on <expert-advice>.
          apply Or.inl
          -- One of the premise coincides with the conclusion.
          exact h17



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_112139794858839880930827789655 : (((p1 ∧ (((((p5 ∨ p3) ∨ True) ∧ (p1 ∨ (((((p2 ∧ False) ∧ p3) ∧ True) ∨ (p4 → True)) ∨ p1))) ∨ p2) ∧ p2)) ∨ False) ∨ (False → True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_134111124902378413666165019771 : ((((((p4 ∧ True) → p5) ∨ (((p2 → (p3 ∨ False)) ∨ (False ∨ (True ∨ p4))) ∨ (p1 → p5))) ∧ (p1 ∧ p1)) ∨ True) ∨ ((True → p5) → p4)) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_628448616408739617452678199231 : (((((p3 ∧ (((p4 → (True ∧ p4)) ∧ (p2 ∧ ((p4 → (p3 ∨ p5)) ∨ p4))) ∧ (((p4 → (p2 → p2)) ∧ p1) → p1))) ∧ p3) → False) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_40143613804922086183271671869 : ((((((False ∧ p3) ∧ ((True → p5) → ((p2 ∨ ((p4 → True) ∨ p3)) → p3))) ∧ ((((p5 → p1) ∨ p2) ∧ p3) ∧ False)) ∧ p4) ∨ True) ∨ p2) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_650201414765725836834793342454 : ((((((((p3 → p3) → ((p3 ∨ p5) ∧ (False ∧ p5))) ∧ (p5 ∧ p1)) → (p2 ∨ p2)) ∨ (True ∨ (True → (p5 → p1)))) ∧ (False ∨ p1)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_47989447468735494228908755207 : ((((((p4 ∨ ((p4 → p5) ∧ ((p4 ∧ True) ∧ p5))) → (p5 → p4)) → p1) ∧ ((p3 ∧ (p1 ∧ (p4 ∧ p2))) → True)) → (p1 ∨ p5)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_52399929705914630890679609729 : ((((False ∧ ((p4 ∧ True) → p1)) ∨ (((p1 → p3) ∧ p2) ∨ (True ∨ p1))) ∧ (((p3 ∧ ((p5 ∨ p2) ∨ p5)) ∨ (p1 ∨ p4)) → p1)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_49441970667787828853431913225 : ((((((p1 → True) ∨ (p5 ∨ (p2 → ((p3 ∨ p2) ∨ (False ∧ p3))))) → (((p5 ∨ p2) ∧ True) → False)) ∨ p3) → ((p5 ∨ p3) ∧ p1)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_136785377787184146059304803312 : (((False → p2) ∧ (p2 → (p2 ∧ (True ∧ (False ∨ (((False → p1) → (p1 ∧ ((p1 ∨ (True → p3)) ∧ False))) → False)))))) ∨ (p2 → (p2 → p4))) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h1
  -- False on the left can always be used.
  apply False.elim h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- One of the premise coincides with the conclusion.
  exact h2
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h3
  -- We want to use the implication h3 based on <expert-advice>. So we show its premise.
  have h4 : (False → p1) := by
    -- Implications on the right can always be decomposed.
    intro h5
    -- False on the left can always be used.
    apply False.elim h5
  -- We have shown the premise of h3, we can now drive its conclusion.
  let h6 := h3 h4
  -- We need to get the right conjuct of h6 based on <expert-advice>.
  let h7 := h6.right
  -- We need to get the right conjuct of h7 based on <expert-advice>.
  let h8 := h7.right
  -- False on the left can always be used.
  apply False.elim h8



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_687715302821083528085437820848 : ((((((p1 ∨ p5) ∨ ((((p4 ∧ p4) ∧ (p2 ∨ False)) ∧ True) ∨ p3)) ∧ (p1 ∨ True)) ∧ ((((p3 → False) → (p1 → p4)) → False) → p4)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_233232508553661877813471938841 : ((p5 ∧ (p5 → False)) → (p2 ∨ (((((p1 ∧ (p3 ∧ (p1 ∧ ((p1 ∨ p1) ∨ ((p5 ∨ p5) → p3))))) ∧ (p4 ∧ p4)) ∨ p4) ∧ True) → p2))) := by
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
theorem thm_5_vars_67729042889652761746589555130 : ((p2 → (((((True → False) ∧ p4) ∨ p4) ∧ ((((((False ∨ p1) → (False ∨ (True ∧ False))) → p5) ∧ p4) ∨ p3) ∧ (True ∨ p4))) ∧ p4)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_165425079411967742075455206971 : (((((p3 → False) ∧ p1) ∨ ((((p1 → p2) ∧ p4) ∧ p1) ∨ p2)) → (p4 ∧ (p4 → p1))) ∨ (p2 ∨ ((p5 ∧ ((p3 ∨ p1) ∨ True)) → True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_707693451053181055477234132010 : (((((p4 → p2) ∨ ((True ∧ p1) ∨ (p4 ∨ p2))) ∨ (False ∧ (p3 ∧ (((p3 ∨ (True ∧ p2)) ∨ p1) ∨ (p2 ∨ ((False → p1) → p1)))))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_111146392306996862097599704800 : ((((((True ∨ (False ∨ True)) ∧ p1) ∧ p5) ∨ (((p1 → (p4 ∨ p3)) ∧ ((p2 ∨ False) → (p5 → (p5 ∨ p3)))) → p3)) ∧ False) ∨ (p3 ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_260890998776326926267957149739 : ((p4 → False) → ((((p2 ∨ (p4 ∧ p1)) ∧ True) ∨ (((True → (p4 ∧ False)) ∧ ((p4 ∨ p1) → p5)) → ((True → (p3 ∧ False)) ∨ p2))) ∨ p5)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h2
  -- Conjunctions on the left can always be decomposed.
  let h3 := h2.left
  let h4 := h2.right
  -- We want to use the implication h3 based on <expert-advice>. So we show its premise.
  have h5 : True := by
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h3, we can now drive its conclusion.
  let h6 := h3 h5
  -- We need to get the right conjuct of h6 based on <expert-advice>.
  let h7 := h6.right
  -- False on the left can always be used.
  apply False.elim h7



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_111527300857292091180851038905 : ((((((p5 ∧ p4) ∨ (False ∨ ((p1 ∨ False) ∨ ((p5 ∨ True) ∧ ((p2 ∨ (False → p4)) ∧ (p4 ∧ p1)))))) ∧ p4) ∧ p4) ∨ True) ∨ (p3 ∨ True)) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



