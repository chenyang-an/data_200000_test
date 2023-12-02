variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_119105845237816271648999232926 : ((p1 → ((p2 ∧ (p5 ∨ p3)) ∨ (p3 ∧ (p4 ∨ (p5 ∨ (p1 ∧ ((p2 ∨ p4) → ((p4 ∨ (p5 → (p5 ∨ p2))) ∧ True)))))))) ∨ (False → p3)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_41680559149513759270871229994 : (((((False → p3) → (p5 ∨ (p5 → p2))) ∨ (p5 ∧ (((p1 ∧ (((p3 ∨ False) ∧ (True ∨ p3)) → p2)) ∧ (p5 ∨ p4)) → p5))) ∨ p5) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_125640439510554299186287477849 : (((p1 ∧ p5) ∨ (p5 ∧ ((p5 ∨ (p5 ∨ (p3 → (p3 ∨ ((p4 ∨ p5) → p3))))) ∨ (((p5 ∧ p2) ∨ (True → p1)) ∧ p1)))) → (p4 ∨ p5)) := by
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
    -- One of the premise coincides with the conclusion.
    exact h4
  case inr h5 =>
    -- Conjunctions on the left can always be decomposed.
    let h6 := h5.left
    let h7 := h5.right
    -- Disjunctions on the left can always be decomposed.
    cases h7
    case inl h8 =>
      -- Disjunctions on the left can always be decomposed.
      cases h8
      case inl h9 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- One of the premise coincides with the conclusion.
        exact h9
      case inr h10 =>
        -- Disjunctions on the left can always be decomposed.
        cases h10
        case inl h11 =>
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- One of the premise coincides with the conclusion.
          exact h11
        case inr h12 =>
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- One of the premise coincides with the conclusion.
          exact h6
    case inr h13 =>
      -- Conjunctions on the left can always be decomposed.
      let h14 := h13.left
      let h15 := h13.right
      -- Disjunctions on the left can always be decomposed.
      cases h14
      case inl h16 =>
        -- Conjunctions on the left can always be decomposed.
        let h17 := h16.left
        let h18 := h16.right
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- One of the premise coincides with the conclusion.
        exact h17
      case inr h19 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- One of the premise coincides with the conclusion.
        exact h6



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_63102626826514475862087994351 : ((p5 ∧ ((False ∨ ((False ∨ ((p1 ∨ ((((False ∧ ((p5 ∧ p4) → (False ∧ p1))) ∧ p4) ∧ True) ∧ p2)) ∧ (p5 ∨ p2))) ∨ False)) ∨ False)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_318193239651853832753871878332 : (p4 ∨ (((((False ∧ (p4 ∨ p1)) → (p2 ∨ (p2 ∧ ((p5 ∧ p3) → False)))) → False) ∧ (True ∨ ((p4 → True) ∧ ((True ∨ True) ∨ p4)))) → p5)) := by
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
    -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
    have h5 : ((False ∧ (p4 ∨ p1)) → (p2 ∨ (p2 ∧ ((p5 ∧ p3) → False)))) := by
      -- Implications on the right can always be decomposed.
      intro h6
      -- Conjunctions on the left can always be decomposed.
      let h7 := h6.left
      let h8 := h6.right
      -- False on the left can always be used.
      apply False.elim h7
    -- We have shown the premise of h2, we can now drive its conclusion.
    let h9 := h2 h5
    -- False on the left can always be used.
    apply False.elim h9
  case inr h10 =>
    -- Conjunctions on the left can always be decomposed.
    let h11 := h10.left
    let h12 := h10.right
    -- Disjunctions on the left can always be decomposed.
    cases h12
    case inl h13 =>
      -- Disjunctions on the left can always be decomposed.
      cases h13
      case inl h14 =>
        -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
        have h15 : ((False ∧ (p4 ∨ p1)) → (p2 ∨ (p2 ∧ ((p5 ∧ p3) → False)))) := by
          -- Implications on the right can always be decomposed.
          intro h16
          -- Conjunctions on the left can always be decomposed.
          let h17 := h16.left
          let h18 := h16.right
          -- False on the left can always be used.
          apply False.elim h17
        -- We have shown the premise of h2, we can now drive its conclusion.
        let h19 := h2 h15
        -- False on the left can always be used.
        apply False.elim h19
      case inr h20 =>
        -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
        have h21 : ((False ∧ (p4 ∨ p1)) → (p2 ∨ (p2 ∧ ((p5 ∧ p3) → False)))) := by
          -- Implications on the right can always be decomposed.
          intro h22
          -- Conjunctions on the left can always be decomposed.
          let h23 := h22.left
          let h24 := h22.right
          -- False on the left can always be used.
          apply False.elim h23
        -- We have shown the premise of h2, we can now drive its conclusion.
        let h25 := h2 h21
        -- False on the left can always be used.
        apply False.elim h25
    case inr h26 =>
      -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
      have h27 : ((False ∧ (p4 ∨ p1)) → (p2 ∨ (p2 ∧ ((p5 ∧ p3) → False)))) := by
        -- Implications on the right can always be decomposed.
        intro h28
        -- Conjunctions on the left can always be decomposed.
        let h29 := h28.left
        let h30 := h28.right
        -- False on the left can always be used.
        apply False.elim h29
      -- We have shown the premise of h2, we can now drive its conclusion.
      let h31 := h2 h27
      -- False on the left can always be used.
      apply False.elim h31



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_695235603699584883263571453700 : ((((((False ∨ (p4 ∨ ((p3 ∧ p2) ∨ (p4 ∧ (p5 ∨ p2))))) ∧ False) → p4) → (((False ∨ ((p4 ∧ p4) ∨ p3)) ∨ (False ∨ p3)) ∧ p2)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_41989902065064851581426259691 : ((((p5 ∨ p4) ∧ (((p5 → False) → ((False ∧ (p2 ∧ p3)) ∨ ((False ∨ p2) ∨ (p4 ∨ (((False ∧ p2) ∨ True) ∨ p5))))) → p3)) ∨ True) ∨ p5) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_137412764275459681654345125504 : ((p4 ∧ (((((True → (p5 → ((((p2 ∨ (p4 ∧ True)) → p5) → (p5 ∨ p2)) ∨ True))) ∨ p5) ∨ p5) → p2) ∧ p1)) ∨ (p5 ∨ (True ∨ False))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_114125251865805842526026146572 : (((p2 → ((p2 ∧ ((p3 ∨ p5) ∧ (p4 → ((p5 ∧ False) ∧ (True ∨ p5))))) → (True → (p4 ∨ p1)))) ∨ (p3 ∨ (p4 ∧ False))) ∨ (p5 → True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_147354443131973817113909447533 : ((((((p4 ∨ ((False → p3) ∨ (p3 → (p1 ∧ True)))) → (p3 → p1)) ∨ p3) ∨ (False ∨ (False ∧ False))) ∨ True) ∨ ((True ∧ (p1 → True)) → p4)) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_352811068155757591348169074222 : (p4 → ((p4 ∨ p4) → ((p4 ∧ ((p4 ∨ p5) → (p4 → (p4 ∧ (p3 ∧ False))))) → ((p1 ∨ p2) ∧ (p2 ∧ ((p4 ∧ p3) ∨ (p4 ∨ p5))))))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Implications on the right can always be decomposed.
  intro h3
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Conjunctions on the left can always be decomposed.
  let h4 := h3.left
  let h5 := h3.right
  -- Disjunctions on the left can always be decomposed.
  cases h2
  case inl h6 =>
    -- We want to use the implication h5 based on <expert-advice>. So we show its premise.
    have h7 : (p4 ∨ p5) := by
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- One of the premise coincides with the conclusion.
      exact h1
    -- We have shown the premise of h5, we can now drive its conclusion.
    let h8 := h5 h7
    -- We want to use the implication h8 based on <expert-advice>. So we show its premise.
    have h9 : p4 := by
      -- One of the premise coincides with the conclusion.
      exact h1
    -- We have shown the premise of h8, we can now drive its conclusion.
    let h10 := h8 h9
    -- We need to get the right conjuct of h10 based on <expert-advice>.
    let h11 := h10.right
    -- We need to get the right conjuct of h11 based on <expert-advice>.
    let h12 := h11.right
    -- False on the left can always be used.
    apply False.elim h12
  case inr h13 =>
    -- We want to use the implication h5 based on <expert-advice>. So we show its premise.
    have h14 : (p4 ∨ p5) := by
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- One of the premise coincides with the conclusion.
      exact h1
    -- We have shown the premise of h5, we can now drive its conclusion.
    let h15 := h5 h14
    -- We want to use the implication h15 based on <expert-advice>. So we show its premise.
    have h16 : p4 := by
      -- One of the premise coincides with the conclusion.
      exact h1
    -- We have shown the premise of h15, we can now drive its conclusion.
    let h17 := h15 h16
    -- We need to get the right conjuct of h17 based on <expert-advice>.
    let h18 := h17.right
    -- We need to get the right conjuct of h18 based on <expert-advice>.
    let h19 := h18.right
    -- False on the left can always be used.
    apply False.elim h19
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Conjunctions on the left can always be decomposed.
  let h20 := h3.left
  let h21 := h3.right
  -- Disjunctions on the left can always be decomposed.
  cases h2
  case inl h22 =>
    -- We want to use the implication h21 based on <expert-advice>. So we show its premise.
    have h23 : (p4 ∨ p5) := by
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- One of the premise coincides with the conclusion.
      exact h1
    -- We have shown the premise of h21, we can now drive its conclusion.
    let h24 := h21 h23
    -- We want to use the implication h24 based on <expert-advice>. So we show its premise.
    have h25 : p4 := by
      -- One of the premise coincides with the conclusion.
      exact h1
    -- We have shown the premise of h24, we can now drive its conclusion.
    let h26 := h24 h25
    -- We need to get the right conjuct of h26 based on <expert-advice>.
    let h27 := h26.right
    -- We need to get the right conjuct of h27 based on <expert-advice>.
    let h28 := h27.right
    -- False on the left can always be used.
    apply False.elim h28
  case inr h29 =>
    -- We want to use the implication h21 based on <expert-advice>. So we show its premise.
    have h30 : (p4 ∨ p5) := by
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- One of the premise coincides with the conclusion.
      exact h1
    -- We have shown the premise of h21, we can now drive its conclusion.
    let h31 := h21 h30
    -- We want to use the implication h31 based on <expert-advice>. So we show its premise.
    have h32 : p4 := by
      -- One of the premise coincides with the conclusion.
      exact h1
    -- We have shown the premise of h31, we can now drive its conclusion.
    let h33 := h31 h32
    -- We need to get the right conjuct of h33 based on <expert-advice>.
    let h34 := h33.right
    -- We need to get the right conjuct of h34 based on <expert-advice>.
    let h35 := h34.right
    -- False on the left can always be used.
    apply False.elim h35
  -- Conjunctions on the left can always be decomposed.
  let h36 := h3.left
  let h37 := h3.right
  -- Disjunctions on the left can always be decomposed.
  cases h2
  case inl h38 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- One of the premise coincides with the conclusion.
    exact h1
  case inr h39 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- One of the premise coincides with the conclusion.
    exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_159320082856943402308110308678 : ((p5 → (((((p1 ∨ p4) ∨ p2) → True) → p1) ∧ (((p3 ∧ p3) ∨ (p1 ∨ True)) → (p2 → p2)))) ∨ ((False → False) ∨ ((p5 ∧ p3) ∨ p5))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_159041954636754610410500609231 : ((p5 ∨ (((p2 → p2) ∧ ((((p3 ∨ p4) → p2) ∨ (False → (p1 ∨ p2))) → (p5 ∧ p3))) ∧ p3)) ∨ (p3 → ((True ∨ p2) ∨ (True ∨ True)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_183852251693830463889445129916 : ((((((p5 → p3) ∧ p3) ∧ (p4 → p2)) → (p2 ∨ False)) ∧ True) ∨ ((False → ((((p1 ∧ ((p5 → p1) ∨ False)) → p1) → p3) → p2)) ∨ p1)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_322423330486388004041419658288 : (p5 ∨ (((p1 ∧ ((False → (False ∨ p1)) ∧ (p4 ∨ p1))) ∨ ((((p4 → ((p1 ∨ (True → False)) → False)) ∧ p2) ∨ (p2 → p3)) ∨ p3)) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_179807194341574016742985728117 : ((((p5 → False) ∨ (p5 ∧ ((p5 ∨ ((p5 ∨ p1) ∨ p2)) → True))) ∧ p4) → ((p2 ∨ ((p2 ∧ (p3 → p5)) ∨ True)) ∧ ((p2 ∧ p4) → p2))) := by
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
    -- True on the right can always be proven directly.
    apply True.intro
  case inr h5 =>
    -- Conjunctions on the left can always be decomposed.
    let h6 := h5.left
    let h7 := h5.right
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro
  -- Implications on the right can always be decomposed.
  intro h8
  -- Conjunctions on the left can always be decomposed.
  let h9 := h8.left
  let h10 := h8.right
  -- Conjunctions on the left can always be decomposed.
  let h11 := h1.left
  let h12 := h1.right
  -- Disjunctions on the left can always be decomposed.
  cases h11
  case inl h13 =>
    -- One of the premise coincides with the conclusion.
    exact h9
  case inr h14 =>
    -- Conjunctions on the left can always be decomposed.
    let h15 := h14.left
    let h16 := h14.right
    -- One of the premise coincides with the conclusion.
    exact h9



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_182513102767868099559726796103 : ((((False ∧ (True → (p1 → p5))) → (False → p3)) → (p3 ∨ True)) ∧ (((p3 → p2) → p2) → ((p5 → p5) → (p3 ∨ (p1 → (p2 → p1)))))) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- Implications on the right can always be decomposed.
  intro h2
  -- Implications on the right can always be decomposed.
  intro h3
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h4
  -- Implications on the right can always be decomposed.
  intro h5
  -- One of the premise coincides with the conclusion.
  exact h4



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_218324617464853192161184158626 : (((True → p5) ∨ (p3 → p2)) → ((p1 → ((p4 → True) ∨ p4)) ∧ (((p4 ∧ (((p1 → p3) ∧ p4) ∨ p2)) ∧ p1) ∨ (True ∨ (True ∨ True))))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h2
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h3 =>
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Implications on the right can always be decomposed.
    intro h4
    -- True on the right can always be proven directly.
    apply True.intro
  case inr h5 =>
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Implications on the right can always be decomposed.
    intro h6
    -- True on the right can always be proven directly.
    apply True.intro
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h7 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- True on the right can always be proven directly.
    apply True.intro
  case inr h8 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- True on the right can always be proven directly.
    apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_112785590518319634357232747967 : ((((((((False ∧ p4) ∧ True) ∨ p2) → False) ∧ p5) → (((False ∧ (((p3 → True) ∨ (p2 ∧ p1)) ∧ p5)) ∨ True) ∧ True)) → p2) ∨ (True ∨ p2)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_137884655685969742921375324025 : ((p4 ∨ (((p2 ∨ p3) ∧ ((((p1 ∧ p2) ∧ p1) ∧ (p5 → (p2 ∧ p2))) ∨ (((False ∧ p4) ∨ p1) ∧ True))) ∨ p2)) ∨ (True ∨ (p5 ∨ p5))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_234435197523186740842577834872 : ((p2 → (p2 ∧ False)) → ((((False ∨ ((True ∧ False) ∨ p3)) ∧ ((((p3 → p2) → p4) ∧ False) ∧ (p3 ∧ True))) ∨ ((p1 → p1) → True)) ∧ True)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h2
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_612560445399840184035244881201 : (((((((p1 → ((((False → False) ∨ (True → (p4 → p3))) ∨ (p2 ∨ (p1 ∧ p1))) → p2)) ∨ (p4 ∨ p4)) → p4) ∨ (False → p4)) ∨ True) ∨ p2) ∧ True) := by
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
theorem thm_5_vars_111615817716439981820109598210 : (((((((p5 → ((p4 ∧ p2) ∧ (p1 → ((False ∧ False) ∨ p4)))) ∧ ((p3 ∧ p4) ∨ (p1 ∨ p3))) → p4) → p3) ∨ p2) ∨ p3) ∨ (p1 ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_765327746792687029713441686048 : (((p4 ∧ (((((p4 ∨ True) ∨ False) ∨ p4) ∧ (True ∧ ((p3 ∨ ((p5 ∧ (p1 ∧ p3)) → p4)) ∨ (p4 → p5)))) ∨ ((p5 ∨ True) → p5))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_231818709044502780109949184869 : (((p4 ∧ p5) → p4) → (p3 ∨ ((((p4 → ((p4 ∨ p4) → p5)) ∧ p2) ∨ ((p4 → (p3 ∨ p1)) ∨ p4)) ∨ (p1 → ((p3 ∧ p2) → p2))))) := by
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
theorem thm_5_vars_48555852130756234356963084039 : ((((((p2 ∨ p4) ∨ (((p4 ∨ (((True ∧ True) ∨ (True → p1)) → p2)) → p2) ∨ p2)) → (p3 ∧ p5)) → False) ∧ (p3 → (p3 ∨ p2))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_111959060531985078870748678672 : ((((((p1 → ((True → True) ∨ p3)) → p1) ∧ p4) → ((p4 → (p3 ∧ False)) → ((p5 ∨ True) ∧ (False ∧ (p2 ∨ p1))))) ∨ False) ∨ (p1 ∧ p3)) := by
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
  -- Conjunctions on the left can always be decomposed.
  let h3 := h1.left
  let h4 := h1.right
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Conjunctions on the left can always be decomposed.
  let h5 := h1.left
  let h6 := h1.right
  -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
  have h7 : p4 := by
    -- One of the premise coincides with the conclusion.
    exact h6
  -- We have shown the premise of h2, we can now drive its conclusion.
  let h8 := h2 h7
  -- We need to get the right conjuct of h8 based on <expert-advice>.
  let h9 := h8.right
  -- False on the left can always be used.
  apply False.elim h9
  -- Conjunctions on the left can always be decomposed.
  let h10 := h1.left
  let h11 := h1.right
  -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
  have h12 : p4 := by
    -- One of the premise coincides with the conclusion.
    exact h11
  -- We have shown the premise of h2, we can now drive its conclusion.
  let h13 := h2 h12
  -- We need to get the right conjuct of h13 based on <expert-advice>.
  let h14 := h13.right
  -- False on the left can always be used.
  apply False.elim h14



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_639975007407534671701397691059 : (((((False ∨ (False → False)) ∨ (((False → p2) ∨ p4) → (((((p2 ∧ (p5 ∨ p2)) ∧ p1) ∧ (False ∧ (p1 ∨ True))) → p2) ∨ p4))) → p4) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_314232981700210253909795226340 : (p3 ∨ (((p2 → (((p4 → p3) → (((p3 ∧ p4) → p4) ∧ (((p1 ∧ p3) ∧ (p3 → False)) ∨ p2))) ∧ p2)) ∨ p1) ∨ (p4 ∨ (p2 ∨ p1)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
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
  -- Implications on the right can always be decomposed.
  intro h3
  -- Conjunctions on the left can always be decomposed.
  let h4 := h3.left
  let h5 := h3.right
  -- One of the premise coincides with the conclusion.
  exact h5
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h1
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_171080615017327529958620408067 : ((p5 ∨ (p2 → (((p1 ∧ (p1 ∨ p2)) → (p3 → ((p5 ∨ p4) ∨ False))) ∨ p2))) ∧ ((p1 → ((p5 ∨ True) ∨ (p2 ∨ p5))) ∨ (p3 ∨ p2))) := by
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
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h2
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_307823748116076739012076241645 : (p1 ∨ (p4 → ((p2 ∨ p5) → (((p3 ∧ p3) ∨ p1) ∨ ((((True ∨ p3) ∨ (p1 ∧ False)) ∧ (False → (p4 ∧ p1))) ∨ ((p2 ∧ p1) ∨ True)))))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
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
    -- True on the right can always be proven directly.
    apply True.intro
  case inr h4 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_184014956379178625292667838069 : (((((p4 → p2) → (True → ((p2 ∨ p5) ∧ p3))) ∨ True) ∨ p3) ∨ (p5 ∨ (((p3 → (p3 ∧ ((p1 ∧ p4) ∧ p1))) → (True ∧ p3)) ∨ p5))) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_140296095776061957650478597415 : ((((p3 → (p1 ∨ p4)) ∨ ((((p2 → ((p2 ∧ p1) ∨ p4)) → (p4 ∧ p4)) → p4) ∨ p3)) ∧ ((p4 → p1) ∨ True)) → ((p5 ∨ p4) ∨ True)) := by
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
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- True on the right can always be proven directly.
      apply True.intro
    case inr h6 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- True on the right can always be proven directly.
      apply True.intro
  case inr h7 =>
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
      cases h3
      case inl h12 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- True on the right can always be proven directly.
        apply True.intro
      case inr h13 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- True on the right can always be proven directly.
        apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_117838197343452227403504086261 : ((p4 ∧ (p4 ∨ ((((p3 ∨ (True ∨ (False → ((p4 → p3) → p1)))) ∧ (True → (True ∧ (p3 ∧ False)))) → p3) → (p2 → p3)))) ∨ (False → False)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_485544334363596724719418594056 : (((((p1 ∧ (p4 ∨ (p4 ∨ p1))) ∨ False) ∨ (((False ∨ (False ∧ (False ∧ p1))) ∧ (((p2 ∨ True) → (p2 ∧ p3)) ∨ p2)) → (True → True))) ∧ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_66411430736205143098751498327 : ((p5 ∨ (p2 → (((((p2 ∧ True) ∧ p5) ∨ ((p1 → p5) → False)) → (((True → False) → True) ∨ p2)) → (p4 ∧ ((False ∨ p4) → p2))))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_684948210515720577488146377020 : ((((p2 ∧ ((False ∨ True) ∨ ((False → (p5 ∧ (p4 ∨ (p3 ∨ (p3 ∧ (p2 → p2)))))) → p4))) ∨ (p4 → ((False ∨ (p2 ∧ False)) ∨ p4))) ∨ p3) ∧ True) := by
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
  -- One of the premise coincides with the conclusion.
  exact h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_40319471241669173031466619664 : (((((p3 ∨ ((((((p1 → (p4 → p1)) → True) ∨ ((p5 ∨ p5) → ((True → p1) ∧ p2))) ∧ True) → p4) ∧ p1)) ∧ False) ∨ True) ∨ True) ∨ p4) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_59956357796817158806440038215 : (((True ∨ p3) → (p3 ∨ (True → (True → ((((p1 → (p5 ∧ (p1 ∨ ((((False ∨ p3) → p5) ∧ p2) ∨ p2)))) → p4) → p1) ∨ True))))) ∨ p4) := by
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
    -- Implications on the right can always be decomposed.
    intro h4
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro
  case inr h5 =>
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- One of the premise coincides with the conclusion.
    exact h5



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_168748708617084020904010804270 : ((False ∨ ((p5 ∨ p1) ∧ ((((True ∨ False) ∨ p1) → (False ∧ p1)) ∧ ((p4 ∧ True) ∨ p2)))) → ((p2 → ((p3 ∨ p2) ∧ (p4 ∨ False))) ∨ p4)) := by
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
    -- Disjunctions on the left can always be decomposed.
    cases h4
    case inl h6 =>
      -- Conjunctions on the left can always be decomposed.
      let h7 := h5.left
      let h8 := h5.right
      -- Disjunctions on the left can always be decomposed.
      cases h8
      case inl h9 =>
        -- Conjunctions on the left can always be decomposed.
        let h10 := h9.left
        let h11 := h9.right
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- One of the premise coincides with the conclusion.
        exact h10
      case inr h12 =>
        -- We want to use the implication h7 based on <expert-advice>. So we show its premise.
        have h13 : ((True ∨ False) ∨ p1) := by
          -- Show the left disjunct based on <expert-advice>.
          apply Or.inl
          -- Show the left disjunct based on <expert-advice>.
          apply Or.inl
          -- True on the right can always be proven directly.
          apply True.intro
        -- We have shown the premise of h7, we can now drive its conclusion.
        let h14 := h7 h13
        -- We need to get the left conjuct of h14 based on <expert-advice>.
        let h15 := h14.left
        -- False on the left can always be used.
        apply False.elim h15
    case inr h16 =>
      -- Conjunctions on the left can always be decomposed.
      let h17 := h5.left
      let h18 := h5.right
      -- Disjunctions on the left can always be decomposed.
      cases h18
      case inl h19 =>
        -- Conjunctions on the left can always be decomposed.
        let h20 := h19.left
        let h21 := h19.right
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- One of the premise coincides with the conclusion.
        exact h20
      case inr h22 =>
        -- We want to use the implication h17 based on <expert-advice>. So we show its premise.
        have h23 : ((True ∨ False) ∨ p1) := by
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- One of the premise coincides with the conclusion.
          exact h16
        -- We have shown the premise of h17, we can now drive its conclusion.
        let h24 := h17 h23
        -- We need to get the left conjuct of h24 based on <expert-advice>.
        let h25 := h24.left
        -- False on the left can always be used.
        apply False.elim h25



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_174084752873151095684946620825 : ((((((p2 → False) ∨ (True → p4)) ∧ (False ∨ p5)) ∧ (p1 → False)) ∧ (p4 ∧ p5)) → ((((True ∨ p3) ∧ False) ∨ (False ∧ p2)) ∨ (False → False))) := by
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
  -- Disjunctions on the left can always be decomposed.
  cases h6
  case inl h8 =>
    -- Disjunctions on the left can always be decomposed.
    cases h7
    case inl h9 =>
      -- False on the left can always be used.
      apply False.elim h9
    case inr h10 =>
      -- Conjunctions on the left can always be decomposed.
      let h11 := h3.left
      let h12 := h3.right
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Implications on the right can always be decomposed.
      intro h13
      -- False on the left can always be used.
      apply False.elim h13
  case inr h14 =>
    -- Disjunctions on the left can always be decomposed.
    cases h7
    case inl h15 =>
      -- False on the left can always be used.
      apply False.elim h15
    case inr h16 =>
      -- Conjunctions on the left can always be decomposed.
      let h17 := h3.left
      let h18 := h3.right
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Implications on the right can always be decomposed.
      intro h19
      -- False on the left can always be used.
      apply False.elim h19



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_704917920378675588823746032861 : ((((p4 ∨ ((False ∨ (p2 ∨ (False → p1))) ∧ (True ∧ p2))) → (False ∨ ((p3 → ((((p3 → True) → p5) → (p4 → p4)) ∧ p4)) ∨ p4))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_58124538542752624434553210324 : (((p2 ∧ False) ∧ ((((p1 ∧ ((((True → ((p3 ∧ (((p4 ∧ True) ∧ p2) ∧ p2)) ∨ False)) ∨ p1) → True) ∧ False)) → p4) → p3) ∨ True)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_624695184355370664358239059440 : ((((p4 ∨ (False ∨ (((p1 → (p1 → ((True ∨ ((p1 ∧ True) ∧ False)) ∨ p3))) ∧ p5) → (p2 ∧ (p5 → (p5 ∧ (p5 ∧ p1))))))) ∨ True) ∨ p3) ∧ True) := by
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
theorem thm_5_vars_157868049520100853493644629425 : (((((p3 → p4) ∧ ((p5 → (p3 ∧ p5)) ∧ p2)) ∧ p1) ∨ ((p2 ∧ (p2 ∨ (p1 ∨ False))) ∧ p2)) ∨ (p5 → (((p2 ∨ p4) ∨ True) ∧ p5))) := by
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
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_41327942247412319655463310024 : ((((p2 → (((p4 ∨ (p2 ∨ (p1 ∧ ((p2 ∨ p3) ∨ p3)))) ∧ p5) → (p3 → p4))) ∧ ((False ∧ p4) → ((True ∨ p5) → True))) ∨ p5) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_326992390543615645485552407464 : (True → ((((p4 → p5) → ((((True → ((True ∧ p3) ∨ p1)) → p5) ∧ (p1 ∨ p3)) ∧ (p5 ∨ p3))) ∧ (p4 ∨ ((p1 → True) ∨ p4))) ∨ True)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_121657035990320736771353344194 : (((((True ∨ p3) ∧ (p5 → ((False ∧ p5) ∧ (p2 ∧ ((p5 → p1) ∨ p2))))) → (p1 ∨ (((False → p5) ∨ p2) ∨ p3))) → False) → (p4 ∨ p1)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h2 : (((True ∨ p3) ∧ (p5 → ((False ∧ p5) ∧ (p2 ∧ ((p5 → p1) ∨ p2))))) → (p1 ∨ (((False → p5) ∨ p2) ∨ p3))) := by
    -- Implications on the right can always be decomposed.
    intro h3
    -- Conjunctions on the left can always be decomposed.
    let h4 := h3.left
    let h5 := h3.right
    -- Disjunctions on the left can always be decomposed.
    cases h4
    case inl h6 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- Implications on the right can always be decomposed.
      intro h7
      -- False on the left can always be used.
      apply False.elim h7
    case inr h8 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- One of the premise coincides with the conclusion.
      exact h8
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h9 := h1 h2
  -- False on the left can always be used.
  apply False.elim h9



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_51195793078824901771857845571 : ((((p5 → ((True → p3) ∨ (((False ∨ (p4 ∨ p4)) → False) → p1))) → (p5 ∨ (p1 ∧ p1))) ∨ (p3 → ((p2 ∨ False) → (p2 ∨ p2)))) ∨ p3) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
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
    exact h3
  case inr h4 =>
    -- False on the left can always be used.
    apply False.elim h4



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_40438328789508486121523792549 : (((((((False → (True ∧ p3)) → (p4 ∨ p3)) ∧ p3) ∧ ((((False → p5) ∨ (p2 ∨ (p2 ∧ (p3 ∨ False)))) ∨ p1) → p5)) ∨ True) ∨ True) ∨ p1) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_98820027201623039199002664587 : ((True → (((p3 → p5) ∨ ((((p2 ∨ p3) ∨ False) → (((p3 ∧ (True → p1)) → p3) → ((p4 ∧ p3) ∧ False))) ∨ (p1 → p1))) ∧ False)) → p2) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h2 : True := by
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h3 := h1 h2
  -- We need to get the right conjuct of h3 based on <expert-advice>.
  let h4 := h3.right
  -- False on the left can always be used.
  apply False.elim h4



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_68437105459497649009194429965 : ((p3 → ((p2 → p2) → (((p5 ∧ ((p1 → ((p1 ∧ p2) → ((p5 ∧ p1) ∨ p3))) → (p3 ∧ p1))) ∧ p4) ∨ (True → (p5 → p4))))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_150720306478354010462550450566 : (((((True ∨ p3) ∨ (p5 ∨ (((p4 → (((p3 → p5) ∨ (p4 → p4)) ∨ p2)) ∨ p1) ∧ p4))) ∧ True) ∨ p3) → (p3 → (p5 ∨ (p5 ∨ True)))) := by
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
    cases h4
    case inl h6 =>
      -- Disjunctions on the left can always be decomposed.
      cases h6
      case inl h7 =>
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
    case inr h9 =>
      -- Disjunctions on the left can always be decomposed.
      cases h9
      case inl h10 =>
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- One of the premise coincides with the conclusion.
        exact h10
      case inr h11 =>
        -- Conjunctions on the left can always be decomposed.
        let h12 := h11.left
        let h13 := h11.right
        -- Disjunctions on the left can always be decomposed.
        cases h12
        case inl h14 =>
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- True on the right can always be proven directly.
          apply True.intro
        case inr h15 =>
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- True on the right can always be proven directly.
          apply True.intro
  case inr h16 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_336230060219898487646675979939 : (p1 → (((((False ∧ (True ∨ p5)) → ((True ∨ (p4 ∧ (((p3 → p4) → p3) → p5))) ∨ (False → p3))) ∨ False) → ((p5 ∨ False) ∨ p3)) ∨ p1)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_958135434026222000367512470343 : ((((p1 → (True ∨ p1)) → (((p3 ∨ ((p5 → True) ∧ (p2 ∨ False))) ∧ False) ∧ (p1 ∧ (((p1 ∨ ((p2 ∨ p4) → p2)) ∧ False) ∧ p1)))) → False) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h1
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h2 : (p1 → (True ∨ p1)) := by
    -- Implications on the right can always be decomposed.
    intro h3
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h4 := h1 h2
  -- We need to get the left conjuct of h4 based on <expert-advice>.
  let h5 := h4.left
  -- We need to get the right conjuct of h5 based on <expert-advice>.
  let h6 := h5.right
  -- False on the left can always be used.
  apply False.elim h6
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_608225822387298159745682232965 : ((((((((((False ∨ (p3 ∧ False)) ∧ (p5 ∧ ((p4 ∧ ((False ∨ (p5 → False)) ∨ p3)) ∨ True))) ∨ p3) ∨ p3) ∧ p1) ∨ True) ∨ p3) ∨ p1) ∨ p1) ∧ True) := by
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
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_54836407397574707809378487510 : (((p3 → ((p3 ∨ (p4 ∨ True)) → (True ∧ p1))) → (((True ∧ ((p3 ∧ True) ∨ (p3 ∨ p3))) → False) ∨ ((True → p5) ∨ (False ∧ True)))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_158450929724914809309956302948 : (((p5 ∨ p2) ∨ ((p3 ∧ ((p4 ∧ (p4 ∨ p2)) → (p1 ∨ p5))) ∧ (p3 → (True ∨ (p2 → True))))) ∨ (p1 → (p1 ∨ ((True ∧ p4) ∧ False)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_701588833907852344555781308650 : (((((p2 → False) ∧ ((True ∧ p2) ∨ (p2 ∧ (p2 ∨ p2)))) ∧ (((((True ∨ p5) → p5) → (p5 ∧ (False ∧ (p4 ∧ p5)))) ∧ p1) → p3)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_234176980414813487842723983518 : ((True → (p5 → False)) → ((p1 ∧ ((False → p2) → p2)) → ((((True → False) → (p1 → (((p4 ∧ p1) ∨ p1) → p1))) → (p5 ∨ p2)) ∨ p5))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Conjunctions on the left can always be decomposed.
  let h3 := h2.left
  let h4 := h2.right
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h5
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- We want to use the implication h4 based on <expert-advice>. So we show its premise.
  have h6 : (False → p2) := by
    -- Implications on the right can always be decomposed.
    intro h7
    -- False on the left can always be used.
    apply False.elim h7
  -- We have shown the premise of h4, we can now drive its conclusion.
  let h8 := h4 h6
  -- One of the premise coincides with the conclusion.
  exact h8



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_134991205613577627826516252398 : ((((False → p4) → (p4 ∨ ((p2 → ((p2 ∧ p4) → ((p3 → ((p1 ∨ False) ∨ False)) → p1))) ∧ p1))) ∧ (True → p5)) ∨ (p5 ∨ (p2 → p2))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_238738729942742964227385217111 : ((p1 ∨ True) ∧ (((p4 ∨ ((p5 → (p5 → p4)) ∧ (p2 ∨ p1))) ∧ ((p5 ∧ p3) ∧ ((p5 ∨ (False → False)) ∨ True))) ∨ ((p5 ∨ p4) ∨ True))) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
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



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_41430428993803219722991509423 : (((((p3 ∧ (p2 → (p2 → ((p5 ∨ p2) ∧ ((p3 ∨ p5) → p1))))) → False) → (p2 ∧ ((p1 ∧ True) → (p5 ∧ (p3 ∧ False))))) ∨ p5) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_229611787510715372615326980673 : ((p3 → (p5 ∧ p1)) ∨ ((p2 → ((p3 → p3) ∧ (p4 → False))) → (p4 ∨ ((((p5 → False) ∧ p4) ∨ True) → (p1 → ((p1 ∨ p2) ∨ p5)))))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h2
  -- Implications on the right can always be decomposed.
  intro h3
  -- Disjunctions on the left can always be decomposed.
  cases h2
  case inl h4 =>
    -- Conjunctions on the left can always be decomposed.
    let h5 := h4.left
    let h6 := h4.right
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- One of the premise coincides with the conclusion.
    exact h3
  case inr h7 =>
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- One of the premise coincides with the conclusion.
    exact h3



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_779994375489667977331016525579 : (((p2 ∨ (((((p4 ∨ p4) ∨ (False ∨ (False ∧ (p5 ∨ (False ∧ ((True → True) → (True ∨ p4))))))) ∨ (p1 → True)) ∨ p3) ∨ (p5 ∨ p1))) ∨ False) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
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
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_65770857836650628771534318939 : ((p4 ∨ ((p3 ∧ ((p3 ∨ p3) → ((p3 ∧ p5) ∨ (((p3 → (p4 → p1)) ∨ True) ∧ p5)))) ∨ (p1 ∨ (((p4 ∧ p2) ∨ True) ∨ p1)))) ∨ p2) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
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
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_53281973798551229811707620831 : (((p4 ∧ ((((p4 ∨ p3) → p1) → (p2 ∨ p5)) ∧ (p5 → p4))) ∨ ((p5 ∧ (((p3 → (False ∧ False)) → p4) → (p4 ∧ p3))) ∨ True)) ∨ p5) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_98947799549219253238189594607 : ((True → (((p1 → (p1 ∧ True)) ∨ (p5 → ((p3 → False) ∧ (p4 ∧ ((((p5 ∧ p2) → p5) ∨ p4) ∧ p1))))) ∧ (False ∧ (False ∧ p3)))) → p1) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h2 : True := by
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



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_149566815643358938354584423211 : ((p2 ∧ (p1 ∧ (p5 ∨ (p5 ∧ (((False ∧ p2) ∨ ((((p1 ∧ p5) → True) ∧ p3) ∧ (True ∧ False))) ∧ False))))) ∨ ((p1 ∧ p4) → (p4 ∨ p2))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- One of the premise coincides with the conclusion.
  exact h3



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_306582695213911200015771802802 : (p1 ∨ ((p5 ∨ False) → ((((p5 ∨ ((p1 ∨ (p2 → (p5 ∧ p2))) ∨ p5)) ∧ (p2 ∨ ((True → (p3 ∧ p3)) ∧ p2))) ∨ (p3 → False)) ∨ True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
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
    -- False on the left can always be used.
    apply False.elim h3



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_187204938400460223413917865748 : (((p4 ∨ True) → ((p1 ∨ p4) ∨ (((p3 ∧ p4) → p3) ∧ p1))) → ((p1 ∨ (((p5 → (p1 → (True ∨ True))) → (p5 ∧ True)) ∨ p4)) ∨ True)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_31574590127135466311133927491 : ((False ∨ ((((p2 → p4) ∧ (((p5 ∧ p4) → ((p3 ∨ (p1 ∨ (p4 ∧ (False ∧ True)))) ∧ False)) ∨ p1)) → ((True → p5) ∨ True)) ∨ p1)) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
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
theorem thm_5_vars_44759653426935391548696963640 : (((((p1 ∧ (p3 ∨ True)) ∨ p4) → (((p2 → ((((p2 → p3) ∨ (p5 → (False ∨ (True ∨ p2)))) ∧ p1) → True)) ∧ p2) → p4)) → False) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_142812907991746739743211530195 : ((p3 ∨ ((p5 ∨ p3) ∨ (False ∨ ((((p4 → p5) ∨ (p3 → p1)) ∨ (p2 → (p3 ∨ ((p2 → True) ∨ p4)))) ∨ p3)))) → ((p4 ∨ True) ∨ p5)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h2 =>
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro
  case inr h3 =>
    -- Disjunctions on the left can always be decomposed.
    cases h3
    case inl h4 =>
      -- Disjunctions on the left can always be decomposed.
      cases h4
      case inl h5 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- One of the premise coincides with the conclusion.
        exact h5
      case inr h6 =>
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
        -- False on the left can always be used.
        apply False.elim h8
      case inr h9 =>
        -- Disjunctions on the left can always be decomposed.
        cases h9
        case inl h10 =>
          -- Disjunctions on the left can always be decomposed.
          cases h10
          case inl h11 =>
            -- Disjunctions on the left can always be decomposed.
            cases h11
            case inl h12 =>
              -- Show the left disjunct based on <expert-advice>.
              apply Or.inl
              -- Show the right disjunct based on <expert-advice>.
              apply Or.inr
              -- True on the right can always be proven directly.
              apply True.intro
            case inr h13 =>
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
        case inr h15 =>
          -- Show the left disjunct based on <expert-advice>.
          apply Or.inl
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- True on the right can always be proven directly.
          apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_759977735766368705475480906189 : (((p2 ∧ (((p2 ∧ (p5 → p5)) ∧ p2) ∨ (((((True → ((p4 ∧ ((p5 → p2) → (p3 ∨ p1))) ∨ p2)) → False) ∨ p3) ∨ p4) ∧ True))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_207262297949799138923732786787 : ((((p5 → (p5 ∧ p4)) ∨ p3) ∨ p2) → (((((p1 ∨ p2) ∧ (p3 → p5)) ∧ (p1 ∨ False)) → ((p2 → p3) ∨ (True ∧ p1))) ∧ (p2 → p2))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h2
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
    cases h4
    case inl h8 =>
      -- Disjunctions on the left can always be decomposed.
      cases h1
      case inl h9 =>
        -- Disjunctions on the left can always be decomposed.
        cases h9
        case inl h10 =>
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- Conjunctions on the right can always be decomposed.
          apply And.intro
          -- True on the right can always be proven directly.
          apply True.intro
          -- One of the premise coincides with the conclusion.
          exact h8
        case inr h11 =>
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- Conjunctions on the right can always be decomposed.
          apply And.intro
          -- True on the right can always be proven directly.
          apply True.intro
          -- One of the premise coincides with the conclusion.
          exact h8
      case inr h12 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- Conjunctions on the right can always be decomposed.
        apply And.intro
        -- True on the right can always be proven directly.
        apply True.intro
        -- One of the premise coincides with the conclusion.
        exact h8
    case inr h13 =>
      -- False on the left can always be used.
      apply False.elim h13
  case inr h14 =>
    -- Disjunctions on the left can always be decomposed.
    cases h4
    case inl h15 =>
      -- Disjunctions on the left can always be decomposed.
      cases h1
      case inl h16 =>
        -- Disjunctions on the left can always be decomposed.
        cases h16
        case inl h17 =>
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- Conjunctions on the right can always be decomposed.
          apply And.intro
          -- True on the right can always be proven directly.
          apply True.intro
          -- One of the premise coincides with the conclusion.
          exact h15
        case inr h18 =>
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- Conjunctions on the right can always be decomposed.
          apply And.intro
          -- True on the right can always be proven directly.
          apply True.intro
          -- One of the premise coincides with the conclusion.
          exact h15
      case inr h19 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- Conjunctions on the right can always be decomposed.
        apply And.intro
        -- True on the right can always be proven directly.
        apply True.intro
        -- One of the premise coincides with the conclusion.
        exact h15
    case inr h20 =>
      -- False on the left can always be used.
      apply False.elim h20
  -- Implications on the right can always be decomposed.
  intro h21
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h22 =>
    -- Disjunctions on the left can always be decomposed.
    cases h22
    case inl h23 =>
      -- One of the premise coincides with the conclusion.
      exact h21
    case inr h24 =>
      -- One of the premise coincides with the conclusion.
      exact h21
  case inr h25 =>
    -- One of the premise coincides with the conclusion.
    exact h25



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_68181792934153057621585785478 : ((p3 → (((p2 ∨ (((((False ∧ (p3 ∧ p1)) → p5) ∨ True) → p5) ∨ (((p3 → p3) ∧ False) ∨ (p1 → (p5 ∨ p4))))) → p2) ∨ p3)) ∨ p4) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_39206224473282747471148199124 : (((True ∧ ((((p3 ∧ (True → (p5 ∧ ((p2 → (((p5 ∨ False) → p1) ∧ False)) → (False ∧ True))))) → p2) ∨ False) ∧ (p3 ∧ p1))) ∧ p1) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_61026469873353761309807044428 : ((False ∧ ((((False ∧ (p5 ∨ p1)) ∧ ((((False ∧ p4) → p5) ∧ p4) → (p5 → ((p5 → p1) → True)))) ∧ (p3 → True)) ∧ (p4 ∨ p1))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_718749242237432575352348816021 : (((((p1 ∧ True) ∨ (p4 → p1)) ∨ (((((False → ((p2 → p2) ∨ p1)) → False) → p5) → p4) → ((p3 ∨ (p3 ∨ (False ∧ p3))) ∨ p1))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_690874718362430709201744777939 : ((((((p5 ∧ (((p4 → p3) ∧ (p5 ∨ (p5 ∧ p2))) ∨ p2)) ∨ p2) ∧ (p1 ∨ True)) → (((p2 → ((p5 ∧ p1) ∨ p4)) ∧ p2) ∨ True)) ∨ False) ∧ True) := by
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
    cases h6
    case inl h7 =>
      -- Conjunctions on the left can always be decomposed.
      let h8 := h7.left
      let h9 := h7.right
      -- Disjunctions on the left can always be decomposed.
      cases h9
      case inl h10 =>
        -- Disjunctions on the left can always be decomposed.
        cases h3
        case inl h11 =>
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- True on the right can always be proven directly.
          apply True.intro
        case inr h12 =>
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- True on the right can always be proven directly.
          apply True.intro
      case inr h13 =>
        -- Conjunctions on the left can always be decomposed.
        let h14 := h13.left
        let h15 := h13.right
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
    -- Disjunctions on the left can always be decomposed.
    cases h3
    case inl h22 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- True on the right can always be proven directly.
      apply True.intro
    case inr h23 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- True on the right can always be proven directly.
      apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_119047915926417021070083468898 : ((p1 → (((((((((p5 → (p5 ∨ p3)) → p4) ∧ (p4 ∨ p1)) ∨ p5) ∧ p1) ∨ p3) → p3) ∨ ((p4 ∨ p4) → p1)) ∨ True)) ∨ (p1 ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_137219996830839834075151790058 : ((p1 ∧ ((((p1 ∨ ((p4 ∧ (p5 ∨ (p2 → (p1 → p1)))) → ((p2 ∧ True) ∧ (p4 ∨ p4)))) ∧ p4) ∨ False) ∨ p1)) ∨ ((False → p3) ∨ p3)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_69182815039585206376192884010 : ((p5 → (((p2 → (((p5 → p4) ∨ ((p4 → (p2 ∧ p1)) ∨ False)) ∧ p4)) ∧ True) → (((p4 → ((p4 ∧ p5) → p4)) → p1) ∧ True))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_213459653048129818042407925384 : (((True → (p3 ∨ p5)) ∧ p3) ∨ ((((p3 → True) → p5) → (p3 ∨ ((((True ∨ p3) ∧ True) → (p4 ∨ False)) → (p2 ∨ p2)))) ∨ (False → True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_254333125596440333644149244600 : ((p2 ∧ p4) → ((False ∧ (((p4 ∨ (p1 ∨ p3)) → p2) ∧ ((True ∧ ((p2 ∧ (p4 ∧ False)) ∨ ((p5 → False) → (p2 ∧ p3)))) ∧ p1))) ∨ p2)) := by
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
theorem thm_5_vars_42507021346943008926187050367 : (((False ∨ (((p3 ∧ p1) ∨ (p4 ∨ (p5 → p3))) ∧ ((p3 ∨ p4) ∧ (True → ((False → p3) ∨ (((p4 ∧ p2) ∨ p3) → True)))))) ∨ True) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_136694738368330969872945958506 : (((False ∧ True) ∧ ((((((p2 ∧ ((p1 ∨ p1) ∨ (p3 ∨ False))) ∨ (p2 ∨ True)) ∧ (p4 → p2)) ∧ p3) ∨ True) ∨ p4)) ∨ (p1 → (p3 ∨ True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_616726023675488786817179204013 : ((((((((p5 ∧ True) ∧ p5) ∧ (p3 → p4)) ∧ (p2 ∨ p1)) ∨ (p3 ∧ (p2 ∧ (True → (((p2 → (p2 ∨ True)) ∨ p2) → p3))))) ∨ True) ∨ p2) ∧ True) := by
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
theorem thm_5_vars_149663970413032319005145014463 : ((p4 ∧ (False ∨ (p1 ∧ ((p5 → (True ∧ (p3 → ((False ∨ (p3 ∨ ((False → p5) → p4))) → p2)))) → p4)))) ∨ ((p4 ∨ (p5 → p1)) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_112051203023120062024202193713 : ((((p2 → (True → p1)) → ((p1 ∧ (((p5 ∧ p2) ∧ True) ∧ (p5 ∨ ((p4 → False) ∨ p5)))) ∧ (p1 ∨ (p3 ∧ True)))) ∨ False) ∨ (p1 → True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_308548446547633244638412561554 : (p2 ∨ (((True → ((((False ∧ p4) ∧ (p4 ∧ p2)) ∨ p1) ∧ p4)) → (p1 ∧ ((((((p4 ∧ p3) → True) ∨ p1) → p2) → p4) ∧ p1))) ∨ p5)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
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
  -- We need to get the left conjuct of h3 based on <expert-advice>.
  let h4 := h3.left
  -- Disjunctions on the left can always be decomposed.
  cases h4
  case inl h5 =>
    -- Conjunctions on the left can always be decomposed.
    let h6 := h5.left
    let h7 := h5.right
    -- Conjunctions on the left can always be decomposed.
    let h8 := h6.left
    let h9 := h6.right
    -- False on the left can always be used.
    apply False.elim h8
  case inr h10 =>
    -- One of the premise coincides with the conclusion.
    exact h10
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h11
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h12 : True := by
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h13 := h1 h12
  -- We need to get the right conjuct of h13 based on <expert-advice>.
  let h14 := h13.right
  -- One of the premise coincides with the conclusion.
  exact h14
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h15 : True := by
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h16 := h1 h15
  -- We need to get the left conjuct of h16 based on <expert-advice>.
  let h17 := h16.left
  -- Disjunctions on the left can always be decomposed.
  cases h17
  case inl h18 =>
    -- Conjunctions on the left can always be decomposed.
    let h19 := h18.left
    let h20 := h18.right
    -- Conjunctions on the left can always be decomposed.
    let h21 := h19.left
    let h22 := h19.right
    -- False on the left can always be used.
    apply False.elim h21
  case inr h23 =>
    -- One of the premise coincides with the conclusion.
    exact h23



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_142070590646492106994433287795 : ((True ∧ ((((p2 ∨ (p4 → p3)) ∨ (p3 ∧ ((p2 ∧ p4) ∧ True))) ∨ p1) ∨ ((p2 → ((False ∧ p3) ∨ True)) ∧ p4))) → ((False ∨ p3) ∨ True)) := by
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
      -- Disjunctions on the left can always be decomposed.
      cases h5
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
        -- Conjunctions on the left can always be decomposed.
        let h10 := h9.left
        let h11 := h9.right
        -- Conjunctions on the left can always be decomposed.
        let h12 := h11.left
        let h13 := h11.right
        -- Conjunctions on the left can always be decomposed.
        let h14 := h12.left
        let h15 := h12.right
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- True on the right can always be proven directly.
        apply True.intro
    case inr h16 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- True on the right can always be proven directly.
      apply True.intro
  case inr h17 =>
    -- Conjunctions on the left can always be decomposed.
    let h18 := h17.left
    let h19 := h17.right
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_661638731244799148586129480600 : ((((((True → ((p5 ∨ (False ∨ ((p3 → p2) → p2))) ∨ p5)) ∧ (p1 ∨ ((p2 → False) ∨ p5))) → ((p5 → p3) ∧ p3)) → (p1 ∧ p5)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_134826799900685334926995081549 : (((p1 ∨ (((p4 ∧ ((((True ∨ p5) ∨ p2) → p5) → p4)) ∨ p3) ∨ ((False ∧ True) → (p5 ∨ (p3 ∨ p1))))) → p4) ∨ ((True ∧ True) ∨ p5)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_615819316164602661752961257476 : (((((((p1 → p2) → ((p4 ∨ (p1 ∨ (p4 → p5))) ∨ (p3 ∨ p2))) → False) ∨ ((p4 ∧ False) ∨ (p1 ∧ ((p4 ∧ False) → p5)))) ∨ True) ∨ p2) ∧ True) := by
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
theorem thm_5_vars_196661198265351020848234106869 : (((((p2 → p3) ∨ (p2 ∧ p4)) ∧ p2) ∧ p2) ∨ (((True ∧ p3) ∨ (False ∧ ((p5 ∨ p5) ∧ (True → ((p3 → p3) → (False ∧ p1)))))) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_218597580382974181072132719402 : (((p3 → p4) → (p4 ∧ False)) → (((p1 ∨ p3) → p4) → ((((p3 ∨ p2) ∨ p1) ∧ ((p4 → (p3 ∧ p1)) → (False → p2))) → (False ∨ p5)))) := by
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
  cases h4
  case inl h6 =>
    -- Disjunctions on the left can always be decomposed.
    cases h6
    case inl h7 =>
      -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
      have h8 : (p3 → p4) := by
        -- Implications on the right can always be decomposed.
        intro h9
        -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
        have h10 : (p1 ∨ p3) := by
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- One of the premise coincides with the conclusion.
          exact h9
        -- We have shown the premise of h2, we can now drive its conclusion.
        let h11 := h2 h10
        -- One of the premise coincides with the conclusion.
        exact h11
      -- We have shown the premise of h1, we can now drive its conclusion.
      let h12 := h1 h8
      -- We need to get the right conjuct of h12 based on <expert-advice>.
      let h13 := h12.right
      -- False on the left can always be used.
      apply False.elim h13
    case inr h14 =>
      -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
      have h15 : (p3 → p4) := by
        -- Implications on the right can always be decomposed.
        intro h16
        -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
        have h17 : (p1 ∨ p3) := by
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- One of the premise coincides with the conclusion.
          exact h16
        -- We have shown the premise of h2, we can now drive its conclusion.
        let h18 := h2 h17
        -- One of the premise coincides with the conclusion.
        exact h18
      -- We have shown the premise of h1, we can now drive its conclusion.
      let h19 := h1 h15
      -- We need to get the right conjuct of h19 based on <expert-advice>.
      let h20 := h19.right
      -- False on the left can always be used.
      apply False.elim h20
  case inr h21 =>
    -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
    have h22 : (p3 → p4) := by
      -- Implications on the right can always be decomposed.
      intro h23
      -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
      have h24 : (p1 ∨ p3) := by
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- One of the premise coincides with the conclusion.
        exact h21
      -- We have shown the premise of h2, we can now drive its conclusion.
      let h25 := h2 h24
      -- One of the premise coincides with the conclusion.
      exact h25
    -- We have shown the premise of h1, we can now drive its conclusion.
    let h26 := h1 h22
    -- We need to get the right conjuct of h26 based on <expert-advice>.
    let h27 := h26.right
    -- False on the left can always be used.
    apply False.elim h27



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_64018344644991030001763669612 : ((False ∨ ((p2 ∧ ((((p5 ∧ (((True ∧ True) → False) ∧ True)) ∧ True) → ((p5 → p3) ∨ ((p1 → p3) ∨ p3))) → p1)) ∨ (True → True))) ∨ p4) := by
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
theorem thm_5_vars_66480289182233816291298053675 : ((True → ((((p4 → (p1 ∨ (p1 ∧ p5))) ∧ (((((((p5 ∧ p3) ∨ p4) → p5) ∧ (p2 ∨ p3)) ∨ True) → True) ∨ p4)) → p1) ∨ p3)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



