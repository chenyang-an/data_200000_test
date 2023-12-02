variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_116380543020097407311933520738 : ((((p3 → True) → p3) → ((((p3 → (True → (p2 → p1))) ∨ True) → (p4 → p5)) ∨ ((((p5 ∨ False) ∧ False) ∨ p3) ∨ p5))) ∨ (p1 ∨ p1)) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h2 : (p3 → True) := by
    -- Implications on the right can always be decomposed.
    intro h3
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h4 := h1 h2
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h4



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_123717820474541968763275228128 : ((((((p1 → (p3 ∨ (p2 → p4))) → (p2 → p4)) → False) ∧ (p5 ∨ p4)) ∧ ((p4 → p4) ∧ (((p3 → p2) ∨ p5) → False))) → (p4 ∧ p2)) := by
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
    -- Conjunctions on the left can always be decomposed.
    let h7 := h3.left
    let h8 := h3.right
    -- We want to use the implication h8 based on <expert-advice>. So we show its premise.
    have h9 : ((p3 → p2) ∨ p5) := by
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- One of the premise coincides with the conclusion.
      exact h6
    -- We have shown the premise of h8, we can now drive its conclusion.
    let h10 := h8 h9
    -- False on the left can always be used.
    apply False.elim h10
  case inr h11 =>
    -- Conjunctions on the left can always be decomposed.
    let h12 := h3.left
    let h13 := h3.right
    -- One of the premise coincides with the conclusion.
    exact h11
  -- Conjunctions on the left can always be decomposed.
  let h14 := h1.left
  let h15 := h1.right
  -- Conjunctions on the left can always be decomposed.
  let h16 := h14.left
  let h17 := h14.right
  -- Disjunctions on the left can always be decomposed.
  cases h17
  case inl h18 =>
    -- Conjunctions on the left can always be decomposed.
    let h19 := h15.left
    let h20 := h15.right
    -- We want to use the implication h20 based on <expert-advice>. So we show its premise.
    have h21 : ((p3 → p2) ∨ p5) := by
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- One of the premise coincides with the conclusion.
      exact h18
    -- We have shown the premise of h20, we can now drive its conclusion.
    let h22 := h20 h21
    -- False on the left can always be used.
    apply False.elim h22
  case inr h23 =>
    -- Conjunctions on the left can always be decomposed.
    let h24 := h15.left
    let h25 := h15.right
    -- We want to use the implication h16 based on <expert-advice>. So we show its premise.
    have h26 : ((p1 → (p3 ∨ (p2 → p4))) → (p2 → p4)) := by
      -- Implications on the right can always be decomposed.
      intro h27
      -- Implications on the right can always be decomposed.
      intro h28
      -- One of the premise coincides with the conclusion.
      exact h23
    -- We have shown the premise of h16, we can now drive its conclusion.
    let h29 := h16 h26
    -- False on the left can always be used.
    apply False.elim h29



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_633780136901304708896945565075 : (((((p1 → ((p3 ∨ p1) ∧ ((True ∨ (p5 ∨ ((p2 ∨ (((p3 → p5) ∨ p1) ∧ p3)) ∨ p4))) ∧ (p5 → p3)))) ∨ (p3 ∧ p2)) → p3) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_198744383610234418088832699937 : ((True → (((p1 ∨ p5) ∧ (p1 ∨ p2)) ∨ p2)) ∨ ((((((p1 → p1) → (p3 ∧ (((p5 ∨ False) ∨ p5) → p4))) ∨ p1) ∧ p4) ∨ False) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_646967160911094033561528501755 : ((((p3 → (((p5 ∧ p4) → (((p1 ∧ p2) ∧ ((p1 → (p2 ∧ True)) → ((True → ((p3 → p4) ∨ False)) ∨ False))) ∨ p5)) ∧ p5)) → p5) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_191844153968559223312086102490 : ((p3 ∨ ((True ∨ p3) → (((p5 ∨ True) → p3) ∧ False))) ∨ (p3 → ((((p3 → p2) ∧ (p5 → (p2 ∨ p5))) → p3) ∨ (p1 → (p4 ∨ p5))))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h2
  -- Conjunctions on the left can always be decomposed.
  let h3 := h2.left
  let h4 := h2.right
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_606790825786133829438686868759 : (((((((p3 ∧ False) ∨ (True ∧ (((((p5 ∧ p1) ∨ False) → (True → p3)) → ((p1 ∨ p3) ∨ False)) → p2))) → (p3 ∨ p5)) ∧ p1) ∨ True) ∨ p3) ∧ True) := by
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
theorem thm_5_vars_191068396212375116522882857629 : (((p4 ∨ (True → (p4 → True))) → (p5 → (p3 ∧ p2))) ∨ (p5 ∨ ((p2 ∨ ((p1 ∨ (False → p5)) ∨ p4)) ∨ (((p5 ∨ p5) → p3) → True)))) := by
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



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_118695574010339333752974156910 : ((p5 ∨ (((((p5 ∧ p4) ∨ p3) ∧ p1) ∧ (False ∨ (((p5 ∧ p3) → p2) ∨ ((False ∨ (p3 ∨ (p5 → False))) ∨ p5)))) ∨ True)) ∨ (p5 ∧ p2)) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_103264571584294813416474604385 : (((p5 ∧ (False ∧ (((p3 → p4) → (((((p2 ∧ p5) → p5) ∨ (p3 ∨ p5)) ∧ p2) ∨ True)) ∧ ((p5 ∨ p2) → p3)))) ∨ True) ∧ (p5 ∨ True)) := by
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
theorem thm_5_vars_115342182395837254504220853972 : (((True → ((((False → p4) ∨ p1) ∨ p4) ∨ (p3 ∧ True))) → (p3 ∧ (((False → True) → p2) → (p3 ∧ (p2 ∨ (True ∧ p3)))))) ∨ (True → True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_180050230711725879701827228950 : (((p2 ∨ ((p4 ∨ ((p5 → False) ∨ p1)) ∧ (True → (False ∧ p2)))) ∨ False) → (p2 ∧ (((p4 → ((p1 ∨ p4) ∧ (p2 ∧ True))) ∨ p5) ∨ p1))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h2 =>
    -- Disjunctions on the left can always be decomposed.
    cases h2
    case inl h3 =>
      -- One of the premise coincides with the conclusion.
      exact h3
    case inr h4 =>
      -- Conjunctions on the left can always be decomposed.
      let h5 := h4.left
      let h6 := h4.right
      -- Disjunctions on the left can always be decomposed.
      cases h5
      case inl h7 =>
        -- We want to use the implication h6 based on <expert-advice>. So we show its premise.
        have h8 : True := by
          -- True on the right can always be proven directly.
          apply True.intro
        -- We have shown the premise of h6, we can now drive its conclusion.
        let h9 := h6 h8
        -- We need to get the left conjuct of h9 based on <expert-advice>.
        let h10 := h9.left
        -- False on the left can always be used.
        apply False.elim h10
      case inr h11 =>
        -- Disjunctions on the left can always be decomposed.
        cases h11
        case inl h12 =>
          -- We want to use the implication h6 based on <expert-advice>. So we show its premise.
          have h13 : True := by
            -- True on the right can always be proven directly.
            apply True.intro
          -- We have shown the premise of h6, we can now drive its conclusion.
          let h14 := h6 h13
          -- We need to get the left conjuct of h14 based on <expert-advice>.
          let h15 := h14.left
          -- False on the left can always be used.
          apply False.elim h15
        case inr h16 =>
          -- We want to use the implication h6 based on <expert-advice>. So we show its premise.
          have h17 : True := by
            -- True on the right can always be proven directly.
            apply True.intro
          -- We have shown the premise of h6, we can now drive its conclusion.
          let h18 := h6 h17
          -- We need to get the left conjuct of h18 based on <expert-advice>.
          let h19 := h18.left
          -- False on the left can always be used.
          apply False.elim h19
  case inr h20 =>
    -- False on the left can always be used.
    apply False.elim h20
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h21 =>
    -- Disjunctions on the left can always be decomposed.
    cases h21
    case inl h22 =>
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- Implications on the right can always be decomposed.
      intro h23
      -- Conjunctions on the right can always be decomposed.
      apply And.intro
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- One of the premise coincides with the conclusion.
      exact h23
      -- Conjunctions on the right can always be decomposed.
      apply And.intro
      -- One of the premise coincides with the conclusion.
      exact h22
      -- True on the right can always be proven directly.
      apply True.intro
    case inr h24 =>
      -- Conjunctions on the left can always be decomposed.
      let h25 := h24.left
      let h26 := h24.right
      -- Disjunctions on the left can always be decomposed.
      cases h25
      case inl h27 =>
        -- We want to use the implication h26 based on <expert-advice>. So we show its premise.
        have h28 : True := by
          -- True on the right can always be proven directly.
          apply True.intro
        -- We have shown the premise of h26, we can now drive its conclusion.
        let h29 := h26 h28
        -- We need to get the left conjuct of h29 based on <expert-advice>.
        let h30 := h29.left
        -- False on the left can always be used.
        apply False.elim h30
      case inr h31 =>
        -- Disjunctions on the left can always be decomposed.
        cases h31
        case inl h32 =>
          -- We want to use the implication h26 based on <expert-advice>. So we show its premise.
          have h33 : True := by
            -- True on the right can always be proven directly.
            apply True.intro
          -- We have shown the premise of h26, we can now drive its conclusion.
          let h34 := h26 h33
          -- We need to get the left conjuct of h34 based on <expert-advice>.
          let h35 := h34.left
          -- False on the left can always be used.
          apply False.elim h35
        case inr h36 =>
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- One of the premise coincides with the conclusion.
          exact h36
  case inr h37 =>
    -- False on the left can always be used.
    apply False.elim h37



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_52355011052329082633735121307 : ((((((p5 → True) → ((p4 ∧ p1) → p1)) → (p2 → False)) ∧ (p5 ∧ p4)) ∧ (True → ((p5 → (((p1 → p3) ∧ True) → True)) → p3))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_318860013389546567243262459501 : (p4 ∨ (((((p2 ∧ p4) ∨ p2) ∧ (p3 ∨ (True → (p5 ∧ (p3 ∨ ((True ∧ (p3 → (False ∨ p3))) ∧ p5)))))) → p3) ∨ ((p2 → p2) ∨ p5))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_114599724261605490132428469208 : (((p2 ∧ ((p4 → (p1 → (((p3 ∨ p3) ∨ ((p4 ∧ p3) ∨ p2)) → True))) → p5)) ∧ (p4 → ((p2 → p4) ∨ (p3 → False)))) ∨ (p4 → p4)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_56246042520634804482447997422 : (((True → (p5 ∨ (p5 → p1))) ∨ (((p1 → (False ∨ (((p4 ∨ p4) ∨ False) ∨ True))) ∧ (p2 ∨ (((False ∧ True) ∧ p3) → p4))) ∧ True)) ∨ p3) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h2
  -- Conjunctions on the left can always be decomposed.
  let h3 := h2.left
  let h4 := h2.right
  -- Conjunctions on the left can always be decomposed.
  let h5 := h3.left
  let h6 := h3.right
  -- False on the left can always be used.
  apply False.elim h5
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_342438173199425675105278022163 : (p2 → ((True → ((p1 ∧ p3) ∨ ((p4 ∨ (True ∧ ((p4 ∧ False) ∧ (p5 → True)))) ∧ False))) → ((((p5 → False) ∨ (p3 ∨ False)) ∧ p1) ∧ True))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
  have h3 : True := by
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h2, we can now drive its conclusion.
  let h4 := h2 h3
  -- Disjunctions on the left can always be decomposed.
  cases h4
  case inl h5 =>
    -- Conjunctions on the left can always be decomposed.
    let h6 := h5.left
    let h7 := h5.right
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- One of the premise coincides with the conclusion.
    exact h7
  case inr h8 =>
    -- Conjunctions on the left can always be decomposed.
    let h9 := h8.left
    let h10 := h8.right
    -- Disjunctions on the left can always be decomposed.
    cases h9
    case inl h11 =>
      -- False on the left can always be used.
      apply False.elim h10
    case inr h12 =>
      -- Conjunctions on the left can always be decomposed.
      let h13 := h12.left
      let h14 := h12.right
      -- Conjunctions on the left can always be decomposed.
      let h15 := h14.left
      let h16 := h14.right
      -- Conjunctions on the left can always be decomposed.
      let h17 := h15.left
      let h18 := h15.right
      -- False on the left can always be used.
      apply False.elim h18
  -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
  have h19 : True := by
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h2, we can now drive its conclusion.
  let h20 := h2 h19
  -- Disjunctions on the left can always be decomposed.
  cases h20
  case inl h21 =>
    -- Conjunctions on the left can always be decomposed.
    let h22 := h21.left
    let h23 := h21.right
    -- One of the premise coincides with the conclusion.
    exact h22
  case inr h24 =>
    -- Conjunctions on the left can always be decomposed.
    let h25 := h24.left
    let h26 := h24.right
    -- Disjunctions on the left can always be decomposed.
    cases h25
    case inl h27 =>
      -- False on the left can always be used.
      apply False.elim h26
    case inr h28 =>
      -- Conjunctions on the left can always be decomposed.
      let h29 := h28.left
      let h30 := h28.right
      -- Conjunctions on the left can always be decomposed.
      let h31 := h30.left
      let h32 := h30.right
      -- Conjunctions on the left can always be decomposed.
      let h33 := h31.left
      let h34 := h31.right
      -- False on the left can always be used.
      apply False.elim h34
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_204903067663584082634268069290 : ((((False → p5) ∧ (p4 → True)) → p4) ∨ (((p3 ∧ p5) ∧ ((p4 ∧ p4) ∧ (p3 ∧ (False ∧ (False ∧ ((False ∧ p2) ∧ p4)))))) → (p5 ∧ p3))) := by
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
  let h6 := h3.left
  let h7 := h3.right
  -- Conjunctions on the left can always be decomposed.
  let h8 := h6.left
  let h9 := h6.right
  -- Conjunctions on the left can always be decomposed.
  let h10 := h7.left
  let h11 := h7.right
  -- Conjunctions on the left can always be decomposed.
  let h12 := h11.left
  let h13 := h11.right
  -- False on the left can always be used.
  apply False.elim h12
  -- Conjunctions on the left can always be decomposed.
  let h14 := h1.left
  let h15 := h1.right
  -- Conjunctions on the left can always be decomposed.
  let h16 := h14.left
  let h17 := h14.right
  -- Conjunctions on the left can always be decomposed.
  let h18 := h15.left
  let h19 := h15.right
  -- Conjunctions on the left can always be decomposed.
  let h20 := h18.left
  let h21 := h18.right
  -- Conjunctions on the left can always be decomposed.
  let h22 := h19.left
  let h23 := h19.right
  -- Conjunctions on the left can always be decomposed.
  let h24 := h23.left
  let h25 := h23.right
  -- False on the left can always be used.
  apply False.elim h24



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_208203710090761794129670175716 : (((False → (True ∧ p2)) → (False ∧ p3)) → ((p3 ∧ True) → ((True → ((((((True ∨ p5) ∧ True) ∧ p4) ∨ p4) ∨ (p1 ∧ False)) ∧ p5)) ∨ True))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Conjunctions on the left can always be decomposed.
  let h3 := h2.left
  let h4 := h2.right
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_157690844333545693826375096069 : (((p3 → ((p2 → (p5 ∧ (((True ∧ p5) → p5) ∨ (p4 → True)))) ∧ True)) ∨ ((p3 ∧ p3) ∨ p4)) ∨ (p3 ∨ ((False ∧ p5) ∨ (p4 → True)))) := by
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



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_134620892117128543217680267849 : (((((p3 ∨ (((p3 ∨ p4) ∧ (p4 ∨ p2)) ∧ ((p1 ∧ p1) ∨ p1))) ∨ (False → p2)) → (False ∧ (p1 ∨ True))) → p1) ∨ (p5 ∨ (True ∨ p1))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_168973903662583727481530945808 : ((False → ((p3 ∧ (p4 ∧ p5)) ∧ ((p3 ∨ ((p3 ∧ (p4 → p2)) ∨ True)) ∧ (p5 ∧ p4)))) → ((p3 ∨ (False ∧ (p3 ∨ (p2 → p1)))) → p3)) := by
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
    -- False on the left can always be used.
    apply False.elim h5



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_199302323208152466988355578849 : ((((((p5 ∧ True) → False) → p4) ∨ p3) ∨ p5) → (p1 ∨ ((p5 → p3) ∨ (((p1 → False) → True) → (p2 → (p5 ∨ (p2 ∨ (p2 ∧ p2)))))))) := by
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
      -- Implications on the right can always be decomposed.
      intro h4
      -- Implications on the right can always be decomposed.
      intro h5
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- One of the premise coincides with the conclusion.
      exact h5
    case inr h6 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- Implications on the right can always be decomposed.
      intro h7
      -- One of the premise coincides with the conclusion.
      exact h6
  case inr h8 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h9
    -- Implications on the right can always be decomposed.
    intro h10
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- One of the premise coincides with the conclusion.
    exact h8



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_303861610323869894630674602400 : (p1 ∨ (((((((((p5 ∨ p1) → (((p2 ∧ p1) ∧ True) → p1)) ∨ (p3 ∨ p5)) → p4) → p1) ∨ p2) ∧ False) ∨ (True ∨ (True ∧ p3))) ∨ p4)) := by
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
theorem thm_5_vars_69257889772286446960575662935 : ((p5 → ((p2 ∧ p1) ∧ (False ∨ (((p2 ∨ True) ∧ (p4 ∨ ((p3 → p1) ∧ False))) → ((((p3 ∨ (p5 → True)) ∨ True) ∧ p2) ∨ p3))))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_226651886356021713105859916219 : (((True ∧ p3) → p5) ∨ (p5 ∨ ((((p5 → (p2 → p4)) ∨ (p2 ∧ p4)) → (((p1 → ((p5 → p5) ∧ False)) ∧ True) ∨ p4)) ∨ (p1 → True)))) := by
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



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_671472526345792294041073229403 : ((((p2 → (False ∧ (((p1 ∨ p4) ∨ (p1 → p3)) ∨ (((p3 ∨ p1) → p5) ∨ ((True ∧ (False ∧ False)) ∧ p5))))) ∨ (p5 → (p4 ∨ p5))) ∨ p1) ∧ True) := by
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
theorem thm_5_vars_196647412916409182265175254239 : (((((p3 ∧ (p2 ∧ p4)) ∧ p4) ∧ p2) ∧ p1) ∨ ((((((False → p1) ∨ ((False ∧ (p4 ∧ p2)) ∧ False)) → (True ∨ True)) ∨ p2) → p5) → True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_58796540927420604759104926118 : (((p5 → False) ∧ ((p4 ∧ (p4 ∨ p1)) ∨ (((((True ∨ (False ∨ (p4 → True))) → True) ∧ True) → (True ∨ (p4 → p3))) ∧ (p5 → p4)))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_50451123459815038478887880900 : (((p2 ∨ (p3 → (p2 ∧ ((((p4 ∨ (True ∨ (p1 ∧ (p3 → p2)))) ∨ p3) → False) → (p3 ∧ p1))))) ∨ (False ∨ (p5 → (p4 → p4)))) ∨ p3) := by
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
  exact h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_67880387998635875328387831340 : ((p2 → ((p1 ∨ (((True → (p5 → p2)) ∧ ((p3 ∨ True) ∧ (((p5 → p4) ∨ p5) ∧ p4))) → p3)) ∧ ((p2 → (p2 ∧ p5)) ∨ p5))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_193294635116822299550946686834 : ((((False ∨ True) → False) ∨ (((p5 ∨ p4) ∧ p1) ∨ p1)) → ((p5 ∨ (p3 ∧ (p5 ∨ (False ∧ p5)))) ∨ (((p5 ∨ p4) ∨ (p1 ∧ True)) → p1))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h2 =>
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
  case inr h5 =>
    -- Disjunctions on the left can always be decomposed.
    cases h5
    case inl h6 =>
      -- Conjunctions on the left can always be decomposed.
      let h7 := h6.left
      let h8 := h6.right
      -- Disjunctions on the left can always be decomposed.
      cases h7
      case inl h9 =>
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- One of the premise coincides with the conclusion.
        exact h9
      case inr h10 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- Implications on the right can always be decomposed.
        intro h11
        -- Disjunctions on the left can always be decomposed.
        cases h11
        case inl h12 =>
          -- Disjunctions on the left can always be decomposed.
          cases h12
          case inl h13 =>
            -- One of the premise coincides with the conclusion.
            exact h8
          case inr h14 =>
            -- One of the premise coincides with the conclusion.
            exact h8
        case inr h15 =>
          -- Conjunctions on the left can always be decomposed.
          let h16 := h15.left
          let h17 := h15.right
          -- One of the premise coincides with the conclusion.
          exact h16
    case inr h18 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Implications on the right can always be decomposed.
      intro h19
      -- Disjunctions on the left can always be decomposed.
      cases h19
      case inl h20 =>
        -- Disjunctions on the left can always be decomposed.
        cases h20
        case inl h21 =>
          -- One of the premise coincides with the conclusion.
          exact h18
        case inr h22 =>
          -- One of the premise coincides with the conclusion.
          exact h18
      case inr h23 =>
        -- Conjunctions on the left can always be decomposed.
        let h24 := h23.left
        let h25 := h23.right
        -- One of the premise coincides with the conclusion.
        exact h24



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_307866321294259609404331009388 : (p1 ∨ (p5 → (((p1 ∨ (p3 ∧ (p3 ∨ ((((p2 → (p1 ∧ (p5 ∨ p3))) ∨ p1) ∧ p2) → p1)))) ∧ p5) ∨ (((p5 ∧ p3) → p3) ∨ p4)))) := by
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
  -- Conjunctions on the left can always be decomposed.
  let h3 := h2.left
  let h4 := h2.right
  -- One of the premise coincides with the conclusion.
  exact h4



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_198004375554965935003825177807 : (((False → p4) ∧ (((p4 ∨ p3) → p2) ∧ p2)) ∨ (((True → ((((p1 ∧ True) ∨ p3) ∨ (p5 ∧ p5)) ∨ p1)) ∨ (p5 ∧ True)) ∨ (p3 → True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_247421271101565036453934657397 : ((False ∨ p2) ∨ (((p5 ∧ p1) → ((((p5 → p5) ∨ p2) → (p4 ∧ (False ∨ (False → p4)))) → ((False ∧ (p2 ∨ False)) → p3))) → (p3 → p3))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- One of the premise coincides with the conclusion.
  exact h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_594965034500841245500172942098 : ((((((((((p1 ∧ True) ∨ True) ∧ False) ∧ (p3 ∧ (p2 → p2))) ∨ p3) ∨ p1) ∨ ((p2 → (p1 → ((p3 ∨ p1) ∧ p4))) ∨ True)) ∧ p2) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_67546618366642532109421808129 : ((p1 → ((False ∧ (p5 → False)) ∨ ((((((p1 ∨ (p3 → (((True → p4) ∨ p3) → p5))) ∨ p2) ∨ p4) ∨ True) → (p5 ∧ True)) ∨ p1))) ∨ p1) := by
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
theorem thm_5_vars_45410683258358994462237646519 : (((p5 ∧ ((p4 ∨ p3) → (((p4 ∨ (p4 → ((p3 ∧ ((((p4 ∧ p5) ∧ p3) → p3) ∨ p2)) → p3))) ∧ (False → p3)) → p5))) → p4) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_773968069296315843096730763992 : (((False ∨ ((((p3 → True) ∧ (((((p3 ∨ True) → p3) ∧ (p2 → (p5 ∨ p1))) ∨ (p3 → (p2 ∨ False))) → p1)) ∨ p2) ∧ (p2 ∧ p5))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_184569665528479111504160684274 : ((((p3 ∨ p3) ∧ (True ∧ ((p4 → p1) → True))) → (p1 → False)) ∨ ((True → p3) ∨ (p2 → ((p2 → (p2 → p2)) ∨ ((p1 ∧ p1) ∨ False))))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h2
  -- Implications on the right can always be decomposed.
  intro h3
  -- One of the premise coincides with the conclusion.
  exact h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_165568475458986428773234658561 : ((((p1 ∨ ((p3 → p3) ∧ (p1 ∧ p4))) ∨ p3) ∨ (p3 ∧ (p2 ∧ ((p1 ∧ False) ∧ False)))) ∨ (True → ((p3 ∧ ((p4 ∨ p5) ∧ True)) → p3))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Conjunctions on the left can always be decomposed.
  let h3 := h2.left
  let h4 := h2.right
  -- Conjunctions on the left can always be decomposed.
  let h5 := h4.left
  let h6 := h4.right
  -- Disjunctions on the left can always be decomposed.
  cases h5
  case inl h7 =>
    -- One of the premise coincides with the conclusion.
    exact h3
  case inr h8 =>
    -- One of the premise coincides with the conclusion.
    exact h3



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_156629121470737872794482899898 : (((((p4 ∨ (p5 ∨ ((p2 ∨ True) ∧ True))) ∧ (p5 → (p2 ∧ ((p2 ∨ False) ∧ p5)))) ∨ p4) ∧ True) ∨ (False → (p5 → ((p2 ∧ True) → True)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Implications on the right can always be decomposed.
  intro h3
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_206393722327583614332355312298 : ((p3 ∨ ((p4 → (p2 ∧ p3)) ∨ p3)) ∨ (((p1 ∧ p5) → (p5 ∧ (((False ∨ ((False ∨ True) → False)) ∧ ((p5 ∧ p1) → p5)) ∨ p4))) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_225890434464057021303984426900 : (((p1 ∧ p1) ∨ p2) ∨ (p5 → ((p4 ∨ p1) → (p1 → ((p4 → ((((p2 ∧ True) ∨ False) ∨ ((p5 ∧ p3) → (False → False))) ∨ True)) ∨ False))))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Implications on the right can always be decomposed.
  intro h3
  -- Disjunctions on the left can always be decomposed.
  cases h2
  case inl h4 =>
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Implications on the right can always be decomposed.
    intro h5
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro
  case inr h6 =>
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Implications on the right can always be decomposed.
    intro h7
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_134762210488942421459747934169 : ((((p3 ∨ p2) → ((p4 ∨ p5) ∨ (((False → p2) ∨ (((p4 → (p3 ∨ (p5 ∨ p1))) ∧ p4) → False)) ∨ p1))) → p4) ∨ (True ∨ (p1 ∨ p5))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_35128269078720240181121986035 : ((p1 → (((False ∨ ((p5 ∧ (p4 ∧ p5)) ∧ p1)) ∨ (p2 → (False ∧ False))) ∨ (p2 ∨ ((True ∧ (p1 ∨ (p1 ∧ (p2 ∧ p4)))) → True)))) ∧ True) := by
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
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_161431897935675105681377452022 : ((p2 ∧ (((p5 → ((p2 ∨ p3) ∨ p3)) → p4) ∧ (((True → (p5 → p2)) ∧ (p4 → p3)) ∨ p5))) → ((False ∨ p4) ∧ (p4 ∧ (True → p4)))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
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
    -- We want to use the implication h4 based on <expert-advice>. So we show its premise.
    have h9 : (p5 → ((p2 ∨ p3) ∨ p3)) := by
      -- Implications on the right can always be decomposed.
      intro h10
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- One of the premise coincides with the conclusion.
      exact h2
    -- We have shown the premise of h4, we can now drive its conclusion.
    let h11 := h4 h9
    -- One of the premise coincides with the conclusion.
    exact h11
  case inr h12 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- We want to use the implication h4 based on <expert-advice>. So we show its premise.
    have h13 : (p5 → ((p2 ∨ p3) ∨ p3)) := by
      -- Implications on the right can always be decomposed.
      intro h14
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- One of the premise coincides with the conclusion.
      exact h2
    -- We have shown the premise of h4, we can now drive its conclusion.
    let h15 := h4 h13
    -- One of the premise coincides with the conclusion.
    exact h15
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Conjunctions on the left can always be decomposed.
  let h16 := h1.left
  let h17 := h1.right
  -- Conjunctions on the left can always be decomposed.
  let h18 := h17.left
  let h19 := h17.right
  -- Disjunctions on the left can always be decomposed.
  cases h19
  case inl h20 =>
    -- Conjunctions on the left can always be decomposed.
    let h21 := h20.left
    let h22 := h20.right
    -- We want to use the implication h18 based on <expert-advice>. So we show its premise.
    have h23 : (p5 → ((p2 ∨ p3) ∨ p3)) := by
      -- Implications on the right can always be decomposed.
      intro h24
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- One of the premise coincides with the conclusion.
      exact h16
    -- We have shown the premise of h18, we can now drive its conclusion.
    let h25 := h18 h23
    -- One of the premise coincides with the conclusion.
    exact h25
  case inr h26 =>
    -- We want to use the implication h18 based on <expert-advice>. So we show its premise.
    have h27 : (p5 → ((p2 ∨ p3) ∨ p3)) := by
      -- Implications on the right can always be decomposed.
      intro h28
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- One of the premise coincides with the conclusion.
      exact h16
    -- We have shown the premise of h18, we can now drive its conclusion.
    let h29 := h18 h27
    -- One of the premise coincides with the conclusion.
    exact h29
  -- Implications on the right can always be decomposed.
  intro h30
  -- Conjunctions on the left can always be decomposed.
  let h31 := h1.left
  let h32 := h1.right
  -- Conjunctions on the left can always be decomposed.
  let h33 := h32.left
  let h34 := h32.right
  -- Disjunctions on the left can always be decomposed.
  cases h34
  case inl h35 =>
    -- Conjunctions on the left can always be decomposed.
    let h36 := h35.left
    let h37 := h35.right
    -- We want to use the implication h33 based on <expert-advice>. So we show its premise.
    have h38 : (p5 → ((p2 ∨ p3) ∨ p3)) := by
      -- Implications on the right can always be decomposed.
      intro h39
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- One of the premise coincides with the conclusion.
      exact h31
    -- We have shown the premise of h33, we can now drive its conclusion.
    let h40 := h33 h38
    -- One of the premise coincides with the conclusion.
    exact h40
  case inr h41 =>
    -- We want to use the implication h33 based on <expert-advice>. So we show its premise.
    have h42 : (p5 → ((p2 ∨ p3) ∨ p3)) := by
      -- Implications on the right can always be decomposed.
      intro h43
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- One of the premise coincides with the conclusion.
      exact h31
    -- We have shown the premise of h33, we can now drive its conclusion.
    let h44 := h33 h42
    -- One of the premise coincides with the conclusion.
    exact h44



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_728117421634558549054977713498 : ((((p5 ∨ (p1 ∧ p4)) ∨ ((((p3 ∧ (p5 → (p2 ∨ False))) ∧ ((False ∨ p4) ∨ False)) → ((((p2 ∧ True) ∧ p1) ∧ p1) ∨ p4)) ∨ p1)) ∨ p4) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
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
  -- Disjunctions on the left can always be decomposed.
  cases h3
  case inl h6 =>
    -- Disjunctions on the left can always be decomposed.
    cases h6
    case inl h7 =>
      -- False on the left can always be used.
      apply False.elim h7
    case inr h8 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- One of the premise coincides with the conclusion.
      exact h8
  case inr h9 =>
    -- False on the left can always be used.
    apply False.elim h9
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_56239647089516494094076857469 : (((p5 ∨ (p4 ∨ (p2 → p4))) ∨ ((((False → p4) ∧ True) ∧ (p4 ∧ True)) ∨ (p1 ∨ ((p2 ∨ True) ∨ ((p1 ∧ p5) ∧ (p1 ∨ True)))))) ∨ p1) := by
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
theorem thm_5_vars_112820215191981502539352441290 : ((((p1 ∧ (p2 ∧ (p4 → p3))) ∧ (((((p3 ∨ (False ∧ False)) ∨ p1) → ((p4 ∧ p2) → True)) ∧ (p3 ∧ p2)) ∨ p2)) → p5) ∨ (p2 → True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_691319652379351819917736205122 : (((((False → (p2 → p2)) ∧ (p2 ∨ ((p5 ∨ (p4 ∨ False)) ∧ ((p1 ∧ p5) → True)))) → ((((True ∨ (p3 ∨ True)) ∨ p4) ∨ p2) → p1)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_131300484464288791118105466854 : (((((p2 → False) ∨ (True ∧ False)) ∧ p2) → (p5 ∨ (((p4 ∨ p3) ∨ (p3 ∧ (p5 ∨ (p1 → (True ∧ False))))) ∨ p5))) ∧ ((p5 → p5) ∨ p4)) := by
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
    -- We want to use the implication h4 based on <expert-advice>. So we show its premise.
    have h5 : p2 := by
      -- One of the premise coincides with the conclusion.
      exact h3
    -- We have shown the premise of h4, we can now drive its conclusion.
    let h6 := h4 h5
    -- False on the left can always be used.
    apply False.elim h6
  case inr h7 =>
    -- Conjunctions on the left can always be decomposed.
    let h8 := h7.left
    let h9 := h7.right
    -- False on the left can always be used.
    apply False.elim h9
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h10
  -- One of the premise coincides with the conclusion.
  exact h10



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_68868818585718737951315784659 : ((p4 → (True ∧ (p1 ∨ ((p1 ∨ (p3 ∨ (((True → p2) → (p5 ∨ True)) → p5))) ∧ (((True → (False → (p1 → True))) ∨ p4) ∧ False))))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_151844445487910257692214186043 : (((((p2 → ((p1 ∨ ((p3 ∧ (p5 ∨ True)) → p5)) ∧ True)) ∧ True) → p5) ∨ (p1 → ((p3 → False) ∨ p2))) → ((True → False) ∨ (p4 → True))) := by
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
theorem thm_5_vars_38674446628522331590198201239 : ((((((p5 → p1) → False) ∨ (False ∨ p3)) ∧ (((p3 ∨ p1) → (p4 ∨ ((p4 ∨ (p1 → p1)) → False))) ∧ (p3 ∧ (p5 ∨ False)))) ∧ p2) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_801194566031914775118608051058 : (((p2 → (((((True ∧ (p1 ∧ (False ∧ (p1 ∨ p5)))) ∨ True) ∨ (True ∧ (p3 ∧ False))) ∧ p3) ∧ (p3 ∧ (((False → p4) → p4) ∨ False)))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_180011323113443049298817289605 : ((((p3 → False) ∨ ((True ∧ (p3 → p1)) → (p4 ∨ (True → p1)))) ∨ p3) → (((p5 → (p3 ∧ (p2 → (p4 ∧ p3)))) ∧ False) ∨ (True ∨ p5))) := by
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
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- True on the right can always be proven directly.
      apply True.intro
  case inr h5 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- True on the right can always be proven directly.
    apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_206371914069153026348110433132 : ((p2 ∨ (p2 ∨ ((p1 ∧ p5) ∨ p1))) ∨ (p5 ∨ (p4 → (True ∨ ((p3 ∨ False) → (p1 ∧ ((True ∧ (p2 ∧ (False → p5))) ∨ (p2 → p4)))))))) := by
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
theorem thm_5_vars_117790230830196067394791814113 : ((p4 ∧ ((p4 ∧ ((p2 → p3) ∨ (p1 → (((p5 ∧ p1) ∧ p1) → False)))) ∨ ((p3 → p1) ∨ ((p5 → (p2 ∨ True)) → True)))) ∨ (True ∧ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_112037503680206089261005835971 : ((((p5 ∨ (p2 ∨ p2)) ∨ ((True → p1) ∨ ((p1 ∨ ((True ∧ False) ∧ ((p3 ∨ (p1 ∨ (True → True))) ∨ p3))) ∧ False))) ∨ True) ∨ (p3 → p4)) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_328300466362218533911276966256 : (True → (((p3 ∨ p1) ∨ (((p4 → p1) ∨ (p1 ∨ ((p3 → p4) → False))) ∧ ((p2 ∧ (True ∧ p5)) → p4))) ∨ ((True ∧ (p5 ∨ True)) ∨ True))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_729214753038806932535602191815 : (((((p4 → True) ∧ p1) → (p5 → ((True → (p3 ∧ ((p3 ∨ p3) ∨ p1))) ∧ (((p5 ∧ (p5 → p2)) ∧ (True ∧ p3)) → (p3 ∨ p4))))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_179942630969941582427273567896 : (((((((p4 ∧ p1) ∨ p5) ∧ True) ∨ (True ∧ False)) ∧ (True ∧ p2)) ∨ True) → (((p3 ∨ (((p3 → p3) → (p3 → p5)) ∨ True)) ∨ p1) ∨ False)) := by
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
      -- Conjunctions on the left can always be decomposed.
      let h6 := h5.left
      let h7 := h5.right
      -- Disjunctions on the left can always be decomposed.
      cases h6
      case inl h8 =>
        -- Conjunctions on the left can always be decomposed.
        let h9 := h8.left
        let h10 := h8.right
        -- Conjunctions on the left can always be decomposed.
        let h11 := h4.left
        let h12 := h4.right
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- One of the premise coincides with the conclusion.
        exact h10
      case inr h13 =>
        -- Conjunctions on the left can always be decomposed.
        let h14 := h4.left
        let h15 := h4.right
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- True on the right can always be proven directly.
        apply True.intro
    case inr h16 =>
      -- Conjunctions on the left can always be decomposed.
      let h17 := h16.left
      let h18 := h16.right
      -- False on the left can always be used.
      apply False.elim h18
  case inr h19 =>
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_62267378221961085805996646121 : ((p3 ∧ ((((((p5 ∨ (p4 ∨ p3)) → p5) ∨ (p2 ∨ (p3 ∨ ((p2 ∧ p3) ∧ ((False ∨ p5) ∨ (p4 → p3)))))) → p3) → p2) → p1)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_256788129058975466510717240616 : ((p1 ∨ p2) → ((p1 ∧ ((p5 ∨ p4) ∨ p3)) ∨ (False → ((p3 ∨ p5) → (p4 ∧ (True → (p5 ∨ (p5 → (p5 ∧ ((p1 ∨ p4) ∧ p2)))))))))) := by
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
    -- Conjunctions on the right can always be decomposed.
    apply And.intro
    -- Disjunctions on the left can always be decomposed.
    cases h4
    case inl h5 =>
      -- False on the left can always be used.
      apply False.elim h3
    case inr h6 =>
      -- False on the left can always be used.
      apply False.elim h3
    -- Implications on the right can always be decomposed.
    intro h7
    -- Disjunctions on the left can always be decomposed.
    cases h4
    case inl h8 =>
      -- False on the left can always be used.
      apply False.elim h3
    case inr h9 =>
      -- False on the left can always be used.
      apply False.elim h3
  case inr h10 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h11
    -- Implications on the right can always be decomposed.
    intro h12
    -- Conjunctions on the right can always be decomposed.
    apply And.intro
    -- Disjunctions on the left can always be decomposed.
    cases h12
    case inl h13 =>
      -- False on the left can always be used.
      apply False.elim h11
    case inr h14 =>
      -- False on the left can always be used.
      apply False.elim h11
    -- Implications on the right can always be decomposed.
    intro h15
    -- Disjunctions on the left can always be decomposed.
    cases h12
    case inl h16 =>
      -- False on the left can always be used.
      apply False.elim h11
    case inr h17 =>
      -- False on the left can always be used.
      apply False.elim h11



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_232834922157824098905666374668 : ((p2 ∧ (p4 ∨ p2)) → (True → ((p2 → False) → ((p2 ∧ ((True ∧ (p4 ∧ ((((p5 ∨ p4) ∧ p3) ∧ p3) → (p4 ∧ p2)))) ∧ False)) ∧ p5)))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Implications on the right can always be decomposed.
  intro h3
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Conjunctions on the left can always be decomposed.
  let h4 := h1.left
  let h5 := h1.right
  -- Disjunctions on the left can always be decomposed.
  cases h5
  case inl h6 =>
    -- One of the premise coincides with the conclusion.
    exact h4
  case inr h7 =>
    -- One of the premise coincides with the conclusion.
    exact h7
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Conjunctions on the left can always be decomposed.
  let h8 := h1.left
  let h9 := h1.right
  -- Disjunctions on the left can always be decomposed.
  cases h9
  case inl h10 =>
    -- One of the premise coincides with the conclusion.
    exact h10
  case inr h11 =>
    -- We want to use the implication h3 based on <expert-advice>. So we show its premise.
    have h12 : p2 := by
      -- One of the premise coincides with the conclusion.
      exact h11
    -- We have shown the premise of h3, we can now drive its conclusion.
    let h13 := h3 h12
    -- False on the left can always be used.
    apply False.elim h13
  -- Implications on the right can always be decomposed.
  intro h14
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Conjunctions on the left can always be decomposed.
  let h15 := h14.left
  let h16 := h14.right
  -- Conjunctions on the left can always be decomposed.
  let h17 := h15.left
  let h18 := h15.right
  -- Disjunctions on the left can always be decomposed.
  cases h17
  case inl h19 =>
    -- Conjunctions on the left can always be decomposed.
    let h20 := h1.left
    let h21 := h1.right
    -- Disjunctions on the left can always be decomposed.
    cases h21
    case inl h22 =>
      -- One of the premise coincides with the conclusion.
      exact h22
    case inr h23 =>
      -- We want to use the implication h3 based on <expert-advice>. So we show its premise.
      have h24 : p2 := by
        -- One of the premise coincides with the conclusion.
        exact h23
      -- We have shown the premise of h3, we can now drive its conclusion.
      let h25 := h3 h24
      -- False on the left can always be used.
      apply False.elim h25
  case inr h26 =>
    -- Conjunctions on the left can always be decomposed.
    let h27 := h1.left
    let h28 := h1.right
    -- Disjunctions on the left can always be decomposed.
    cases h28
    case inl h29 =>
      -- One of the premise coincides with the conclusion.
      exact h29
    case inr h30 =>
      -- One of the premise coincides with the conclusion.
      exact h26
  -- Conjunctions on the left can always be decomposed.
  let h31 := h14.left
  let h32 := h14.right
  -- Conjunctions on the left can always be decomposed.
  let h33 := h31.left
  let h34 := h31.right
  -- Disjunctions on the left can always be decomposed.
  cases h33
  case inl h35 =>
    -- Conjunctions on the left can always be decomposed.
    let h36 := h1.left
    let h37 := h1.right
    -- Disjunctions on the left can always be decomposed.
    cases h37
    case inl h38 =>
      -- One of the premise coincides with the conclusion.
      exact h36
    case inr h39 =>
      -- One of the premise coincides with the conclusion.
      exact h39
  case inr h40 =>
    -- Conjunctions on the left can always be decomposed.
    let h41 := h1.left
    let h42 := h1.right
    -- Disjunctions on the left can always be decomposed.
    cases h42
    case inl h43 =>
      -- One of the premise coincides with the conclusion.
      exact h41
    case inr h44 =>
      -- One of the premise coincides with the conclusion.
      exact h44
  -- Conjunctions on the left can always be decomposed.
  let h45 := h1.left
  let h46 := h1.right
  -- Disjunctions on the left can always be decomposed.
  cases h46
  case inl h47 =>
    -- We want to use the implication h3 based on <expert-advice>. So we show its premise.
    have h48 : p2 := by
      -- One of the premise coincides with the conclusion.
      exact h45
    -- We have shown the premise of h3, we can now drive its conclusion.
    let h49 := h3 h48
    -- False on the left can always be used.
    apply False.elim h49
  case inr h50 =>
    -- We want to use the implication h3 based on <expert-advice>. So we show its premise.
    have h51 : p2 := by
      -- One of the premise coincides with the conclusion.
      exact h50
    -- We have shown the premise of h3, we can now drive its conclusion.
    let h52 := h3 h51
    -- False on the left can always be used.
    apply False.elim h52
  -- Conjunctions on the left can always be decomposed.
  let h53 := h1.left
  let h54 := h1.right
  -- Disjunctions on the left can always be decomposed.
  cases h54
  case inl h55 =>
    -- We want to use the implication h3 based on <expert-advice>. So we show its premise.
    have h56 : p2 := by
      -- One of the premise coincides with the conclusion.
      exact h53
    -- We have shown the premise of h3, we can now drive its conclusion.
    let h57 := h3 h56
    -- False on the left can always be used.
    apply False.elim h57
  case inr h58 =>
    -- We want to use the implication h3 based on <expert-advice>. So we show its premise.
    have h59 : p2 := by
      -- One of the premise coincides with the conclusion.
      exact h58
    -- We have shown the premise of h3, we can now drive its conclusion.
    let h60 := h3 h59
    -- False on the left can always be used.
    apply False.elim h60



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_44296814681534371797843367359 : (((((True ∧ True) → (((p1 → (True → (p1 → (False ∧ (False ∧ p4))))) ∨ p1) ∧ False)) ∧ ((False ∧ (p3 ∧ (p3 ∧ False))) → p3)) → False) ∨ False) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
  have h4 : (True ∧ True) := by
    -- Conjunctions on the right can always be decomposed.
    apply And.intro
    -- True on the right can always be proven directly.
    apply True.intro
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h2, we can now drive its conclusion.
  let h5 := h2 h4
  -- We need to get the right conjuct of h5 based on <expert-advice>.
  let h6 := h5.right
  -- False on the left can always be used.
  apply False.elim h6



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_673853835097614663296884535505 : (((((True ∧ p1) → (p1 ∧ (((((True ∧ p5) ∧ (p3 ∨ p2)) ∧ False) ∨ (p2 ∨ (p5 → p4))) → (p4 ∧ p1)))) → ((p3 ∨ p3) → p1)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_60656475268986307782873558709 : ((True ∧ ((((True ∨ (True → p2)) ∨ ((False → p1) ∧ p1)) → ((p1 ∧ (p1 ∨ (p1 ∧ True))) ∧ p1)) ∨ (((p3 ∧ False) ∧ p2) → p5))) ∨ False) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
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
  let h4 := h2.left
  let h5 := h2.right
  -- False on the left can always be used.
  apply False.elim h5



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_179761157326793774127760605944 : ((((((False → p3) ∧ (p2 → False)) → True) ∨ (True ∧ (True ∧ p4))) ∧ True) → ((((p1 ∧ (p3 ∨ False)) ∨ p4) ∧ p3) ∨ ((True ∧ False) → p2))) := by
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
    -- Implications on the right can always be decomposed.
    intro h5
    -- Conjunctions on the left can always be decomposed.
    let h6 := h5.left
    let h7 := h5.right
    -- False on the left can always be used.
    apply False.elim h7
  case inr h8 =>
    -- Conjunctions on the left can always be decomposed.
    let h9 := h8.left
    let h10 := h8.right
    -- Conjunctions on the left can always be decomposed.
    let h11 := h10.left
    let h12 := h10.right
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h13
    -- Conjunctions on the left can always be decomposed.
    let h14 := h13.left
    let h15 := h13.right
    -- False on the left can always be used.
    apply False.elim h15



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_191449746698322523450808494685 : (((p1 → p1) → (True → ((p4 ∨ (p4 → p1)) ∨ p3))) ∨ (True ∨ (((True → (((p2 → (p1 ∧ p2)) ∨ p2) ∧ p4)) → (False → True)) ∧ False))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_119425929560834527521083625107 : ((p4 → ((p5 ∨ (p1 ∨ (p1 ∨ (((p2 ∨ (p5 ∧ ((p3 ∨ p1) ∧ (True ∨ (p3 ∨ p5))))) ∧ p3) ∨ p5)))) ∨ (False → False))) ∨ (p5 ∧ p3)) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h2
  -- False on the left can always be used.
  apply False.elim h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_349697341148716516681920916923 : (p4 → ((((p5 ∨ ((p1 → ((((p5 → True) ∨ p4) → (p2 ∧ p5)) ∧ False)) → False)) → p1) ∨ ((p2 → ((p3 ∧ p1) → True)) ∧ True)) ∧ p4)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h2
  -- Implications on the right can always be decomposed.
  intro h3
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_134389710478288628195083947950 : (((p5 ∨ ((p2 ∧ (p5 ∧ p1)) ∨ (True → ((((p1 → p4) ∧ (p4 → False)) → p5) → ((False ∨ p1) ∧ p5))))) ∨ True) ∨ (p5 ∨ (True → p1))) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_65447724395802752043325053704 : ((p3 ∨ ((p4 ∨ p2) ∨ ((p1 ∨ (p5 ∨ p4)) → ((p3 ∨ (p5 ∨ (((False ∨ p2) ∨ True) → True))) ∨ (p1 → (True → (p3 ∧ False))))))) ∨ p4) := by
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
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h3
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
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- One of the premise coincides with the conclusion.
      exact h5
    case inr h6 =>
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Implications on the right can always be decomposed.
      intro h7
      -- True on the right can always be proven directly.
      apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_345480187833446048559574840673 : (p3 → (((p5 ∧ ((p4 → ((p2 ∨ (((True → p4) ∧ p3) ∧ p4)) → (p4 ∨ False))) ∨ ((p3 → p4) ∨ p3))) → (p1 → (p2 → p4))) ∨ True)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_204453272981309633399613443082 : ((((p1 ∧ (False → p5)) ∧ p2) ∨ p5) ∨ ((True ∨ p3) → ((((p3 ∧ p3) ∨ ((p2 → (p5 ∧ p2)) ∧ p3)) → p2) ∨ (True ∨ (p3 ∧ False))))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h2 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- True on the right can always be proven directly.
    apply True.intro
  case inr h3 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- True on the right can always be proven directly.
    apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_785946388826198163973041530009 : (((p4 ∨ ((((((p4 ∨ ((p1 ∧ (p1 ∨ (p1 → p3))) ∨ (p3 → True))) ∧ p4) ∧ p4) → (p4 → (p3 ∨ p3))) ∨ False) ∨ (p5 ∧ p3))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_111260096914170448354277785915 : ((((p4 ∨ False) ∨ ((p1 ∧ True) ∨ ((True ∧ (((p1 ∨ False) → (p3 ∧ (True ∧ (p2 → p5)))) ∨ p2)) → (p3 ∧ p2)))) ∧ p1) ∨ (False → p2)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_214555501366951155528716213118 : (((False ∨ p5) ∧ (p5 → p4)) ∨ ((p5 → p4) → (p2 → ((((((((False ∧ p4) ∧ p3) ∨ (p1 ∧ p3)) ∨ p3) ∨ p4) → p5) ∨ p4) ∨ True)))) := by
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
theorem thm_5_vars_346462024508545825069258716514 : (p3 → (((p3 ∧ (((p1 → p5) ∨ False) → p2)) ∧ ((p5 ∧ ((p3 ∧ p4) → p2)) ∧ ((p1 → (False ∧ p1)) ∧ (p4 → p4)))) → (p4 ∨ p5))) := by
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
  let h7 := h4.left
  let h8 := h4.right
  -- Conjunctions on the left can always be decomposed.
  let h9 := h7.left
  let h10 := h7.right
  -- Conjunctions on the left can always be decomposed.
  let h11 := h8.left
  let h12 := h8.right
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h9



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_702349859721654310381221253499 : (((((((p3 ∧ (False ∧ p1)) ∧ (p1 ∨ True)) ∨ p2) ∨ p5) ∨ (((((False ∧ (p5 ∨ (p3 ∨ True))) ∧ p2) ∨ p3) → (p2 → p3)) → True)) ∨ p3) ∧ True) := by
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
theorem thm_5_vars_171979470762622443600132170979 : (((True → ((p2 → False) ∧ (((p2 ∨ (True ∨ p1)) ∧ p2) ∧ p2))) ∧ (p2 → p2)) ∨ (p4 → (True → (p2 ∨ ((p4 ∨ (p3 ∧ p4)) ∨ p1))))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_647240785909577201981487338476 : ((((p4 → ((((p2 ∨ False) ∨ p2) → (((((p1 → (((p3 ∧ p1) → (p4 → p1)) → p4)) ∨ p3) ∧ False) ∨ p1) → p1)) ∧ True)) → p3) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_245062861802174992310374667447 : ((p1 ∧ p5) ∨ ((p4 ∨ (((p1 ∧ p2) → p2) ∧ ((p2 ∧ p5) ∨ p1))) ∨ ((p5 → (p5 ∧ (True ∧ ((p3 ∨ p4) ∨ True)))) ∧ (p4 → True)))) := by
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
  -- One of the premise coincides with the conclusion.
  exact h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- Implications on the right can always be decomposed.
  intro h2
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_160582679539626235417169856579 : (((p1 → (p2 → ((((p1 → False) → False) ∧ p1) ∨ (p5 → p1)))) → ((p4 ∧ (p4 → p5)) ∧ p2)) → ((((p5 ∧ p5) ∨ p2) ∨ p1) → p2)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Disjunctions on the left can always be decomposed.
  cases h2
  case inl h3 =>
    -- Disjunctions on the left can always be decomposed.
    cases h3
    case inl h4 =>
      -- Conjunctions on the left can always be decomposed.
      let h5 := h4.left
      let h6 := h4.right
      -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
      have h7 : (p1 → (p2 → ((((p1 → False) → False) ∧ p1) ∨ (p5 → p1)))) := by
        -- Implications on the right can always be decomposed.
        intro h8
        -- Implications on the right can always be decomposed.
        intro h9
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- Implications on the right can always be decomposed.
        intro h10
        -- One of the premise coincides with the conclusion.
        exact h8
      -- We have shown the premise of h1, we can now drive its conclusion.
      let h11 := h1 h7
      -- We need to get the right conjuct of h11 based on <expert-advice>.
      let h12 := h11.right
      -- One of the premise coincides with the conclusion.
      exact h12
    case inr h13 =>
      -- One of the premise coincides with the conclusion.
      exact h13
  case inr h14 =>
    -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
    have h15 : (p1 → (p2 → ((((p1 → False) → False) ∧ p1) ∨ (p5 → p1)))) := by
      -- Implications on the right can always be decomposed.
      intro h16
      -- Implications on the right can always be decomposed.
      intro h17
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Implications on the right can always be decomposed.
      intro h18
      -- One of the premise coincides with the conclusion.
      exact h16
    -- We have shown the premise of h1, we can now drive its conclusion.
    let h19 := h1 h15
    -- We need to get the right conjuct of h19 based on <expert-advice>.
    let h20 := h19.right
    -- One of the premise coincides with the conclusion.
    exact h20



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_319049763193481723556013430385 : (p4 ∨ ((((False → (p1 ∧ p5)) → p5) → ((p1 ∨ p2) → (((p3 ∧ p3) ∧ p3) ∧ (p5 ∧ (p5 ∧ p5))))) ∨ ((True → True) ∧ (True ∨ p3)))) := by
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
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_116366902911013138551213457273 : ((((p3 ∧ p5) → p3) → (True ∧ ((False ∨ (p4 ∧ ((p1 ∧ (((False ∨ p1) ∧ p2) → False)) → p2))) ∧ (p4 → (p4 ∨ True))))) ∨ (True ∨ p1)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_136066374921281865104960574415 : (((((p2 ∨ False) ∨ True) ∧ (p1 ∧ (p3 ∨ p2))) ∧ ((p1 ∨ ((p1 → (True → p1)) ∧ (p4 → p4))) ∨ (p5 ∧ p1))) ∨ (False → (p5 → False))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_174964590635412232845488686903 : ((True ∧ (((p5 → p5) ∨ p4) → ((((False ∧ p1) ∨ p2) → (p2 → p2)) ∧ p5))) → (((p5 ∨ p3) → p2) → (p4 ∨ (p2 ∨ (p4 ∧ p3))))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Conjunctions on the left can always be decomposed.
  let h3 := h1.left
  let h4 := h1.right
  -- We want to use the implication h4 based on <expert-advice>. So we show its premise.
  have h5 : ((p5 → p5) ∨ p4) := by
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Implications on the right can always be decomposed.
    intro h6
    -- One of the premise coincides with the conclusion.
    exact h6
  -- We have shown the premise of h4, we can now drive its conclusion.
  let h7 := h4 h5
  -- We need to get the right conjuct of h7 based on <expert-advice>.
  let h8 := h7.right
  -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
  have h9 : (p5 ∨ p3) := by
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- One of the premise coincides with the conclusion.
    exact h8
  -- We have shown the premise of h2, we can now drive its conclusion.
  let h10 := h2 h9
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- One of the premise coincides with the conclusion.
  exact h10



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_648581469038300193534891814516 : (((((((p1 ∨ (p2 → ((p5 ∧ p2) → (p2 ∨ False)))) ∧ p3) → (p5 ∧ (False ∧ ((p1 → (p2 → p3)) ∧ True)))) ∨ True) ∧ (p2 → True)) ∨ False) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_191356078629811933785602671222 : (((p3 ∨ p2) ∨ ((p3 ∧ (p1 ∧ (p5 → p1))) ∧ False)) ∨ ((False ∨ ((False ∨ (False ∨ (p5 → (p3 → (True ∧ p5))))) ∧ (p1 ∨ True))) ∨ p2)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
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
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- One of the premise coincides with the conclusion.
  exact h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_152201072613585157609219054275 : ((((((p4 ∧ p4) ∨ p1) ∧ p1) ∧ p2) ∧ (((p5 → p2) → p4) ∨ ((p2 ∨ p1) ∧ ((p1 ∧ True) ∨ p3)))) → (p3 ∨ ((p5 → p2) ∧ True))) := by
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
    -- Conjunctions on the left can always be decomposed.
    let h9 := h8.left
    let h10 := h8.right
    -- Disjunctions on the left can always be decomposed.
    cases h3
    case inl h11 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Conjunctions on the right can always be decomposed.
      apply And.intro
      -- Implications on the right can always be decomposed.
      intro h12
      -- One of the premise coincides with the conclusion.
      exact h5
      -- True on the right can always be proven directly.
      apply True.intro
    case inr h13 =>
      -- Conjunctions on the left can always be decomposed.
      let h14 := h13.left
      let h15 := h13.right
      -- Disjunctions on the left can always be decomposed.
      cases h14
      case inl h16 =>
        -- Disjunctions on the left can always be decomposed.
        cases h15
        case inl h17 =>
          -- Conjunctions on the left can always be decomposed.
          let h18 := h17.left
          let h19 := h17.right
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- Conjunctions on the right can always be decomposed.
          apply And.intro
          -- Implications on the right can always be decomposed.
          intro h20
          -- One of the premise coincides with the conclusion.
          exact h16
          -- True on the right can always be proven directly.
          apply True.intro
        case inr h21 =>
          -- Show the left disjunct based on <expert-advice>.
          apply Or.inl
          -- One of the premise coincides with the conclusion.
          exact h21
      case inr h22 =>
        -- Disjunctions on the left can always be decomposed.
        cases h15
        case inl h23 =>
          -- Conjunctions on the left can always be decomposed.
          let h24 := h23.left
          let h25 := h23.right
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- Conjunctions on the right can always be decomposed.
          apply And.intro
          -- Implications on the right can always be decomposed.
          intro h26
          -- One of the premise coincides with the conclusion.
          exact h5
          -- True on the right can always be proven directly.
          apply True.intro
        case inr h27 =>
          -- Show the left disjunct based on <expert-advice>.
          apply Or.inl
          -- One of the premise coincides with the conclusion.
          exact h27
  case inr h28 =>
    -- Disjunctions on the left can always be decomposed.
    cases h3
    case inl h29 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Conjunctions on the right can always be decomposed.
      apply And.intro
      -- Implications on the right can always be decomposed.
      intro h30
      -- One of the premise coincides with the conclusion.
      exact h5
      -- True on the right can always be proven directly.
      apply True.intro
    case inr h31 =>
      -- Conjunctions on the left can always be decomposed.
      let h32 := h31.left
      let h33 := h31.right
      -- Disjunctions on the left can always be decomposed.
      cases h32
      case inl h34 =>
        -- Disjunctions on the left can always be decomposed.
        cases h33
        case inl h35 =>
          -- Conjunctions on the left can always be decomposed.
          let h36 := h35.left
          let h37 := h35.right
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- Conjunctions on the right can always be decomposed.
          apply And.intro
          -- Implications on the right can always be decomposed.
          intro h38
          -- One of the premise coincides with the conclusion.
          exact h34
          -- True on the right can always be proven directly.
          apply True.intro
        case inr h39 =>
          -- Show the left disjunct based on <expert-advice>.
          apply Or.inl
          -- One of the premise coincides with the conclusion.
          exact h39
      case inr h40 =>
        -- Disjunctions on the left can always be decomposed.
        cases h33
        case inl h41 =>
          -- Conjunctions on the left can always be decomposed.
          let h42 := h41.left
          let h43 := h41.right
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- Conjunctions on the right can always be decomposed.
          apply And.intro
          -- Implications on the right can always be decomposed.
          intro h44
          -- One of the premise coincides with the conclusion.
          exact h5
          -- True on the right can always be proven directly.
          apply True.intro
        case inr h45 =>
          -- Show the left disjunct based on <expert-advice>.
          apply Or.inl
          -- One of the premise coincides with the conclusion.
          exact h45



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_635540012511231365253376609585 : ((((((((p5 → p1) ∨ False) ∨ (p2 ∧ (False → ((False ∨ (p4 ∧ p5)) ∧ (p3 ∨ p4))))) → True) ∨ ((p5 ∧ (p2 ∧ p5)) ∨ True)) → p2) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_381642204358910936908410932912 : (((((((True → False) → (((p4 → ((p3 ∨ (True ∧ (p3 → False))) ∨ (p3 ∨ p5))) → p3) ∨ ((p5 ∧ False) ∨ False))) ∧ p5) ∨ p1) ∨ True) ∧ True) ∧ True) := by
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
theorem thm_5_vars_609463128163781780296388568483 : (((((False ∧ ((p4 → (((((p4 ∧ ((p1 → (p2 ∧ p2)) ∨ p1)) → True) → ((p5 → p5) ∧ False)) ∧ p4) ∧ p4)) ∨ p2)) ∨ p4) ∨ p4) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_41747107084629778542023762614 : ((((((p3 ∧ p1) ∨ p1) ∧ False) ∨ (((p1 ∧ p3) ∨ ((((p3 ∧ (p4 ∧ p2)) ∨ p1) → p4) ∨ ((p3 → p2) → True))) → p4)) ∨ True) ∨ p3) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_342794400386659379986143216260 : (p2 → (((p3 ∧ p3) → ((False ∨ p2) ∨ (p1 ∨ p2))) → ((False ∨ ((True ∧ (False ∨ (p3 → (p2 → (False ∧ p1))))) ∨ (p3 → False))) ∨ p2))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_313992630956334350154134692307 : (p3 ∨ ((((p4 ∨ p2) ∧ p1) → (((p3 ∧ p4) ∧ ((p1 ∨ (True ∧ p5)) ∧ (((p2 ∧ p5) → (p4 ∨ p2)) ∨ p5))) ∨ False)) ∨ (p4 → True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_601268202164259915328409394770 : ((((p2 ∧ ((((p1 ∧ (p2 → (True ∨ ((True ∨ p4) → p4)))) → False) ∧ (p2 ∧ (False ∨ p2))) ∧ (p2 ∨ ((p4 ∧ p1) → p5)))) ∧ p5) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



