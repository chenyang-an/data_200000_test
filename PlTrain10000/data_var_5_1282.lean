variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_217565561418232914432558928474 : ((((p5 ∧ p1) ∨ p1) → p1) → ((p3 → (p4 ∧ p5)) → (p3 → ((((p4 ∧ p1) ∧ p3) ∨ ((p2 → (p4 → (False ∨ p4))) ∨ p1)) → p5)))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Implications on the right can always be decomposed.
  intro h3
  -- Implications on the right can always be decomposed.
  intro h4
  -- Disjunctions on the left can always be decomposed.
  cases h4
  case inl h5 =>
    -- Conjunctions on the left can always be decomposed.
    let h6 := h5.left
    let h7 := h5.right
    -- Conjunctions on the left can always be decomposed.
    let h8 := h6.left
    let h9 := h6.right
    -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
    have h10 : p3 := by
      -- One of the premise coincides with the conclusion.
      exact h3
    -- We have shown the premise of h2, we can now drive its conclusion.
    let h11 := h2 h10
    -- We need to get the right conjuct of h11 based on <expert-advice>.
    let h12 := h11.right
    -- One of the premise coincides with the conclusion.
    exact h12
  case inr h13 =>
    -- Disjunctions on the left can always be decomposed.
    cases h13
    case inl h14 =>
      -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
      have h15 : p3 := by
        -- One of the premise coincides with the conclusion.
        exact h3
      -- We have shown the premise of h2, we can now drive its conclusion.
      let h16 := h2 h15
      -- We need to get the right conjuct of h16 based on <expert-advice>.
      let h17 := h16.right
      -- One of the premise coincides with the conclusion.
      exact h17
    case inr h18 =>
      -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
      have h19 : p3 := by
        -- One of the premise coincides with the conclusion.
        exact h3
      -- We have shown the premise of h2, we can now drive its conclusion.
      let h20 := h2 h19
      -- We need to get the right conjuct of h20 based on <expert-advice>.
      let h21 := h20.right
      -- One of the premise coincides with the conclusion.
      exact h21



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_171375929905176049659905173967 : (((((p4 ∧ (((False ∨ p4) ∧ p5) ∨ p2)) → True) ∧ ((False ∨ p3) ∨ p1)) ∧ False) ∨ (((p5 ∨ True) ∨ (p3 ∨ (p1 ∧ p4))) ∨ (p4 ∨ False))) := by
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
theorem thm_5_vars_63972745752644313460817826059 : ((False ∨ ((((p1 ∧ ((((p5 ∨ p2) → ((True → p2) → p5)) ∧ (False ∨ (p4 ∧ (p1 ∧ p4)))) ∨ p1)) ∧ False) → (False → p1)) → p4)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_722434504281815433548554184980 : (((((True ∨ p1) ∧ p4) ∧ (True → ((True ∨ (False ∧ False)) ∧ (((p1 ∨ ((p3 ∨ p2) ∨ p4)) ∧ ((False ∧ p5) ∧ True)) ∧ (p5 → False))))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_323538863889344062105522541813 : (p5 ∨ (((False → (p2 ∧ ((p5 ∨ p5) → (p1 ∧ (True → ((False → (((p2 → p5) ∨ p4) → p4)) ∧ p3)))))) ∧ p2) → (p1 ∨ (p3 → p3)))) := by
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
  -- One of the premise coincides with the conclusion.
  exact h4



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_313158976773594414935145474486 : (p3 ∨ (((p1 ∧ (((p4 → (p4 ∧ p5)) ∨ ((False ∨ p1) ∧ p4)) ∧ p5)) ∨ (((False ∧ (True ∧ ((p5 ∧ p5) → p3))) ∨ p3) ∨ True)) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_309307611541357611534747606068 : (p2 ∨ ((((((p2 → (True → (True ∨ (True → ((False ∨ (p2 → False)) ∧ True))))) → (False ∧ (True → p1))) ∧ p1) ∨ p1) ∨ True) ∨ (p3 → p3))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_147379002580030087698491130371 : ((((False ∨ ((p3 ∧ (((p2 ∧ True) → p4) → p1)) ∨ p4)) ∧ ((p2 ∨ True) ∨ (False ∨ (p2 ∧ p2)))) ∨ True) ∨ ((True ∧ (p2 ∧ p4)) → p4)) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_17955350343177342929616381242 : ((((True → (p1 ∧ (p2 → ((p1 ∨ p3) ∨ ((p5 ∨ p5) ∧ True))))) → (p5 ∧ ((p4 → p5) → p2))) ∨ (((p3 ∧ True) ∧ p2) ∨ True)) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_262263231866215041588040315747 : (True ∧ ((((p2 → ((p1 ∧ (p2 → ((False ∨ False) ∧ p5))) → p3)) ∧ ((p5 ∨ ((p1 ∨ p5) ∨ p5)) ∧ p5)) → ((p4 ∨ p2) ∨ True)) ∨ p2)) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- True on the right can always be proven directly.
  apply True.intro
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
  cases h4
  case inl h6 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro
  case inr h7 =>
    -- Disjunctions on the left can always be decomposed.
    cases h7
    case inl h8 =>
      -- Disjunctions on the left can always be decomposed.
      cases h8
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
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- True on the right can always be proven directly.
      apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_689737662478127199127228364229 : ((((((True ∧ p3) ∨ p2) ∨ ((True ∨ ((p5 → p4) ∧ (p1 ∧ p2))) → (True → p4))) ∨ (p1 ∨ ((p3 ∨ ((p2 → p3) ∨ True)) ∧ True))) ∨ p1) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_624275805809366467117689204877 : ((((p3 ∨ (((p2 ∧ ((p3 ∧ (p1 ∨ p1)) ∨ (p5 ∨ (False ∧ (p4 → ((p4 ∨ p5) → (p5 ∨ p3))))))) ∨ p1) ∨ (p5 ∧ True))) ∨ p2) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_655567299288473936791033885866 : ((((((p3 ∨ (p3 → ((p1 ∨ True) → p5))) ∧ ((True → p4) ∧ ((p2 ∧ (False ∧ (p4 ∧ False))) → True))) → (p4 ∨ p2)) ∨ (p4 → p1)) ∨ p1) ∧ True) := by
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
  -- Disjunctions on the left can always be decomposed.
  cases h2
  case inl h4 =>
    -- Conjunctions on the left can always be decomposed.
    let h5 := h3.left
    let h6 := h3.right
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- We want to use the implication h5 based on <expert-advice>. So we show its premise.
    have h7 : True := by
      -- True on the right can always be proven directly.
      apply True.intro
    -- We have shown the premise of h5, we can now drive its conclusion.
    let h8 := h5 h7
    -- One of the premise coincides with the conclusion.
    exact h8
  case inr h9 =>
    -- Conjunctions on the left can always be decomposed.
    let h10 := h3.left
    let h11 := h3.right
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- We want to use the implication h10 based on <expert-advice>. So we show its premise.
    have h12 : True := by
      -- True on the right can always be proven directly.
      apply True.intro
    -- We have shown the premise of h10, we can now drive its conclusion.
    let h13 := h10 h12
    -- One of the premise coincides with the conclusion.
    exact h13
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_115030839069268887133625152176 : (((p3 → ((((p1 ∨ True) ∨ p1) ∨ (p3 ∨ (False → False))) ∨ p2)) ∧ ((((p5 → True) → p2) ∧ p3) ∨ ((p2 ∧ False) ∨ p4))) ∨ (True → True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_46821128244287495480399131513 : (((((p1 → ((((p1 → (p4 → True)) → True) → ((p5 → False) ∨ ((p1 ∧ p1) ∧ p3))) → (p4 → True))) → p2) ∧ False) ∨ (p2 ∨ p1)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_654040000593030931331854042452 : (((((p4 ∨ (((False ∨ (p4 ∨ (((p5 → p1) → p1) → p1))) → p3) ∨ (((False ∨ True) → (p3 ∧ False)) → p2))) ∧ p4) ∨ (p4 → p4)) ∨ p1) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- One of the premise coincides with the conclusion.
  exact h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_345452099167562133194857411737 : (p3 → (((((((((False ∧ ((False ∨ p2) ∨ True)) → True) ∧ (p5 ∨ p3)) ∧ p5) ∨ False) ∧ ((p1 ∧ True) ∨ p5)) ∧ p1) → (p2 ∧ p4)) ∨ True)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_259918962246683052056077747889 : ((p1 → p5) → (((p3 ∨ ((False ∧ p5) → (p5 ∨ ((p4 ∧ p5) → p5)))) → ((p4 → p5) ∨ (True ∧ (p5 ∧ ((p1 ∧ True) ∧ p4))))) ∨ True)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_323196127783421610801349795505 : (p5 ∨ (((p2 ∨ (((False ∨ ((p5 ∨ (True ∨ ((p2 ∨ p4) → (p3 → p5)))) → p5)) ∧ (p1 → p5)) ∧ (p4 ∧ True))) → False) ∨ (p3 → p3))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_646177788216777641481028945720 : ((((False → ((((p5 ∨ ((p5 → p2) → p1)) ∧ ((False → (p3 ∧ (False ∨ p1))) ∨ (((p2 → True) ∧ p4) ∧ True))) ∨ False) → p5)) → False) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_720537664601945088348667143353 : (((((p2 → (p3 ∧ p1)) ∨ p5) → ((p5 ∨ p4) → (p2 ∨ ((p2 ∧ ((p5 → False) ∧ (p5 ∨ (True ∧ p5)))) → (p5 ∧ (p4 ∨ p3)))))) ∨ p5) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
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
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Implications on the right can always be decomposed.
      intro h5
      -- Conjunctions on the right can always be decomposed.
      apply And.intro
      -- Conjunctions on the left can always be decomposed.
      let h6 := h5.left
      let h7 := h5.right
      -- Conjunctions on the left can always be decomposed.
      let h8 := h7.left
      let h9 := h7.right
      -- Disjunctions on the left can always be decomposed.
      cases h9
      case inl h10 =>
        -- One of the premise coincides with the conclusion.
        exact h10
      case inr h11 =>
        -- Conjunctions on the left can always be decomposed.
        let h12 := h11.left
        let h13 := h11.right
        -- One of the premise coincides with the conclusion.
        exact h13
      -- Conjunctions on the left can always be decomposed.
      let h14 := h5.left
      let h15 := h5.right
      -- Conjunctions on the left can always be decomposed.
      let h16 := h15.left
      let h17 := h15.right
      -- Disjunctions on the left can always be decomposed.
      cases h17
      case inl h18 =>
        -- We want to use the implication h16 based on <expert-advice>. So we show its premise.
        have h19 : p5 := by
          -- One of the premise coincides with the conclusion.
          exact h18
        -- We have shown the premise of h16, we can now drive its conclusion.
        let h20 := h16 h19
        -- False on the left can always be used.
        apply False.elim h20
      case inr h21 =>
        -- Conjunctions on the left can always be decomposed.
        let h22 := h21.left
        let h23 := h21.right
        -- We want to use the implication h16 based on <expert-advice>. So we show its premise.
        have h24 : p5 := by
          -- One of the premise coincides with the conclusion.
          exact h23
        -- We have shown the premise of h16, we can now drive its conclusion.
        let h25 := h16 h24
        -- False on the left can always be used.
        apply False.elim h25
    case inr h26 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Implications on the right can always be decomposed.
      intro h27
      -- Conjunctions on the right can always be decomposed.
      apply And.intro
      -- Conjunctions on the left can always be decomposed.
      let h28 := h27.left
      let h29 := h27.right
      -- Conjunctions on the left can always be decomposed.
      let h30 := h29.left
      let h31 := h29.right
      -- Disjunctions on the left can always be decomposed.
      cases h31
      case inl h32 =>
        -- One of the premise coincides with the conclusion.
        exact h32
      case inr h33 =>
        -- Conjunctions on the left can always be decomposed.
        let h34 := h33.left
        let h35 := h33.right
        -- One of the premise coincides with the conclusion.
        exact h35
      -- Conjunctions on the left can always be decomposed.
      let h36 := h27.left
      let h37 := h27.right
      -- Conjunctions on the left can always be decomposed.
      let h38 := h37.left
      let h39 := h37.right
      -- Disjunctions on the left can always be decomposed.
      cases h39
      case inl h40 =>
        -- We want to use the implication h38 based on <expert-advice>. So we show its premise.
        have h41 : p5 := by
          -- One of the premise coincides with the conclusion.
          exact h40
        -- We have shown the premise of h38, we can now drive its conclusion.
        let h42 := h38 h41
        -- False on the left can always be used.
        apply False.elim h42
      case inr h43 =>
        -- Conjunctions on the left can always be decomposed.
        let h44 := h43.left
        let h45 := h43.right
        -- We want to use the implication h38 based on <expert-advice>. So we show its premise.
        have h46 : p5 := by
          -- One of the premise coincides with the conclusion.
          exact h45
        -- We have shown the premise of h38, we can now drive its conclusion.
        let h47 := h38 h46
        -- False on the left can always be used.
        apply False.elim h47
  case inr h48 =>
    -- Disjunctions on the left can always be decomposed.
    cases h1
    case inl h49 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Implications on the right can always be decomposed.
      intro h50
      -- Conjunctions on the right can always be decomposed.
      apply And.intro
      -- Conjunctions on the left can always be decomposed.
      let h51 := h50.left
      let h52 := h50.right
      -- Conjunctions on the left can always be decomposed.
      let h53 := h52.left
      let h54 := h52.right
      -- Disjunctions on the left can always be decomposed.
      cases h54
      case inl h55 =>
        -- One of the premise coincides with the conclusion.
        exact h55
      case inr h56 =>
        -- Conjunctions on the left can always be decomposed.
        let h57 := h56.left
        let h58 := h56.right
        -- One of the premise coincides with the conclusion.
        exact h58
      -- Conjunctions on the left can always be decomposed.
      let h59 := h50.left
      let h60 := h50.right
      -- Conjunctions on the left can always be decomposed.
      let h61 := h60.left
      let h62 := h60.right
      -- Disjunctions on the left can always be decomposed.
      cases h62
      case inl h63 =>
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- One of the premise coincides with the conclusion.
        exact h48
      case inr h64 =>
        -- Conjunctions on the left can always be decomposed.
        let h65 := h64.left
        let h66 := h64.right
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- One of the premise coincides with the conclusion.
        exact h48
    case inr h67 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Implications on the right can always be decomposed.
      intro h68
      -- Conjunctions on the right can always be decomposed.
      apply And.intro
      -- Conjunctions on the left can always be decomposed.
      let h69 := h68.left
      let h70 := h68.right
      -- Conjunctions on the left can always be decomposed.
      let h71 := h70.left
      let h72 := h70.right
      -- Disjunctions on the left can always be decomposed.
      cases h72
      case inl h73 =>
        -- One of the premise coincides with the conclusion.
        exact h73
      case inr h74 =>
        -- Conjunctions on the left can always be decomposed.
        let h75 := h74.left
        let h76 := h74.right
        -- One of the premise coincides with the conclusion.
        exact h76
      -- Conjunctions on the left can always be decomposed.
      let h77 := h68.left
      let h78 := h68.right
      -- Conjunctions on the left can always be decomposed.
      let h79 := h78.left
      let h80 := h78.right
      -- Disjunctions on the left can always be decomposed.
      cases h80
      case inl h81 =>
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- One of the premise coincides with the conclusion.
        exact h48
      case inr h82 =>
        -- Conjunctions on the left can always be decomposed.
        let h83 := h82.left
        let h84 := h82.right
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- One of the premise coincides with the conclusion.
        exact h48
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_637257529678184157931151038719 : ((((((False → ((p1 ∧ (((True → p5) ∧ p4) → p4)) ∨ p1)) → p4) → (((p5 ∨ p2) → False) ∧ ((p4 ∨ (p2 → p2)) → p1))) → False) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_149573436355461700258736813773 : ((p2 ∧ (p5 ∨ ((p1 → (p2 ∨ ((p4 ∧ (p4 ∨ (p2 ∧ (p5 ∧ (True ∨ p4))))) → p4))) ∧ (p3 ∧ p2)))) ∨ ((False ∧ p3) ∨ (True ∨ p4))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_427866565048642012538486998225 : ((((((p2 ∨ (((p4 ∨ True) ∨ p3) → p2)) ∨ (False ∨ (((p5 ∨ p3) ∨ ((p2 → False) ∨ p1)) ∨ (p2 ∧ p1)))) ∨ p4) ∨ (p1 → p1)) ∧ True) ∧ True) := by
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
theorem thm_5_vars_148030778655036698648876624540 : (((((p5 ∧ p4) ∧ p1) ∨ ((True ∨ (((p5 ∧ (True ∨ (p2 → p5))) ∧ False) → False)) → p5)) ∨ (p1 ∧ False)) ∨ (True ∨ (p2 ∧ (p1 ∧ p4)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_224327201052073325933435276175 : ((False → (p3 ∨ p2)) ∧ (p5 → ((((((p2 ∧ (p2 ∧ ((True ∧ False) ∨ (p4 ∧ ((False ∧ p5) ∨ False))))) ∧ p4) ∧ False) → p1) → False) ∨ p5))) := by
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
  -- One of the premise coincides with the conclusion.
  exact h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_49516037596286873785287510414 : ((((((p1 ∧ False) ∧ (True → (False ∨ True))) ∨ ((p1 ∨ (((False → p2) ∧ True) ∧ p1)) → p4)) ∧ (p1 → p2)) → ((p3 ∧ p2) ∨ True)) ∨ p3) := by
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
    -- Conjunctions on the left can always be decomposed.
    let h7 := h5.left
    let h8 := h5.right
    -- False on the left can always be used.
    apply False.elim h8
  case inr h9 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_50532928556892271962092851524 : (((((((((((False ∨ p3) ∨ p3) ∨ p3) ∧ True) → ((False ∨ p5) → True)) ∧ True) ∧ p3) → False) ∨ p1) → ((p2 → (p4 ∨ p5)) ∧ p4)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_160079074806650952581991512840 : (((False ∨ ((p4 ∨ p4) ∨ (p5 → (p5 ∧ ((((p3 → True) ∨ p1) ∧ (True ∧ p2)) ∧ p3))))) → p5) → (p4 → (p2 ∨ (p3 → (p5 ∧ p3))))) := by
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
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h4 : (False ∨ ((p4 ∨ p4) ∨ (p5 → (p5 ∧ ((((p3 → True) ∨ p1) ∧ (True ∧ p2)) ∧ p3))))) := by
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- One of the premise coincides with the conclusion.
    exact h2
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h5 := h1 h4
  -- One of the premise coincides with the conclusion.
  exact h5
  -- One of the premise coincides with the conclusion.
  exact h3



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_200350349232833531022722550406 : (((p5 ∨ p4) ∧ (((p3 → p4) ∧ False) → p4)) → ((p3 ∨ (p2 ∨ False)) ∨ (True ∨ ((False ∧ p5) ∧ ((((p2 ∨ p1) → True) ∨ p2) ∨ True))))) := by
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
theorem thm_5_vars_758730227416648326952739747512 : (((p2 ∧ ((False ∧ ((p3 → (p4 → (p2 ∨ (p3 ∨ p1)))) ∧ (((True → (True → (False ∨ ((p4 ∨ p1) → p5)))) ∨ False) ∧ True))) ∨ True)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_51851572284785830632321172466 : ((((p2 ∧ (((((True → p3) ∨ p2) ∨ p2) → (True ∧ False)) ∧ (p4 ∨ p5))) ∧ p3) ∨ (True ∨ (((False ∨ (True → p3)) → p2) ∨ True))) ∨ False) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_600934101015915682489169633987 : ((((p1 ∧ (((((p3 ∧ p1) ∨ (p3 → ((True ∧ (((p2 ∧ (p4 ∨ p5)) ∧ p3) ∧ (True ∨ False))) ∧ True))) ∧ p5) ∨ p3) → p4)) ∧ p4) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_115606472254129023920642800208 : (((p5 ∧ (p4 ∨ ((p4 ∨ False) ∨ p3))) ∧ ((p1 ∧ (((p5 → p5) ∨ p1) → ((p5 → p4) ∧ (p4 ∧ (p4 ∨ p4))))) → p5)) ∨ (p3 → p3)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_639392924976823948642033941703 : (((((p5 ∧ ((p2 ∧ False) → True)) → ((p2 → True) ∧ ((((False ∨ p2) ∨ (p3 ∨ ((p5 ∧ p2) ∨ p2))) → (p5 → p3)) ∧ p1))) → p3) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_317768780234930809753746754368 : (p4 ∨ ((((p1 ∧ (((False → p3) → p5) → p3)) ∧ ((p2 ∨ p3) → (p5 → p4))) ∧ (p5 → ((True → ((p1 → p2) → p2)) ∧ False))) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_344370656660439844270994544555 : (p2 → (p4 ∨ ((p5 ∨ ((p4 ∨ (p1 ∧ p2)) ∨ ((p4 → p1) ∨ True))) ∧ (((p2 ∧ (p5 ∨ (((p4 ∧ False) → False) ∨ p5))) ∧ True) ∨ False)))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
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
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- One of the premise coincides with the conclusion.
  exact h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h2
  -- Conjunctions on the left can always be decomposed.
  let h3 := h2.left
  let h4 := h2.right
  -- False on the left can always be used.
  apply False.elim h4
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_166441631928402541221787622430 : ((p2 ∨ ((((p4 ∨ p5) ∨ (p1 → (((True → (False ∨ p3)) → False) → p4))) ∧ p5) ∨ False)) ∨ (p4 → ((p3 ∧ p5) ∨ (p3 → (False ∨ True))))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h2
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_61108839398002987525647650693 : ((False ∧ ((((p2 ∧ p5) ∨ (((True → (p1 ∨ True)) ∨ p5) ∨ p2)) ∧ p3) ∧ (((True ∧ p3) ∨ p3) ∧ (((p5 → p3) ∧ p5) ∧ False)))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_797069177974546998837229343290 : (((p1 → ((((p4 → p5) ∧ (((p2 → (p4 → p3)) → p4) ∧ (p4 ∨ p5))) → (p2 ∧ (p2 ∨ (((p1 → p2) ∨ p2) ∨ p1)))) ∧ p2)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_354597634417421076637728006515 : (p5 → ((((((p1 → p3) → (p1 ∧ (((((p1 → (p1 → ((p4 ∨ p3) ∨ p1))) ∧ False) ∧ p4) ∧ False) ∧ True))) ∨ True) ∧ p5) ∨ p1) ∨ False)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
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
theorem thm_5_vars_2450327851416570136189847390 : (((((True ∧ False) ∨ (p1 ∨ (p3 ∨ p4))) ∧ p2) ∨ True) ∨ ((((True ∧ (p2 ∨ p1)) → p4) ∧ ((True ∧ p3) ∨ p4)) ∨ (p1 ∨ False))) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_338218644748230954346589024580 : (p1 → ((p2 → (p5 → (p2 → (p1 → True)))) ∧ (((False ∧ (p2 → (p4 ∧ (True ∧ p4)))) ∧ ((p3 → (p5 → (p5 ∨ p3))) → False)) ∨ p1))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h2
  -- Implications on the right can always be decomposed.
  intro h3
  -- Implications on the right can always be decomposed.
  intro h4
  -- Implications on the right can always be decomposed.
  intro h5
  -- True on the right can always be proven directly.
  apply True.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_138000790843170024446415605516 : ((p5 ∨ (True → (((((p1 → ((p1 ∧ ((p2 ∨ p1) ∧ p5)) ∧ False)) ∨ True) ∧ p4) → p4) → (p3 ∧ (p3 ∨ p3))))) ∨ (True ∨ (p1 → p5))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_136608782398176487317399902490 : (((p3 → (p4 ∧ p1)) ∨ (p1 → (p4 → ((((p3 ∨ ((p4 ∧ False) ∨ ((p5 → p2) → p4))) ∧ p4) ∧ p1) ∧ p3)))) ∨ ((False ∧ False) → p5)) := by
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
theorem thm_5_vars_264377106959995201850313261073 : (True ∧ (((p3 ∧ (p3 → True)) ∧ p5) ∨ (((p4 ∧ p2) ∨ (p1 ∨ False)) ∨ ((True → (p5 → (False → (True ∧ p3)))) → ((p3 ∧ p1) ∨ True))))) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_2180427959539953246677750686 : (((p1 → (False ∧ ((p1 → True) → (True ∧ ((False ∧ (True → True)) ∨ p5))))) ∨ p5) ∨ (False → (((p5 ∧ p2) ∨ p2) ∨ (p3 → True)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_52651315292076184174755807931 : (((False ∧ ((p1 ∨ p3) ∨ ((True → (p5 → (p2 → (p4 ∧ True)))) → False))) ∨ (p1 ∨ (p1 → ((False → (p4 ∧ (True → p4))) ∨ p4)))) ∨ p2) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
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
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- False on the left can always be used.
  apply False.elim h2
  -- Implications on the right can always be decomposed.
  intro h3
  -- False on the left can always be used.
  apply False.elim h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_230626032396965357903898320999 : (((p2 → p3) ∧ p4) → (((p5 ∧ p1) ∨ ((((p4 ∧ (p5 ∧ p5)) ∨ p5) ∧ p3) → ((True ∧ p4) → ((p2 ∧ (p4 → p1)) ∧ p3)))) ∨ True)) := by
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
theorem thm_5_vars_49434281090275439991431368360 : (((((p3 ∨ (((((((p4 → p1) ∧ p2) ∨ p2) ∧ False) → True) → (False ∧ p3)) ∧ (p4 → p1))) → p5) ∨ p3) → (p5 → (p5 ∨ p1))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_14524374954567159553569484808 : (((((((True ∨ ((p2 → ((((p4 ∧ True) ∧ (False ∧ (p4 → p5))) → True) ∨ p3)) ∧ True)) ∨ False) → p3) ∨ p3) ∨ p2) ∨ (False → False)) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- False on the left can always be used.
  apply False.elim h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_57616523428775376534962341114 : ((((True ∧ p2) ∨ p5) → ((p5 → p3) ∨ (p2 ∧ ((p2 → (((False → p1) → p4) ∧ p1)) ∨ (((p5 ∧ (p1 ∨ False)) ∧ p4) ∧ p5))))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_346397257649571162505911987239 : (p3 → ((p5 → ((p3 → (((p1 → p3) → p1) ∧ False)) ∨ ((((p2 → (p2 → False)) ∨ p3) → ((p2 ∨ p4) ∨ p1)) ∨ p4))) ∨ (p2 ∨ True))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_248658162512912469074641616841 : ((p3 ∨ p1) ∨ ((False → True) → (((False ∧ (p1 ∧ p3)) ∨ ((True ∧ False) → p4)) ∨ ((((False ∧ p2) ∨ (p3 ∨ p4)) ∧ (True → p2)) ∨ p2)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
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
  -- False on the left can always be used.
  apply False.elim h4



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_113530618189931396392057705481 : ((((p4 ∧ ((p1 → (True → False)) → p4)) ∧ (((p2 ∧ (p4 ∧ (True → True))) ∧ p4) ∨ (p2 → (p5 → p1)))) ∨ (p3 ∧ p5)) ∨ (p2 ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_245512205430509867842665263716 : ((p2 ∧ p5) ∨ (True → ((((True ∧ p3) → False) → ((p1 ∨ (p3 → p2)) ∧ ((p2 ∧ p1) → (p4 → (p5 ∨ True))))) ∧ ((True ∨ p1) ∨ p5)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h2
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h3
  -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
  have h4 : (True ∧ p3) := by
    -- Conjunctions on the right can always be decomposed.
    apply And.intro
    -- True on the right can always be proven directly.
    apply True.intro
    -- One of the premise coincides with the conclusion.
    exact h3
  -- We have shown the premise of h2, we can now drive its conclusion.
  let h5 := h2 h4
  -- False on the left can always be used.
  apply False.elim h5
  -- Implications on the right can always be decomposed.
  intro h6
  -- Implications on the right can always be decomposed.
  intro h7
  -- Conjunctions on the left can always be decomposed.
  let h8 := h6.left
  let h9 := h6.right
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_353370004993176523237279803065 : (p4 → (False ∨ ((((((p1 ∨ p4) ∨ p1) ∧ (p2 ∧ False)) ∧ p4) ∨ ((p4 ∨ (p2 ∧ p3)) ∧ p3)) ∨ (((p5 ∧ (False ∧ p5)) ∨ True) ∨ p5)))) := by
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
theorem thm_5_vars_148808526008455384725647292320 : (((((p5 → False) ∨ True) ∧ (True → False)) → ((p4 ∨ p1) ∨ ((p1 → ((p3 ∨ p2) ∨ True)) ∨ (p2 ∨ p5)))) ∨ ((True → p4) → (p4 → True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_116427942905341954138442641695 : (((True → (p4 ∧ False)) → (((p5 ∨ (p5 ∧ (True → p2))) → p4) ∧ (False ∧ (((p1 ∨ p4) ∨ p5) ∧ ((p5 ∧ p3) → False))))) ∨ (True → p5)) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h2
  -- Disjunctions on the left can always be decomposed.
  cases h2
  case inl h3 =>
    -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
    have h4 : True := by
      -- True on the right can always be proven directly.
      apply True.intro
    -- We have shown the premise of h1, we can now drive its conclusion.
    let h5 := h1 h4
    -- We need to get the left conjuct of h5 based on <expert-advice>.
    let h6 := h5.left
    -- One of the premise coincides with the conclusion.
    exact h6
  case inr h7 =>
    -- Conjunctions on the left can always be decomposed.
    let h8 := h7.left
    let h9 := h7.right
    -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
    have h10 : True := by
      -- True on the right can always be proven directly.
      apply True.intro
    -- We have shown the premise of h1, we can now drive its conclusion.
    let h11 := h1 h10
    -- We need to get the left conjuct of h11 based on <expert-advice>.
    let h12 := h11.left
    -- One of the premise coincides with the conclusion.
    exact h12
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h13 : True := by
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h14 := h1 h13
  -- We need to get the right conjuct of h14 based on <expert-advice>.
  let h15 := h14.right
  -- False on the left can always be used.
  apply False.elim h15
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h16 : True := by
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h17 := h1 h16
  -- We need to get the right conjuct of h17 based on <expert-advice>.
  let h18 := h17.right
  -- False on the left can always be used.
  apply False.elim h18
  -- Implications on the right can always be decomposed.
  intro h19
  -- Conjunctions on the left can always be decomposed.
  let h20 := h19.left
  let h21 := h19.right
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h22 : True := by
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h23 := h1 h22
  -- We need to get the right conjuct of h23 based on <expert-advice>.
  let h24 := h23.right
  -- False on the left can always be used.
  apply False.elim h24



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_39065136723801744849500458132 : ((((p5 ∧ p3) ∨ ((((((((False ∧ p5) ∧ True) ∧ p1) ∨ p5) ∨ (p4 ∨ p2)) → p2) ∧ p5) ∧ (p2 ∨ (p1 → (p3 ∧ False))))) ∧ False) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_351941077003142846077161308402 : (p4 → (((True ∧ (True ∧ p3)) ∨ (p1 → (False ∨ (p3 → p5)))) → ((((p1 → ((p2 ∧ (p5 ∨ p5)) → p3)) → p2) → (p2 ∨ False)) ∨ p4))) := by
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
    -- Conjunctions on the left can always be decomposed.
    let h6 := h5.left
    let h7 := h5.right
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h1
  case inr h8 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_228563464547520196710996020827 : ((p1 ∨ (False ∨ p5)) ∨ ((((p4 ∨ (True → False)) ∨ p1) ∨ True) ∨ ((p1 → ((p1 ∧ (((p3 ∨ p3) → p5) ∨ False)) ∧ (False ∧ p3))) → p3))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_265697168628250199220948586690 : (True ∧ (p3 ∨ ((False ∧ ((((True ∧ p3) → p4) → False) ∨ ((((p1 ∧ (p3 → ((False → p3) → True))) ∧ True) ∨ (p4 ∨ p1)) ∧ p3))) ∨ True))) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_52479542110561107878180304376 : (((True → (((p2 ∨ p4) ∧ (p3 ∧ (p4 → (p2 ∨ p1)))) → (False ∧ p5))) ∧ ((((True → (False ∨ True)) → p4) ∧ p4) ∧ (p3 ∧ p4))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_16699558034641088521330772146 : ((((((((p1 → p2) ∨ p3) ∨ (p3 ∧ (True → p3))) ∧ (False → ((p2 ∨ p1) ∧ p3))) ∨ p1) ∨ (p2 → p5)) ∨ (False ∨ (False → p2))) ∧ True) := by
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
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_695315108704978468085981463764 : ((((((p4 → p1) ∧ ((p4 → (p1 ∧ False)) ∨ (True ∧ (True → False)))) → p4) → ((((p5 ∨ False) ∨ (p4 ∧ False)) → (p5 ∧ p2)) → p3)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_43582924853985273315692713432 : (((((((p5 ∨ (True ∧ ((True → True) → (p3 → (False ∧ (p4 → (p1 → (p1 → True)))))))) ∧ p5) → (p2 → False)) ∨ True) → p5) → p5) ∨ p5) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h2 : ((((p5 ∨ (True ∧ ((True → True) → (p3 → (False ∧ (p4 → (p1 → (p1 → True)))))))) ∧ p5) → (p2 → False)) ∨ True) := by
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h3 := h1 h2
  -- One of the premise coincides with the conclusion.
  exact h3



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_117893085661296730540932444366 : ((p5 ∧ (((p3 → (True → p1)) → (p1 → (p2 ∧ (((p5 ∨ ((p2 ∧ p5) ∧ p5)) ∧ True) ∧ (p4 → p5))))) → (p1 ∨ p3))) ∨ (False ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_325810938346134212310048227770 : (p5 ∨ (p3 ∨ (((False ∨ p5) ∧ (p1 ∧ (((p5 ∨ False) ∨ (((False ∧ p1) → True) ∨ p2)) ∨ (p1 → (p3 ∨ p1))))) → (p4 ∨ (False → True))))) := by
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
    -- False on the left can always be used.
    apply False.elim h4
  case inr h5 =>
    -- Conjunctions on the left can always be decomposed.
    let h6 := h3.left
    let h7 := h3.right
    -- Disjunctions on the left can always be decomposed.
    cases h7
    case inl h8 =>
      -- Disjunctions on the left can always be decomposed.
      cases h8
      case inl h9 =>
        -- Disjunctions on the left can always be decomposed.
        cases h9
        case inl h10 =>
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- Implications on the right can always be decomposed.
          intro h11
          -- True on the right can always be proven directly.
          apply True.intro
        case inr h12 =>
          -- False on the left can always be used.
          apply False.elim h12
      case inr h13 =>
        -- Disjunctions on the left can always be decomposed.
        cases h13
        case inl h14 =>
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- Implications on the right can always be decomposed.
          intro h15
          -- True on the right can always be proven directly.
          apply True.intro
        case inr h16 =>
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- Implications on the right can always be decomposed.
          intro h17
          -- True on the right can always be proven directly.
          apply True.intro
    case inr h18 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Implications on the right can always be decomposed.
      intro h19
      -- True on the right can always be proven directly.
      apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_38978580625584208595689542763 : ((((p3 ∧ True) ∧ ((((p3 ∧ (p1 ∨ p4)) ∧ p1) → ((p5 ∧ p4) ∧ p3)) ∨ ((p3 ∧ (False ∨ ((p2 → p3) ∧ p5))) ∧ p1))) ∧ p3) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_161013917828406987896981550525 : (((p5 ∧ (p5 ∨ False)) ∨ ((p4 ∧ ((((((p4 ∨ p4) → p5) ∨ p2) → p1) ∧ p5) ∧ p2)) → True)) → ((p3 ∧ ((p3 → p4) ∨ False)) → p4)) := by
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
    cases h1
    case inl h6 =>
      -- Conjunctions on the left can always be decomposed.
      let h7 := h6.left
      let h8 := h6.right
      -- Disjunctions on the left can always be decomposed.
      cases h8
      case inl h9 =>
        -- We want to use the implication h5 based on <expert-advice>. So we show its premise.
        have h10 : p3 := by
          -- One of the premise coincides with the conclusion.
          exact h3
        -- We have shown the premise of h5, we can now drive its conclusion.
        let h11 := h5 h10
        -- One of the premise coincides with the conclusion.
        exact h11
      case inr h12 =>
        -- False on the left can always be used.
        apply False.elim h12
    case inr h13 =>
      -- We want to use the implication h5 based on <expert-advice>. So we show its premise.
      have h14 : p3 := by
        -- One of the premise coincides with the conclusion.
        exact h3
      -- We have shown the premise of h5, we can now drive its conclusion.
      let h15 := h5 h14
      -- One of the premise coincides with the conclusion.
      exact h15
  case inr h16 =>
    -- False on the left can always be used.
    apply False.elim h16



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_181539644909957102863911229325 : ((True → (p1 ∨ (((True → (p5 ∨ p2)) ∧ p2) → ((p3 → p4) → True)))) → ((False ∨ (((p1 → p2) ∨ (True ∨ (True ∨ True))) ∨ p2)) ∨ p2)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
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
theorem thm_5_vars_143240095102315058603103961257 : ((p3 → ((((p5 ∧ ((True ∧ (p1 ∧ False)) → p4)) → True) ∨ (((p2 → (p4 ∨ p5)) → False) ∧ (p4 ∨ p3))) ∨ p2)) → (p4 ∨ (True ∨ False))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_756914591962983148667117770037 : (((p1 ∧ ((p5 ∨ ((p1 ∨ (p1 ∧ p3)) → p4)) ∧ (((((p3 ∨ p1) → p1) ∨ p5) → ((p4 → (False → False)) → (p4 → p4))) ∨ p3))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_592875661864308502922483378704 : (((((((p2 → p3) ∨ p4) ∨ (((p2 ∧ (p2 ∨ (True → True))) ∨ (p1 → (p5 ∨ p1))) ∧ (p4 ∧ True))) ∧ (p5 ∨ (p2 → p2))) ∧ p3) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_301011810269799733440332668644 : (False ∨ ((((((True ∨ (p2 ∨ False)) ∧ p3) ∨ p3) ∨ True) ∧ True) ∧ ((False ∧ (p3 → (((True ∨ (p3 ∧ (False ∨ p5))) → p5) ∧ p2))) ∨ True))) := by
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
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_136753403684994122579283710822 : (((p2 ∨ p2) ∧ (((True → ((False ∨ (False → True)) ∨ ((p1 ∧ p5) ∨ (p2 ∧ (False ∧ (p3 ∧ p1)))))) → p4) ∧ False)) ∨ ((p2 ∧ p3) → p2)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- One of the premise coincides with the conclusion.
  exact h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_587773771073118440548579681609 : ((((((((True ∧ (p1 → p1)) → (p3 ∨ ((((p4 ∨ p4) ∨ True) ∨ False) → p3))) ∨ (p4 → (p3 ∨ p2))) ∧ (p2 ∨ True)) ∨ p4) ∧ p5) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_336213478957016689754190283940 : (p1 → ((((p2 → p3) → ((True ∨ ((p3 ∧ ((p5 → (p1 ∧ (True ∨ (p3 → (p1 ∧ p2))))) ∧ True)) → p5)) ∨ True)) → (False ∧ p3)) ∨ p1)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_676206591036201898422862402843 : ((((((False → p2) → p1) ∧ (((p2 ∧ (p3 → (p5 ∨ p2))) → p5) → ((p4 ∨ (p2 ∨ p1)) ∨ p5))) ∧ (((True ∧ p3) → False) ∧ p3)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_92333964579430450695474365524 : (((False ∨ True) → (p3 ∧ (((((p1 ∧ p4) ∨ p4) → (p3 → ((p1 ∨ (p4 ∨ ((p1 → p2) ∨ (p3 → p4)))) ∧ True))) ∧ False) ∧ True))) → p2) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h2 : (False ∨ True) := by
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
  -- We need to get the right conjuct of h5 based on <expert-advice>.
  let h6 := h5.right
  -- False on the left can always be used.
  apply False.elim h6



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_172169215579456462632310826095 : ((((p1 ∧ (p4 → (p3 ∧ p4))) → (p1 → (p5 → p2))) ∨ ((p1 ∨ p2) ∨ p4)) ∨ ((p5 ∨ (((True ∧ True) → p1) ∧ (p4 ∨ True))) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_200138358882933475123689169066 : (((p5 → (p4 ∧ p5)) ∧ ((True ∨ p3) → False)) → ((p5 ∨ ((False ∨ (p2 ∨ (p3 ∧ (p2 ∧ p2)))) ∨ p1)) ∨ (True → ((False → p3) → p4)))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- We want to use the implication h3 based on <expert-advice>. So we show its premise.
  have h4 : (True ∨ p3) := by
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h3, we can now drive its conclusion.
  let h5 := h3 h4
  -- False on the left can always be used.
  apply False.elim h5



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_52621007914015630868067652047 : ((((False ∧ (p1 → p2)) ∨ ((True ∧ p1) ∧ (((p4 ∧ p1) ∧ p2) ∧ p2))) ∨ ((((p4 ∧ p1) ∧ (True ∧ p1)) ∧ p5) ∨ (p5 → True))) ∨ p5) := by
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
theorem thm_5_vars_2805482582404887858681712714 : ((p1 → ((p2 ∧ p3) ∧ False)) ∨ (((True ∧ (False → (((p2 → p3) ∧ (p2 ∧ p4)) → p5))) ∧ ((False → p5) → (p4 ∨ p2))) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_164945307842788384428274496557 : ((((((p1 → (False → p3)) → ((False ∧ True) ∨ (True ∨ (p2 ∧ True)))) → False) → p1) → p5) ∨ ((p5 ∧ ((p2 ∧ (p3 ∨ p4)) ∨ p1)) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_780860524074478422453999579767 : (((p2 ∨ ((False ∨ (True ∨ (False ∧ False))) → (p5 ∨ (p1 ∧ (p4 ∨ ((p5 → ((p4 ∨ p5) → (p5 ∨ False))) ∧ ((p2 → False) ∨ p3))))))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_757593377252678318206037803613 : (((p1 ∧ (p3 ∧ ((p5 ∧ (p4 ∨ ((True ∧ p4) ∨ (((False → ((p3 ∧ p4) ∨ (p5 ∨ (p1 ∧ p4)))) ∨ p2) ∧ p4)))) ∧ (p1 ∨ p3)))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_123442409877606611607199897646 : ((((p1 → p2) → ((((p1 → (p1 ∧ p5)) ∨ p5) → p1) ∧ (p2 ∧ ((p3 → p4) → True)))) → ((p3 ∨ True) → (True → p5))) → (p5 ∨ True)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_181582783318469089707877113972 : ((p1 → ((p4 → (True ∨ (((True ∨ p1) → False) → (p5 ∧ False)))) → True)) → (p5 → (p2 ∨ ((((True ∨ True) ∧ p2) ∧ p4) → (p5 ∨ p3))))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
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
  -- Disjunctions on the left can always be decomposed.
  cases h6
  case inl h8 =>
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- One of the premise coincides with the conclusion.
    exact h2
  case inr h9 =>
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- One of the premise coincides with the conclusion.
    exact h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_612807699447747318640596189488 : ((((((p3 ∨ p1) ∨ (p2 ∨ ((p4 ∧ ((p3 ∨ True) ∨ False)) ∧ (True → ((p2 ∨ p3) ∧ (False → (p2 → p4))))))) ∨ (True ∨ False)) ∨ p1) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_126495374045049044786135205311 : ((p2 ∧ (((True → False) ∧ p3) ∧ (p2 ∧ ((((((p5 → False) ∧ (p5 → ((False ∧ p4) → True))) → False) → False) ∧ p5) ∧ p2)))) → (p5 ∧ False)) := by
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
  -- Conjunctions on the left can always be decomposed.
  let h6 := h4.left
  let h7 := h4.right
  -- Conjunctions on the left can always be decomposed.
  let h8 := h5.left
  let h9 := h5.right
  -- Conjunctions on the left can always be decomposed.
  let h10 := h9.left
  let h11 := h9.right
  -- Conjunctions on the left can always be decomposed.
  let h12 := h10.left
  let h13 := h10.right
  -- One of the premise coincides with the conclusion.
  exact h13
  -- Conjunctions on the left can always be decomposed.
  let h14 := h1.left
  let h15 := h1.right
  -- Conjunctions on the left can always be decomposed.
  let h16 := h15.left
  let h17 := h15.right
  -- Conjunctions on the left can always be decomposed.
  let h18 := h16.left
  let h19 := h16.right
  -- Conjunctions on the left can always be decomposed.
  let h20 := h17.left
  let h21 := h17.right
  -- Conjunctions on the left can always be decomposed.
  let h22 := h21.left
  let h23 := h21.right
  -- Conjunctions on the left can always be decomposed.
  let h24 := h22.left
  let h25 := h22.right
  -- We want to use the implication h18 based on <expert-advice>. So we show its premise.
  have h26 : True := by
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h18, we can now drive its conclusion.
  let h27 := h18 h26
  -- False on the left can always be used.
  apply False.elim h27



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_165723041328911509627336497275 : (((True ∨ ((p5 ∨ p2) ∧ p1)) ∧ (((False ∨ p3) → p1) ∨ ((p2 ∨ p1) ∨ (p1 ∧ False)))) ∨ ((p2 → (p4 ∨ ((p4 ∧ p2) → p1))) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_40995658800242015418182857729 : ((((True → ((p4 → ((p2 ∨ (p2 ∧ p1)) ∨ ((p1 ∨ ((p5 → p1) ∨ True)) → (True ∧ p5)))) ∨ (False → p2))) ∨ (False ∧ p5)) ∨ p2) ∨ p1) := by
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
  -- Implications on the right can always be decomposed.
  intro h2
  -- False on the left can always be used.
  apply False.elim h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_254271051465967843107543450751 : ((p2 ∧ p3) → (((p1 ∧ (((True ∧ False) ∨ (p1 ∧ True)) ∨ (p1 ∨ False))) ∨ ((p1 ∨ (False ∨ ((p5 ∧ p2) ∧ (True → p5)))) → True)) ∨ False)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h4
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_134182156832413101672855611702 : ((((True ∨ ((((p1 ∧ p1) ∨ p5) → ((True ∨ p4) ∨ False)) ∨ p1)) ∧ (p4 ∨ ((p2 ∧ p2) ∨ (True ∧ False)))) ∨ p4) ∨ ((p4 ∨ False) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_186436543289165571814388081479 : (((p3 → (((p1 ∨ (p1 ∧ (True ∨ p3))) ∧ p2) ∨ p1)) → p5) → ((p1 ∧ ((p5 ∨ p4) → p3)) ∨ ((True ∨ p1) ∨ ((p2 ∨ p1) → p2)))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_245204606663347576220071016310 : ((p2 ∧ False) ∨ (p1 ∨ ((((p1 → p4) ∧ (p1 ∧ p1)) ∨ (True ∨ (((True → False) ∧ p3) → p4))) ∨ (((True ∨ p4) ∧ p2) ∨ (p2 ∧ p4))))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
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
theorem thm_5_vars_57041058698295719381258903727 : (((p2 → (p5 → p2)) ∧ ((p2 ∧ (((p2 ∨ p4) ∨ (p1 ∧ True)) ∨ (((True → p3) ∧ p2) → (((p1 ∧ p1) ∧ p1) ∧ p4)))) → p5)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_215340715634266069405363822277 : ((p1 ∧ (False → (True → p4))) ∨ (p5 ∨ (((((True → (p5 → (p2 → p3))) → p4) ∧ p2) ∧ (p5 ∨ False)) ∨ (True ∨ (p3 ∧ (p3 ∨ p1)))))) := by
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



