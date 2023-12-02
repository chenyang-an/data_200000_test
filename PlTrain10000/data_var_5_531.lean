variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_207997182812941282979678259544 : ((((True → True) ∨ p5) ∨ (p5 → p1)) → (((p5 ∧ ((p3 ∧ p5) → p2)) ∧ (p2 ∨ ((p3 ∨ False) → True))) ∨ (False ∨ (p2 → (p4 ∨ p2))))) := by
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
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- One of the premise coincides with the conclusion.
      exact h4
    case inr h5 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Implications on the right can always be decomposed.
      intro h6
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- One of the premise coincides with the conclusion.
      exact h6
  case inr h7 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h8
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h8



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_136210499492892760352789132607 : (((p3 → (((True → p5) ∧ p1) ∧ False)) ∧ ((p2 ∧ ((p1 ∧ p1) ∧ ((((p3 ∧ p2) ∧ p1) ∧ p5) ∨ True))) ∨ False)) ∨ ((p4 ∧ True) → True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_300075808510198755386674826742 : (False ∨ (((((((((p1 ∨ (p1 ∨ p3)) ∧ (p3 ∨ p2)) → p3) ∨ (p5 ∨ True)) ∨ p5) ∧ p5) → (p5 ∨ (False → False))) → p5) ∨ (p5 → True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_493627830454954892058017855178 : (((((p5 ∧ (p2 → p5)) ∧ p1) → ((p5 ∨ (((p2 ∨ p3) ∧ p5) → p5)) → ((((True ∨ p4) → False) ∧ (p5 → p3)) ∨ (p3 ∨ True)))) ∧ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
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
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro
  case inr h8 =>
    -- Conjunctions on the left can always be decomposed.
    let h9 := h1.left
    let h10 := h1.right
    -- Conjunctions on the left can always be decomposed.
    let h11 := h9.left
    let h12 := h9.right
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
theorem thm_5_vars_342405252188669869233852255007 : (p2 → ((p5 ∨ ((p3 ∨ p5) ∧ (((p2 → p1) → p4) → (((p1 → False) ∨ p2) → p5)))) ∨ ((p1 → (p4 ∧ ((True ∧ p2) → True))) ∨ p2))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_187747909325315723512709020932 : ((p2 → ((((p2 ∨ (False ∨ p2)) → p2) → (p1 ∧ p2)) ∨ p5)) → ((p5 → (False ∨ ((p3 ∧ p4) → False))) ∨ ((True ∨ p1) ∨ (p2 ∧ p1)))) := by
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
theorem thm_5_vars_244847207378780081290109192090 : ((p1 ∧ p1) ∨ (p3 → ((((True → (True ∧ (p1 ∨ ((True ∧ p2) ∨ False)))) ∧ True) ∨ ((p2 → (p5 ∨ (p2 → (p4 ∧ True)))) → True)) ∨ p1))) := by
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
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_137831441166799859784315434834 : ((p3 ∨ (((((p4 ∧ (p2 → p5)) ∨ p2) → p1) ∨ (((p5 ∧ True) ∨ p2) ∧ ((p3 → p3) ∧ p1))) → (p2 → p5))) ∨ (p4 ∨ (False → p3))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_266241248736343277402991174609 : (True ∧ (p5 → ((((False → p2) → ((True ∨ ((p4 → (p1 → p1)) → p2)) ∧ (((p2 ∧ False) ∨ (p1 ∧ True)) ∧ p3))) ∧ (p4 → False)) ∨ True))) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_480689586714364969132646536277 : (((((p1 → (p5 → (p1 → (p4 ∨ p2)))) → p2) ∨ (((p2 → True) ∧ (((p3 ∧ p2) ∨ ((False → p5) → p4)) ∧ (p5 ∨ p5))) → p5)) ∧ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
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
  -- Disjunctions on the left can always be decomposed.
  cases h4
  case inl h6 =>
    -- Conjunctions on the left can always be decomposed.
    let h7 := h6.left
    let h8 := h6.right
    -- Disjunctions on the left can always be decomposed.
    cases h5
    case inl h9 =>
      -- One of the premise coincides with the conclusion.
      exact h9
    case inr h10 =>
      -- One of the premise coincides with the conclusion.
      exact h10
  case inr h11 =>
    -- Disjunctions on the left can always be decomposed.
    cases h5
    case inl h12 =>
      -- One of the premise coincides with the conclusion.
      exact h12
    case inr h13 =>
      -- One of the premise coincides with the conclusion.
      exact h13
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_321317708574682823385758806947 : (p4 ∨ (p5 ∨ ((((p3 ∨ p5) → (True ∨ p2)) → (False ∧ False)) ∨ ((((True ∨ p3) ∨ p4) ∧ (((p2 ∧ p4) ∧ p3) ∧ p5)) ∨ (p5 → p5))))) := by
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
theorem thm_5_vars_198370962287032305671822181728 : ((p3 ∧ (((p5 ∨ p1) ∨ (False ∨ False)) ∨ p2)) ∨ (((p3 ∨ ((p3 ∧ True) → p1)) → ((p3 ∧ p3) ∨ p5)) ∨ (p5 → (p1 → (p5 ∨ p5))))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_133625825909089113878725158082 : (((((p4 → p1) ∧ ((((p5 ∧ False) → p4) ∨ (p2 ∨ p4)) → (((p4 ∧ True) → (p4 ∨ p2)) ∨ p4))) → p4) ∧ True) ∨ ((p3 ∧ p1) → True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_149805265163764907282169714825 : ((False ∨ (p2 ∨ (((((p5 ∨ p5) → p4) ∨ p3) ∧ p5) → (((p2 → (p3 ∧ p4)) ∨ p3) ∨ (p5 ∨ p1))))) ∨ (p4 ∧ (True ∧ (p3 → p1)))) := by
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
  -- Disjunctions on the left can always be decomposed.
  cases h2
  case inl h4 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- One of the premise coincides with the conclusion.
    exact h3
  case inr h5 =>
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h5



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_138514122202946199105316084930 : (((((((p5 ∧ (p3 ∧ (((p2 ∨ True) ∧ (True → p2)) ∧ p1))) ∧ ((p4 ∧ True) ∨ True)) → p5) ∧ p3) ∨ p1) ∧ p5) → ((True → False) → p2)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Conjunctions on the left can always be decomposed.
  let h3 := h1.left
  let h4 := h1.right
  -- Disjunctions on the left can always be decomposed.
  cases h3
  case inl h5 =>
    -- Conjunctions on the left can always be decomposed.
    let h6 := h5.left
    let h7 := h5.right
    -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
    have h8 : True := by
      -- True on the right can always be proven directly.
      apply True.intro
    -- We have shown the premise of h2, we can now drive its conclusion.
    let h9 := h2 h8
    -- False on the left can always be used.
    apply False.elim h9
  case inr h10 =>
    -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
    have h11 : True := by
      -- True on the right can always be proven directly.
      apply True.intro
    -- We have shown the premise of h2, we can now drive its conclusion.
    let h12 := h2 h11
    -- False on the left can always be used.
    apply False.elim h12



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_381005346832304545349579574119 : (((((False ∧ (((p2 ∨ ((p2 ∨ (((p2 ∧ p3) ∨ p1) → p5)) ∨ (((p3 → (p4 ∧ p4)) ∧ p1) → p4))) ∧ p1) → p2)) ∧ True) ∨ True) ∧ True) ∧ True) := by
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
theorem thm_5_vars_60347827190875930547736904513 : (((p2 → p3) → (((True ∨ (p1 ∨ ((False ∧ (p1 ∨ p2)) → p3))) ∧ p4) ∨ (((p5 → (False ∨ False)) → ((p5 ∧ True) ∧ p5)) ∧ p2))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_147860452529908440212896713044 : (((p1 → (((False → p1) ∧ ((p1 → ((p5 ∧ ((p3 → p4) → p2)) ∨ (p4 → p2))) ∧ p4)) ∨ p2)) → p4) ∨ ((False ∧ p5) → (p2 ∧ False))) := by
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
  apply False.elim h2
  -- Conjunctions on the left can always be decomposed.
  let h4 := h1.left
  let h5 := h1.right
  -- False on the left can always be used.
  apply False.elim h4



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_322567000181275358103950890348 : (p5 ∨ ((p3 ∨ (((True → ((((p1 ∨ p4) → p2) ∧ (p3 ∧ p4)) ∨ (False ∧ ((p1 ∨ p5) → p1)))) ∨ (p2 → p2)) ∨ (True ∧ False))) ∨ p1)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
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
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_241528239724091336818718809510 : ((False → p3) ∧ (((p1 ∨ (p1 ∨ (p2 ∨ (((False ∧ False) → ((p5 ∧ False) ∧ ((p1 → p3) → p5))) ∨ (p4 ∨ True))))) → False) ∨ (True ∨ p1))) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h1
  -- False on the left can always be used.
  apply False.elim h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_60308012908626074991151348555 : (((p1 → p3) → (((p3 → (((False ∨ p2) ∧ (True ∨ (False ∧ (p5 → p3)))) ∧ (False ∧ p5))) ∧ True) ∨ ((False → p5) ∨ (p5 → True)))) ∨ False) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
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



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_153402898802693513444469158955 : ((p3 ∨ (((p5 ∨ False) ∨ (p4 ∧ True)) ∧ ((p2 ∧ ((True → (False ∧ p5)) ∧ p5)) ∧ (p5 ∨ (p1 ∨ True))))) → (p5 → ((p2 → p4) → p3))) := by
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
    exact h4
  case inr h5 =>
    -- Conjunctions on the left can always be decomposed.
    let h6 := h5.left
    let h7 := h5.right
    -- Disjunctions on the left can always be decomposed.
    cases h6
    case inl h8 =>
      -- Disjunctions on the left can always be decomposed.
      cases h8
      case inl h9 =>
        -- Conjunctions on the left can always be decomposed.
        let h10 := h7.left
        let h11 := h7.right
        -- Conjunctions on the left can always be decomposed.
        let h12 := h10.left
        let h13 := h10.right
        -- Conjunctions on the left can always be decomposed.
        let h14 := h13.left
        let h15 := h13.right
        -- Disjunctions on the left can always be decomposed.
        cases h11
        case inl h16 =>
          -- We want to use the implication h14 based on <expert-advice>. So we show its premise.
          have h17 : True := by
            -- True on the right can always be proven directly.
            apply True.intro
          -- We have shown the premise of h14, we can now drive its conclusion.
          let h18 := h14 h17
          -- We need to get the left conjuct of h18 based on <expert-advice>.
          let h19 := h18.left
          -- False on the left can always be used.
          apply False.elim h19
        case inr h20 =>
          -- Disjunctions on the left can always be decomposed.
          cases h20
          case inl h21 =>
            -- We want to use the implication h14 based on <expert-advice>. So we show its premise.
            have h22 : True := by
              -- True on the right can always be proven directly.
              apply True.intro
            -- We have shown the premise of h14, we can now drive its conclusion.
            let h23 := h14 h22
            -- We need to get the left conjuct of h23 based on <expert-advice>.
            let h24 := h23.left
            -- False on the left can always be used.
            apply False.elim h24
          case inr h25 =>
            -- We want to use the implication h14 based on <expert-advice>. So we show its premise.
            have h26 : True := by
              -- True on the right can always be proven directly.
              apply True.intro
            -- We have shown the premise of h14, we can now drive its conclusion.
            let h27 := h14 h26
            -- We need to get the left conjuct of h27 based on <expert-advice>.
            let h28 := h27.left
            -- False on the left can always be used.
            apply False.elim h28
      case inr h29 =>
        -- False on the left can always be used.
        apply False.elim h29
    case inr h30 =>
      -- Conjunctions on the left can always be decomposed.
      let h31 := h30.left
      let h32 := h30.right
      -- Conjunctions on the left can always be decomposed.
      let h33 := h7.left
      let h34 := h7.right
      -- Conjunctions on the left can always be decomposed.
      let h35 := h33.left
      let h36 := h33.right
      -- Conjunctions on the left can always be decomposed.
      let h37 := h36.left
      let h38 := h36.right
      -- Disjunctions on the left can always be decomposed.
      cases h34
      case inl h39 =>
        -- We want to use the implication h37 based on <expert-advice>. So we show its premise.
        have h40 : True := by
          -- True on the right can always be proven directly.
          apply True.intro
        -- We have shown the premise of h37, we can now drive its conclusion.
        let h41 := h37 h40
        -- We need to get the left conjuct of h41 based on <expert-advice>.
        let h42 := h41.left
        -- False on the left can always be used.
        apply False.elim h42
      case inr h43 =>
        -- Disjunctions on the left can always be decomposed.
        cases h43
        case inl h44 =>
          -- We want to use the implication h37 based on <expert-advice>. So we show its premise.
          have h45 : True := by
            -- True on the right can always be proven directly.
            apply True.intro
          -- We have shown the premise of h37, we can now drive its conclusion.
          let h46 := h37 h45
          -- We need to get the left conjuct of h46 based on <expert-advice>.
          let h47 := h46.left
          -- False on the left can always be used.
          apply False.elim h47
        case inr h48 =>
          -- We want to use the implication h37 based on <expert-advice>. So we show its premise.
          have h49 : True := by
            -- True on the right can always be proven directly.
            apply True.intro
          -- We have shown the premise of h37, we can now drive its conclusion.
          let h50 := h37 h49
          -- We need to get the left conjuct of h50 based on <expert-advice>.
          let h51 := h50.left
          -- False on the left can always be used.
          apply False.elim h51



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_40854696846204434049935620759 : (((((p4 ∨ ((p1 ∧ ((((p5 ∨ (True → p4)) ∨ p3) ∧ p1) ∨ p2)) ∨ (p5 ∨ ((p1 → p3) → p1)))) ∧ p2) ∧ (p4 ∨ True)) ∨ p2) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_47984776117915863313384821370 : (((((p1 ∧ False) → (p4 ∨ (((p3 ∨ p2) ∧ (p1 ∧ ((p2 ∨ False) ∨ p5))) ∨ True))) → ((False → p1) ∧ (p3 ∧ p3))) → (p5 ∧ p5)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_113703455440665790666131346741 : ((((p4 → ((p2 → ((p3 → p2) → ((p4 ∨ (p3 ∨ p3)) → (False ∨ (p2 ∧ p4))))) ∨ (p5 → True))) → False) → (p1 ∧ p5)) ∨ (p2 ∧ True)) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h2 : (p4 → ((p2 → ((p3 → p2) → ((p4 ∨ (p3 ∨ p3)) → (False ∨ (p2 ∧ p4))))) ∨ (p5 → True))) := by
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
  -- False on the left can always be used.
  apply False.elim h5
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h6 : (p4 → ((p2 → ((p3 → p2) → ((p4 ∨ (p3 ∨ p3)) → (False ∨ (p2 ∧ p4))))) ∨ (p5 → True))) := by
    -- Implications on the right can always be decomposed.
    intro h7
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h8
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h9 := h1 h6
  -- False on the left can always be used.
  apply False.elim h9



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_350115257330963251973561614997 : (p4 → ((((p5 ∨ (p2 → ((p3 → p1) → (p3 → (p4 → (p3 ∧ p3)))))) → (p1 → (p2 → True))) → (False ∧ (True → (False → False)))) ∨ True)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_3415580262683895637867988261 : (True ∧ (((((((p4 → p3) → p4) ∨ ((p3 → False) ∨ (((p2 → p4) ∨ (False → p2)) ∨ p2))) ∨ p1) ∨ (p1 → p3)) ∨ p2) ∨ p4)) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
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
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_138346575744285539487346661270 : ((p4 → ((((p5 ∧ ((True → p5) ∨ p3)) ∨ (p5 ∨ p2)) ∧ ((p3 → False) → (p2 ∧ (False ∨ (p1 → p1))))) ∨ True)) ∨ (p2 → (p1 ∨ False))) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_180887261398369098019530240742 : ((((p4 ∨ p1) ∨ False) → ((p5 → False) → (False ∨ ((p4 → p4) ∨ p2)))) → ((False ∧ (p4 ∧ (p1 ∧ p3))) ∨ (p4 → ((p4 → p3) → p3)))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h2
  -- Implications on the right can always be decomposed.
  intro h3
  -- We want to use the implication h3 based on <expert-advice>. So we show its premise.
  have h4 : p4 := by
    -- One of the premise coincides with the conclusion.
    exact h2
  -- We have shown the premise of h3, we can now drive its conclusion.
  let h5 := h3 h4
  -- One of the premise coincides with the conclusion.
  exact h5



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_200709350219295420076684664396 : ((p2 ∧ (p4 ∧ (p5 ∨ (p1 ∧ (p2 ∧ p1))))) → ((False ∨ ((p3 ∧ p1) ∨ (p5 ∧ False))) ∨ (((True → p2) ∨ ((p5 ∨ p4) → p3)) ∨ p2))) := by
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
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h2
  case inr h7 =>
    -- Conjunctions on the left can always be decomposed.
    let h8 := h7.left
    let h9 := h7.right
    -- Conjunctions on the left can always be decomposed.
    let h10 := h9.left
    let h11 := h9.right
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h10



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_175065262730805385187190191184 : ((p2 ∧ (p2 → ((((p3 ∨ False) ∨ True) → p3) ∨ ((p1 ∧ p3) ∧ (p4 ∧ p1))))) → (p3 ∧ (True ∧ ((False ∧ (p4 → p4)) ∨ (p5 ∨ p3))))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- We want to use the implication h3 based on <expert-advice>. So we show its premise.
  have h4 : p2 := by
    -- One of the premise coincides with the conclusion.
    exact h2
  -- We have shown the premise of h3, we can now drive its conclusion.
  let h5 := h3 h4
  -- Disjunctions on the left can always be decomposed.
  cases h5
  case inl h6 =>
    -- We want to use the implication h6 based on <expert-advice>. So we show its premise.
    have h7 : ((p3 ∨ False) ∨ True) := by
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- True on the right can always be proven directly.
      apply True.intro
    -- We have shown the premise of h6, we can now drive its conclusion.
    let h8 := h6 h7
    -- One of the premise coincides with the conclusion.
    exact h8
  case inr h9 =>
    -- Conjunctions on the left can always be decomposed.
    let h10 := h9.left
    let h11 := h9.right
    -- Conjunctions on the left can always be decomposed.
    let h12 := h10.left
    let h13 := h10.right
    -- Conjunctions on the left can always be decomposed.
    let h14 := h11.left
    let h15 := h11.right
    -- One of the premise coincides with the conclusion.
    exact h13
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- Conjunctions on the left can always be decomposed.
  let h16 := h1.left
  let h17 := h1.right
  -- We want to use the implication h17 based on <expert-advice>. So we show its premise.
  have h18 : p2 := by
    -- One of the premise coincides with the conclusion.
    exact h16
  -- We have shown the premise of h17, we can now drive its conclusion.
  let h19 := h17 h18
  -- Disjunctions on the left can always be decomposed.
  cases h19
  case inl h20 =>
    -- We want to use the implication h20 based on <expert-advice>. So we show its premise.
    have h21 : ((p3 ∨ False) ∨ True) := by
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- True on the right can always be proven directly.
      apply True.intro
    -- We have shown the premise of h20, we can now drive its conclusion.
    let h22 := h20 h21
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h22
  case inr h23 =>
    -- Conjunctions on the left can always be decomposed.
    let h24 := h23.left
    let h25 := h23.right
    -- Conjunctions on the left can always be decomposed.
    let h26 := h24.left
    let h27 := h24.right
    -- Conjunctions on the left can always be decomposed.
    let h28 := h25.left
    let h29 := h25.right
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h27



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_304701337219191219936748478422 : (p1 ∨ ((((p2 → (p1 → p4)) ∨ (p5 ∨ (((False ∧ (((p1 → p5) ∨ ((p5 ∨ True) ∧ p4)) → p3)) ∧ p4) ∨ p4))) → p1) ∨ (False → True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_357086153237140080279679663528 : (p5 → (((True ∨ p5) → p5) → (True → (((p2 → p5) → ((p2 → (True ∧ p1)) → ((p1 ∧ True) ∨ (True ∨ p4)))) ∨ ((False ∧ p3) → p3))))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Implications on the right can always be decomposed.
  intro h3
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h4
  -- Conjunctions on the left can always be decomposed.
  let h5 := h4.left
  let h6 := h4.right
  -- False on the left can always be used.
  apply False.elim h5



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_48948864282132430131479020981 : ((((p2 ∧ (((False ∧ ((p4 ∧ ((True ∨ (((p4 → p5) → p4) ∧ True)) → p4)) ∨ True)) ∧ p2) ∨ p5)) ∧ p5) ∨ ((p4 ∨ p5) ∨ True)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_41880063581608727525276445670 : ((((p4 ∧ (p3 → True)) ∨ (p3 → (((((p4 → False) ∨ ((p3 ∨ True) → ((p3 → (True → True)) → p2))) → p1) → p2) ∨ p3))) ∨ False) ∨ p2) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
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



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_213262218822521126275983012814 : ((((p2 ∨ p5) → p4) ∧ False) ∨ (p3 → ((p3 ∧ ((p3 ∧ p2) → True)) → (((((p2 → (p4 ∧ (p2 ∨ False))) → p4) ∧ p3) ∨ True) ∨ p3)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Conjunctions on the left can always be decomposed.
  let h3 := h2.left
  let h4 := h2.right
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_135093658672321908396165633949 : (((((p3 ∨ True) ∧ ((True ∨ (p1 ∧ p4)) ∧ False)) ∧ (p1 → ((((p1 → False) ∨ p1) ∧ True) → p1))) ∨ (p1 ∧ p3)) ∨ ((p2 → False) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_184083016196451746698374592471 : (((((p1 ∧ p3) ∧ p2) ∧ (p3 ∨ (p1 ∧ (p4 ∨ p1)))) ∨ p2) ∨ ((((((p3 → p4) ∧ p5) → p5) ∨ p1) ∨ ((True ∧ p4) ∨ p3)) ∨ p5)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- One of the premise coincides with the conclusion.
  exact h3



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_601180103073762063279062891081 : ((((p2 ∧ ((p2 → (((p5 ∨ ((True ∨ ((False → (p3 ∨ p3)) ∨ False)) → p3)) ∧ False) ∧ (p5 → (True ∧ (p3 → p2))))) ∧ p4)) ∧ p1) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_311212028173750556389860539515 : (p2 ∨ ((True → False) → (p2 → (((p2 ∨ ((p1 ∨ (False ∧ p3)) → (False ∨ (((p4 ∧ p1) ∨ ((p4 → p4) ∧ p2)) ∨ p4)))) → p4) ∨ p4)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h3 : True := by
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h4 := h1 h3
  -- False on the left can always be used.
  apply False.elim h4



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_114360547645435131528307494896 : (((((p1 ∨ (p4 ∧ ((p4 ∧ p3) → p5))) → ((False ∨ (p5 ∨ p2)) ∧ (p2 ∨ p1))) ∧ p4) ∨ (p4 → (False ∧ (p3 ∧ p1)))) ∨ (False → p3)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_171800879594274198502170891421 : ((((((p3 → p1) ∨ p4) ∨ ((p4 ∨ p2) ∧ False)) ∨ ((p1 ∨ False) → False)) → p4) ∨ ((p3 → p3) → (((p2 ∨ (p4 → True)) ∨ p2) ∨ p4))) := by
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
  -- Implications on the right can always be decomposed.
  intro h2
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_308515601072398858074523234737 : (p2 ∨ (((((True ∧ (True ∨ p3)) ∧ (p2 ∨ (p4 ∧ p2))) ∧ ((True ∧ p2) ∨ (p2 ∧ p4))) ∨ ((True → False) → (p4 → (p4 → p1)))) ∨ p4)) := by
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
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h4 : True := by
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h5 := h1 h4
  -- False on the left can always be used.
  apply False.elim h5



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_60402572680422575765682601235 : (((p4 → True) → (((((((p3 → p3) → p5) ∧ p5) ∧ (False ∨ True)) ∧ p5) → ((True ∨ (p2 ∨ True)) → ((p1 ∧ False) ∨ p1))) → p4)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_136858212649560209284715659512 : (((p5 ∧ False) ∨ (p5 ∧ (((((((p5 ∨ p4) ∨ (p5 ∧ p3)) → (p3 ∨ p3)) ∨ p5) → p1) ∧ p5) ∨ (p2 ∧ False)))) ∨ ((p3 ∧ p3) → True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_977224778364860327905839206173 : (((True ∧ (((True → p3) ∧ (p5 ∨ (p3 → (((True ∨ p3) ∨ (True → p1)) ∧ p5)))) ∧ ((p2 → (p4 → (p5 ∨ (True ∨ False)))) ∨ True))) → p3) ∧ True) := by
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
  -- Conjunctions on the left can always be decomposed.
  let h6 := h4.left
  let h7 := h4.right
  -- Disjunctions on the left can always be decomposed.
  cases h7
  case inl h8 =>
    -- Disjunctions on the left can always be decomposed.
    cases h5
    case inl h9 =>
      -- We want to use the implication h6 based on <expert-advice>. So we show its premise.
      have h10 : True := by
        -- True on the right can always be proven directly.
        apply True.intro
      -- We have shown the premise of h6, we can now drive its conclusion.
      let h11 := h6 h10
      -- One of the premise coincides with the conclusion.
      exact h11
    case inr h12 =>
      -- We want to use the implication h6 based on <expert-advice>. So we show its premise.
      have h13 : True := by
        -- True on the right can always be proven directly.
        apply True.intro
      -- We have shown the premise of h6, we can now drive its conclusion.
      let h14 := h6 h13
      -- One of the premise coincides with the conclusion.
      exact h14
  case inr h15 =>
    -- Disjunctions on the left can always be decomposed.
    cases h5
    case inl h16 =>
      -- We want to use the implication h6 based on <expert-advice>. So we show its premise.
      have h17 : True := by
        -- True on the right can always be proven directly.
        apply True.intro
      -- We have shown the premise of h6, we can now drive its conclusion.
      let h18 := h6 h17
      -- One of the premise coincides with the conclusion.
      exact h18
    case inr h19 =>
      -- We want to use the implication h6 based on <expert-advice>. So we show its premise.
      have h20 : True := by
        -- True on the right can always be proven directly.
        apply True.intro
      -- We have shown the premise of h6, we can now drive its conclusion.
      let h21 := h6 h20
      -- One of the premise coincides with the conclusion.
      exact h21
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_177724632162179665709845379447 : ((((p1 → ((p3 → p4) ∨ p2)) ∧ ((p2 ∧ (p2 ∧ p2)) ∨ p2)) ∧ False) ∨ (True ∨ ((False ∧ p4) → ((((p3 ∨ p4) ∨ False) ∨ p3) → p3)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_351808567094297157259356545156 : (p4 → (((p1 ∧ ((((p3 → p2) → True) → (p2 ∧ p2)) ∨ p1)) ∧ p5) ∨ ((((p4 → (p2 → True)) → (p4 → False)) ∨ (False ∨ p1)) ∨ True))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_636559770823737278950100089309 : ((((((False → p4) → (p1 → (p2 ∨ ((((False → p3) ∨ p3) ∨ p3) ∧ p2)))) ∧ ((p5 ∧ False) ∨ ((p2 ∧ (p5 → p5)) → p2))) → False) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_654371087774589425288891421005 : ((((((True ∨ (p2 → ((p1 ∨ p1) → ((p4 ∧ p1) → p4)))) → (p4 → (p5 ∨ (p4 → ((p1 ∨ p1) ∨ p5))))) ∨ p5) ∨ (False → p3)) ∨ p2) ∧ True) := by
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
theorem thm_5_vars_475681455781537850294384073874 : ((((((((True ∧ p5) ∧ p5) ∧ (p4 ∧ True)) → p4) ∧ p3) ∨ ((((False → False) → ((p3 → (p2 ∧ p4)) ∨ p1)) → p5) ∨ (p1 ∨ True))) ∧ True) ∧ True) := by
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
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_200553984298327895823788998311 : (((p2 → p2) → (p1 ∧ ((True → False) ∧ False))) → ((True ∧ ((p5 → (p5 → ((p4 ∧ (p1 ∧ (p2 ∨ False))) → p3))) → p3)) ∨ (p5 → p2))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h2 : (p2 → p2) := by
    -- Implications on the right can always be decomposed.
    intro h3
    -- One of the premise coincides with the conclusion.
    exact h3
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h4 := h1 h2
  -- We need to get the right conjuct of h4 based on <expert-advice>.
  let h5 := h4.right
  -- We need to get the right conjuct of h5 based on <expert-advice>.
  let h6 := h5.right
  -- False on the left can always be used.
  apply False.elim h6



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_41311227903057583741914523957 : (((((False → (False → (p4 → (((p4 → p3) ∧ False) ∧ ((p3 ∨ p2) ∨ p4))))) → p4) ∧ (True ∧ (p3 → (False → (True ∧ False))))) ∨ p1) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_746510336312498520565496867537 : ((((p2 ∨ p4) → (((False ∨ p3) → ((True ∨ (p3 ∧ p3)) ∨ False)) → (((True ∧ ((True → p3) ∨ p1)) ∧ (p5 → False)) ∧ (True ∨ p5)))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_651866291744683111926909676254 : (((((p2 ∨ p3) → (((((((False → p4) ∧ p4) → p3) → p2) ∧ p1) → ((True ∧ p5) → (p4 ∨ (p2 ∨ p4)))) → p5)) ∧ (p1 ∨ p1)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_66363689489095586729761169536 : ((p5 ∨ (False ∨ (p1 → ((p1 ∧ ((p5 → p1) ∨ p2)) → ((False ∧ False) ∨ (((p2 ∨ (((p4 ∨ p5) ∨ p1) ∧ p3)) ∧ p5) ∨ True)))))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_341091807929425813320082763982 : (p2 → ((p2 → ((((p5 ∧ (p4 → p2)) ∧ ((((True → p2) → (p4 ∨ p1)) ∧ p3) ∨ (((p3 ∨ p5) ∧ p3) ∨ False))) → p1) ∨ p1)) ∨ p2)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_356739109441668801259162077434 : (p5 → ((p2 ∧ (p3 ∧ ((p4 ∨ p1) ∨ p4))) ∨ (False → ((p5 ∨ p4) ∧ ((p2 ∧ (p5 ∧ (((p2 → True) → p2) ∧ p2))) ∨ (p1 ∧ p1)))))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h2
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- False on the left can always be used.
  apply False.elim h2
  -- False on the left can always be used.
  apply False.elim h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_351650046321509095321154691392 : (p4 → ((p2 ∨ (p3 ∧ (((True → p4) ∨ p3) ∧ ((p3 ∧ True) ∨ (p1 → (p3 ∨ False)))))) ∨ ((p3 ∨ ((p4 ∨ (p1 → p2)) ∨ False)) ∨ p1))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_43519012091382284168284161379 : ((((p4 ∨ (p4 → ((p5 → (((False → p1) → ((p2 ∨ p2) → ((False ∨ p1) → (p1 ∨ (p3 ∨ p4))))) ∧ p2)) ∧ p2))) ∨ True) → p4) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_208219988334358250521039839938 : (((p5 → (p4 ∧ False)) → (True ∨ True)) → ((True → ((p1 ∨ p1) ∧ ((((p3 ∨ False) → (p2 ∨ (True ∨ p5))) ∨ p5) → p2))) ∨ (p5 ∨ True))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_747726870212309606545536619093 : ((((False → False) → (((p2 ∧ (((((p4 ∨ p2) → False) → False) → (p1 → p5)) ∨ True)) → p2) ∧ ((p5 ∧ (p5 ∧ (p3 ∧ p5))) → p1))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_779600151406462529011356591033 : (((p2 ∨ ((p4 ∨ (((p4 ∧ True) ∧ (False ∨ (p4 ∨ ((False → ((True ∨ (p2 ∧ p3)) ∧ (p5 ∧ p3))) → True)))) ∨ (False → True))) ∨ p1)) ∨ p2) ∧ True) := by
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
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_112207232728964151053150110081 : (((False ∨ ((((p2 → p1) → (p2 ∨ (p1 → ((True ∨ p1) → ((p1 ∨ p3) ∨ p5))))) → (p5 → (p2 ∧ p3))) ∨ False)) ∨ True) ∨ (p3 → True)) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_264301462389740709384481772109 : (True ∧ (((False ∨ ((p5 → p1) → p1)) → False) → ((((True → ((p5 → p1) ∧ p5)) ∨ p1) ∨ True) ∨ ((False ∨ ((p1 → p5) ∧ p2)) → p3)))) := by
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
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_47793639863858672743053666390 : (((((p4 ∧ (((p4 ∨ (p1 ∧ False)) → (((((p4 ∨ p5) ∧ p2) ∧ p3) ∧ p1) ∨ (False ∧ p4))) ∧ p4)) ∨ p5) → p3) → (p2 ∧ p1)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_55299739911883987524601443392 : (((p4 ∧ ((False ∨ p3) ∨ (p1 ∨ p2))) ∨ ((p2 ∨ (p5 ∨ (((p5 ∨ True) ∨ p2) ∨ (((p1 → (p4 ∨ p1)) ∨ p5) ∧ p4)))) ∨ True)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_38162092686754346584244904941 : (((((True ∧ ((True ∨ (p1 → (p4 ∨ p3))) → (p5 → ((True → p3) → (False ∧ p1))))) ∨ (p4 → p1)) ∨ ((True ∧ p5) ∧ False)) ∧ p5) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_190718015090878690848275430089 : (((((p1 ∧ p3) ∧ False) ∨ (p1 ∨ False)) ∧ (False ∧ p4)) ∨ (p3 → (((False → True) ∨ p1) ∨ ((p5 → (((True ∧ False) → p1) → p4)) → p4)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h2
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_308985951776913178035693841623 : (p2 ∨ (((p2 ∧ ((p3 ∨ p4) ∨ (p2 ∨ p1))) ∧ ((((True → ((p1 ∨ (True → p5)) ∨ (False ∧ False))) ∨ (p2 ∧ p5)) ∨ p2) → False)) → p3)) := by
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
  -- Disjunctions on the left can always be decomposed.
  cases h5
  case inl h6 =>
    -- Disjunctions on the left can always be decomposed.
    cases h6
    case inl h7 =>
      -- One of the premise coincides with the conclusion.
      exact h7
    case inr h8 =>
      -- We want to use the implication h3 based on <expert-advice>. So we show its premise.
      have h9 : (((True → ((p1 ∨ (True → p5)) ∨ (False ∧ False))) ∨ (p2 ∧ p5)) ∨ p2) := by
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- One of the premise coincides with the conclusion.
        exact h4
      -- We have shown the premise of h3, we can now drive its conclusion.
      let h10 := h3 h9
      -- False on the left can always be used.
      apply False.elim h10
  case inr h11 =>
    -- Disjunctions on the left can always be decomposed.
    cases h11
    case inl h12 =>
      -- We want to use the implication h3 based on <expert-advice>. So we show its premise.
      have h13 : (((True → ((p1 ∨ (True → p5)) ∨ (False ∧ False))) ∨ (p2 ∧ p5)) ∨ p2) := by
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- One of the premise coincides with the conclusion.
        exact h12
      -- We have shown the premise of h3, we can now drive its conclusion.
      let h14 := h3 h13
      -- False on the left can always be used.
      apply False.elim h14
    case inr h15 =>
      -- We want to use the implication h3 based on <expert-advice>. So we show its premise.
      have h16 : (((True → ((p1 ∨ (True → p5)) ∨ (False ∧ False))) ∨ (p2 ∧ p5)) ∨ p2) := by
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- One of the premise coincides with the conclusion.
        exact h4
      -- We have shown the premise of h3, we can now drive its conclusion.
      let h17 := h3 h16
      -- False on the left can always be used.
      apply False.elim h17



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_189026970536877819939397197749 : (((False ∨ (p1 → p1)) ∨ (((p5 → False) ∧ p3) → p4)) ∧ (((p3 ∧ p2) ∧ (p2 → p5)) ∨ (p5 → ((p2 ∧ ((p2 ∧ False) ∧ p5)) ∨ p5)))) := by
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
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h2
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_323493841626382826488792826742 : (p5 ∨ (((p4 ∧ ((p3 → (p5 → (p3 ∧ (p3 ∧ ((p4 ∨ p4) ∨ (p1 ∧ p1)))))) ∨ p3)) → (p5 ∨ (p2 ∧ p1))) ∨ (True → (p2 → p2)))) := by
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
theorem thm_5_vars_740922294173268419817080978075 : ((((p3 ∨ p2) ∨ (((False → (p2 ∧ p5)) → p5) ∧ (p1 ∧ ((True → (True ∧ False)) ∧ (p5 → (p2 → ((False ∧ True) → (p1 ∧ p1)))))))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_174737524303993175625961963322 : ((((p3 → p1) → p2) → (((p4 → (p3 ∧ (p2 ∨ p1))) → p4) ∨ (p2 ∧ False))) → ((p1 ∧ ((p4 ∧ ((p2 ∧ p4) ∨ p1)) ∧ p2)) → p2)) := by
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
  -- Conjunctions on the left can always be decomposed.
  let h7 := h5.left
  let h8 := h5.right
  -- Disjunctions on the left can always be decomposed.
  cases h8
  case inl h9 =>
    -- Conjunctions on the left can always be decomposed.
    let h10 := h9.left
    let h11 := h9.right
    -- One of the premise coincides with the conclusion.
    exact h6
  case inr h12 =>
    -- One of the premise coincides with the conclusion.
    exact h6



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_345343107922842933237511680668 : (p3 → (((p5 ∧ (((p5 ∧ p4) ∧ (((((p5 → p5) ∨ (p1 → (True → p4))) ∧ (p5 → p4)) ∧ (p4 ∧ True)) → True)) ∧ False)) ∧ p2) ∨ p3)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_67975098618429679605985343340 : ((p2 → (((p3 ∨ True) ∧ p3) → (((True ∧ p4) ∧ (True → p5)) → (True ∧ (p5 → (((False → True) → (p1 ∧ (p3 → p3))) ∨ True)))))) ∨ p3) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Implications on the right can always be decomposed.
  intro h3
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- Implications on the right can always be decomposed.
  intro h4
  -- Conjunctions on the left can always be decomposed.
  let h5 := h3.left
  let h6 := h3.right
  -- Conjunctions on the left can always be decomposed.
  let h7 := h5.left
  let h8 := h5.right
  -- Conjunctions on the left can always be decomposed.
  let h9 := h2.left
  let h10 := h2.right
  -- Disjunctions on the left can always be decomposed.
  cases h9
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



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_345559972989983482074430823151 : (p3 → ((((p1 → p3) ∧ (True → p5)) ∨ (((((p3 ∧ (p3 → (p1 → p3))) ∧ p2) → (p5 → (p1 ∧ True))) ∨ (p1 ∨ p3)) ∨ p1)) ∨ p1)) := by
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
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_657655459502381484645304970089 : (((((p3 ∨ True) → (((((((True ∧ True) → ((True ∧ p4) ∧ p5)) → p1) ∧ (False ∨ (p2 ∨ p3))) ∨ False) ∨ False) ∨ True)) ∨ (p4 ∧ p5)) ∨ p3) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
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
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_301965714339840426854868612536 : (False ∨ ((True → False) → ((p5 ∧ p1) ∨ (((p4 → ((p4 ∨ ((((False ∨ p2) ∧ True) ∨ (True ∨ p4)) → True)) → p5)) → True) ∧ (p4 ∧ p1))))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
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
theorem thm_5_vars_262348907362553075913174712134 : (True ∧ (((((p5 ∨ p4) ∨ p3) → True) → (False ∧ ((True ∨ (((p5 ∧ ((p1 ∧ False) ∨ (p2 → p4))) ∧ p3) ∧ False)) ∨ (p2 ∧ p4)))) ∨ True)) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_165701504767162960787180968909 : (((((True → True) ∨ p2) ∧ p1) ∧ (((p4 ∧ ((p5 ∧ (p4 ∧ p3)) → p5)) ∨ p1) ∨ False)) ∨ ((p2 → p4) ∨ (((p4 ∧ False) → p2) ∧ True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
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
theorem thm_5_vars_50458046298149310801570338912 : (((p4 ∨ ((((p1 ∨ (p4 ∧ p2)) ∧ p5) ∨ p5) → (((p1 ∧ p2) ∨ (True ∧ p1)) ∨ (False ∨ True)))) ∨ (p2 ∨ (p1 → (p2 → p5)))) ∨ p1) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
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
    -- Disjunctions on the left can always be decomposed.
    cases h3
    case inl h5 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
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
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- True on the right can always be proven directly.
      apply True.intro
  case inr h9 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_314546272522975293531496468272 : (p3 ∨ ((((p2 ∨ (p2 ∧ p3)) ∧ (((p1 ∧ True) ∨ p2) → (p5 ∨ p1))) → (p1 → (p3 ∧ p3))) ∨ ((p2 ∨ (p2 ∧ (p2 → True))) → p2))) := by
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
    -- Conjunctions on the left can always be decomposed.
    let h4 := h3.left
    let h5 := h3.right
    -- One of the premise coincides with the conclusion.
    exact h4



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_263704760798049982847579993661 : (True ∧ ((p1 ∧ ((p1 ∨ (((p2 → (p2 ∧ (p3 ∧ False))) ∨ (p4 → p3)) ∧ (p4 ∨ True))) ∧ p1)) ∨ (False ∨ (p2 → ((p2 → True) → True))))) := by
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
  -- Implications on the right can always be decomposed.
  intro h2
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_261361430364798758145701253735 : ((p5 → False) → (p4 ∨ (p1 ∨ (((False ∧ ((p3 ∨ p1) ∨ True)) ∨ (((p2 ∨ p5) → p5) ∧ p5)) → (((p4 ∨ (p3 ∨ True)) → p2) ∨ p2))))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h2
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
    -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
    have h9 : p5 := by
      -- One of the premise coincides with the conclusion.
      exact h8
    -- We have shown the premise of h1, we can now drive its conclusion.
    let h10 := h1 h9
    -- False on the left can always be used.
    apply False.elim h10



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_149361987950518806044290266629 : (((True → p1) → ((p4 ∨ p2) ∨ ((True → p2) ∧ (((True → (p1 → True)) ∨ p1) ∨ (p2 ∧ (p4 ∧ p5)))))) ∨ (p3 → (p2 → (False → False)))) := by
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
theorem thm_5_vars_212427408930716827098709967671 : ((p3 ∨ ((p4 → True) ∨ p4)) ∧ ((((p5 ∧ ((p1 ∧ p1) → ((p5 ∨ ((p5 ∧ p5) → p1)) → False))) ∨ (p2 ∨ True)) ∨ p5) ∨ (False ∨ False))) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro
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
theorem thm_5_vars_134931653096269392487590340647 : (((((p2 → p1) ∧ (p4 → ((((True ∨ (False → p2)) ∧ (p2 ∨ p5)) → p4) → (False ∨ p4)))) → p5) ∧ (False ∧ p5)) ∨ (p2 → (False ∨ p2))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_43817234576321675755511336209 : ((((p4 → (((p1 → (p4 ∧ p2)) ∧ (((((p2 → p1) ∨ (p4 → p4)) → False) ∨ True) ∧ ((False ∨ True) → p5))) ∨ p2)) → p4) → p1) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_336436376065983972360318140777 : (p1 → ((p3 ∨ ((True → (True → ((((True ∧ False) ∨ p5) ∨ False) ∨ (((p4 ∧ True) ∨ p4) → (p5 ∨ (True ∧ p1)))))) → (p2 → p5))) ∨ p1)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_601320595796265453610625402566 : ((((p2 ∧ (((p3 ∧ p4) ∨ True) ∧ ((p3 → (((False → p2) ∨ (True → p1)) ∨ (((p4 → p5) ∨ p4) ∧ True))) → (p4 ∨ p4)))) ∧ False) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_354078412131790923884316560847 : (p4 → (p5 → (((p5 ∧ ((((p1 → (p3 ∨ p3)) ∨ (p4 → (((False ∧ True) ∨ p3) ∨ (p1 ∧ (p2 → p3))))) → False) → p1)) ∨ p5) ∨ p1))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_732187974464855640582640655327 : ((((True ∧ p4) ∧ ((False ∧ p1) ∨ ((p3 ∨ (p4 ∨ ((p3 → (p5 → (p5 ∨ (p3 ∨ (((True → p2) → False) → p2))))) → p1))) ∨ p1))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_323884986193390550068340646643 : (p5 ∨ ((((p4 ∧ ((False → ((True ∨ (p4 ∨ p4)) → p5)) ∧ p2)) ∧ (True → p4)) ∧ p1) ∨ (p2 ∨ ((True ∨ (p2 ∨ (True ∧ p1))) ∨ False)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
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
theorem thm_5_vars_330871536345912199448076600996 : (True → (p3 → ((True → ((p2 → p2) → p2)) → ((p5 ∨ ((p2 → (p3 ∧ p1)) → (p1 ∧ ((p4 ∧ p4) ∨ (p1 ∨ p2))))) ∨ (p2 ∨ p3))))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Implications on the right can always be decomposed.
  intro h3
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_117646477336031726799620332282 : ((p3 ∧ ((p4 ∧ (p3 ∨ (p1 ∧ (((p5 → ((p3 ∧ ((p5 → (p1 ∧ (p5 ∨ p1))) ∨ False)) ∨ p1)) → p5) → False)))) → False)) ∨ (p4 ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_310206246229042223038810894811 : (p2 ∨ ((((p5 ∧ (p5 → ((p1 → False) ∧ True))) → (True → True)) → False) ∨ (p2 → ((p2 ∧ ((((p1 ∧ p2) ∨ p4) ∧ p4) → False)) → True)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_766000921586990360406601042808 : (((p4 ∧ (((p5 ∨ False) ∨ p4) ∧ ((((p2 ∧ True) → ((p1 ∧ p2) ∧ (p2 ∨ p2))) → ((True ∧ (p3 ∨ p4)) → p3)) → (p5 ∨ p5)))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_227680564547409090953948584102 : ((False ∧ (p4 → p5)) ∨ (((((p2 → (False ∨ (p1 ∨ True))) → p2) ∧ p3) ∨ (p3 ∧ (False ∨ False))) → (p2 ∨ ((p4 ∧ False) ∧ (True → False))))) := by
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
    -- We want to use the implication h3 based on <expert-advice>. So we show its premise.
    have h5 : (p2 → (False ∨ (p1 ∨ True))) := by
      -- Implications on the right can always be decomposed.
      intro h6
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- True on the right can always be proven directly.
      apply True.intro
    -- We have shown the premise of h3, we can now drive its conclusion.
    let h7 := h3 h5
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- One of the premise coincides with the conclusion.
    exact h7
  case inr h8 =>
    -- Conjunctions on the left can always be decomposed.
    let h9 := h8.left
    let h10 := h8.right
    -- Disjunctions on the left can always be decomposed.
    cases h10
    case inl h11 =>
      -- False on the left can always be used.
      apply False.elim h11
    case inr h12 =>
      -- False on the left can always be used.
      apply False.elim h12



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_68492175192748843480732057055 : ((p3 → (p1 ∨ (((((p2 ∧ (p4 ∨ p5)) → (p3 → p4)) → (True → p2)) ∨ True) ∧ ((p5 ∨ (((True ∧ False) ∧ p5) ∨ p3)) ∨ p2)))) ∨ p1) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h1



