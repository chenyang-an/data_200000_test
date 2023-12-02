variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_258861580116484382260314104364 : ((True → p1) → (True ∧ (((p4 ∧ ((True ∨ (p1 → ((p3 ∨ p5) ∧ p5))) → p5)) ∧ True) → (((p1 ∧ (True → p4)) ∨ True) → (p5 ∨ False))))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- Implications on the right can always be decomposed.
  intro h2
  -- Implications on the right can always be decomposed.
  intro h3
  -- Disjunctions on the left can always be decomposed.
  cases h3
  case inl h4 =>
    -- Conjunctions on the left can always be decomposed.
    let h5 := h4.left
    let h6 := h4.right
    -- Conjunctions on the left can always be decomposed.
    let h7 := h2.left
    let h8 := h2.right
    -- Conjunctions on the left can always be decomposed.
    let h9 := h7.left
    let h10 := h7.right
    -- We want to use the implication h10 based on <expert-advice>. So we show its premise.
    have h11 : (True ∨ (p1 → ((p3 ∨ p5) ∧ p5))) := by
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- True on the right can always be proven directly.
      apply True.intro
    -- We have shown the premise of h10, we can now drive its conclusion.
    let h12 := h10 h11
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- One of the premise coincides with the conclusion.
    exact h12
  case inr h13 =>
    -- Conjunctions on the left can always be decomposed.
    let h14 := h2.left
    let h15 := h2.right
    -- Conjunctions on the left can always be decomposed.
    let h16 := h14.left
    let h17 := h14.right
    -- We want to use the implication h17 based on <expert-advice>. So we show its premise.
    have h18 : (True ∨ (p1 → ((p3 ∨ p5) ∧ p5))) := by
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- True on the right can always be proven directly.
      apply True.intro
    -- We have shown the premise of h17, we can now drive its conclusion.
    let h19 := h17 h18
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- One of the premise coincides with the conclusion.
    exact h19



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_102665201514647055193572298762 : ((((True → (((((False ∧ (p2 ∧ True)) ∨ p5) ∨ (((p4 ∨ False) ∨ p4) ∨ p2)) ∨ (p4 ∧ (p2 ∧ p2))) ∨ p3)) ∧ p2) ∨ True) ∧ (p1 ∨ True)) := by
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
theorem thm_5_vars_209441998388086834536068759076 : ((p2 → (p4 ∧ (False ∧ (p1 ∨ True)))) → ((p3 ∨ ((((((p4 ∨ (p5 → (p5 → p1))) ∧ (True ∨ p1)) → p5) ∨ True) ∨ p4) ∨ True)) ∨ p2)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_191567918450357431375274310492 : ((p2 ∧ ((((p1 ∨ p4) ∨ (p4 → p1)) ∨ p1) ∨ True)) ∨ (((p5 ∨ p3) ∧ (((((p4 ∨ p1) → True) ∨ p5) ∧ False) ∧ (p5 → True))) → True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_747437275233403278076761285693 : ((((True → False) → ((p4 ∨ (((p5 ∧ ((p4 ∨ (False ∨ (p4 ∧ ((p2 ∧ (p1 → p2)) ∧ p4)))) ∨ (p5 ∧ False))) ∧ p2) → False)) ∧ True)) ∨ p5) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
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
  -- False on the left can always be used.
  apply False.elim h3
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_178682326971360212819127282805 : (((((p4 ∨ p3) ∧ p1) ∧ p1) ∨ (((p1 → (p3 → p2)) → p1) ∨ p3)) ∨ ((p1 ∨ ((False → p5) ∨ ((p1 ∨ p3) → p3))) ∨ (False → p5))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_179053353332178969308514512219 : (((p4 → p2) → (((p1 ∧ (p3 ∧ ((p1 ∨ False) ∨ p1))) ∧ p1) ∨ True)) ∨ (((((p4 ∨ (p3 ∨ p3)) ∨ (p5 ∨ p3)) → p4) ∧ p1) ∧ p3)) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_314659599603713503597441159297 : (p3 ∨ (((p1 → False) ∨ (((True → (True → p2)) ∨ (p4 ∧ (p3 → (True ∧ True)))) ∧ p5)) ∨ (p1 → ((((True ∨ True) ∨ p3) ∧ p4) ∨ p1)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_206184519601912797277249957368 : ((p5 ∧ (p1 ∨ (p3 ∧ (p2 → p3)))) ∨ (((p4 ∨ p5) ∧ (((p2 ∨ p5) → False) ∧ (p4 ∧ (p3 ∨ False)))) ∨ ((p5 → (True ∧ p1)) → True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_45659138009172189400877845538 : (((p5 ∨ (((((p2 ∧ (False ∨ True)) ∨ (((p4 ∧ p1) ∨ p1) → (p2 ∨ p4))) → ((p5 ∨ p2) → (p1 → p5))) → p2) ∧ True)) → p5) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_160955304174941997502357259593 : ((((False ∧ True) → p4) ∧ ((((p2 ∧ (p1 ∧ p3)) ∨ p5) ∧ p5) ∧ ((p5 → p3) ∧ (p2 ∨ p5)))) → (((True → False) → False) ∧ (p3 → True))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h2
  -- Conjunctions on the left can always be decomposed.
  let h3 := h1.left
  let h4 := h1.right
  -- Conjunctions on the left can always be decomposed.
  let h5 := h4.left
  let h6 := h4.right
  -- Conjunctions on the left can always be decomposed.
  let h7 := h5.left
  let h8 := h5.right
  -- Disjunctions on the left can always be decomposed.
  cases h7
  case inl h9 =>
    -- Conjunctions on the left can always be decomposed.
    let h10 := h9.left
    let h11 := h9.right
    -- Conjunctions on the left can always be decomposed.
    let h12 := h11.left
    let h13 := h11.right
    -- Conjunctions on the left can always be decomposed.
    let h14 := h6.left
    let h15 := h6.right
    -- Disjunctions on the left can always be decomposed.
    cases h15
    case inl h16 =>
      -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
      have h17 : True := by
        -- True on the right can always be proven directly.
        apply True.intro
      -- We have shown the premise of h2, we can now drive its conclusion.
      let h18 := h2 h17
      -- False on the left can always be used.
      apply False.elim h18
    case inr h19 =>
      -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
      have h20 : True := by
        -- True on the right can always be proven directly.
        apply True.intro
      -- We have shown the premise of h2, we can now drive its conclusion.
      let h21 := h2 h20
      -- False on the left can always be used.
      apply False.elim h21
  case inr h22 =>
    -- Conjunctions on the left can always be decomposed.
    let h23 := h6.left
    let h24 := h6.right
    -- Disjunctions on the left can always be decomposed.
    cases h24
    case inl h25 =>
      -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
      have h26 : True := by
        -- True on the right can always be proven directly.
        apply True.intro
      -- We have shown the premise of h2, we can now drive its conclusion.
      let h27 := h2 h26
      -- False on the left can always be used.
      apply False.elim h27
    case inr h28 =>
      -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
      have h29 : True := by
        -- True on the right can always be proven directly.
        apply True.intro
      -- We have shown the premise of h2, we can now drive its conclusion.
      let h30 := h2 h29
      -- False on the left can always be used.
      apply False.elim h30
  -- Implications on the right can always be decomposed.
  intro h31
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_183883113706889501526611181864 : ((((p3 → (False ∧ False)) ∨ (((p3 → p2) ∨ p4) ∨ p3)) ∧ p3) ∨ ((((p4 ∨ (False ∨ True)) ∨ p3) → p5) ∨ ((True ∨ (p4 ∨ p1)) → True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_679823662490392116968934637506 : (((((p4 ∧ ((p3 ∨ p2) ∧ ((p1 ∧ True) ∧ (((p5 ∨ (True → p4)) ∨ True) ∨ (p5 → True))))) ∨ p1) → (p3 ∨ ((False ∨ p4) → p4))) ∨ p4) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
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
    -- Conjunctions on the left can always be decomposed.
    let h5 := h4.left
    let h6 := h4.right
    -- Disjunctions on the left can always be decomposed.
    cases h5
    case inl h7 =>
      -- Conjunctions on the left can always be decomposed.
      let h8 := h6.left
      let h9 := h6.right
      -- Conjunctions on the left can always be decomposed.
      let h10 := h8.left
      let h11 := h8.right
      -- Disjunctions on the left can always be decomposed.
      cases h9
      case inl h12 =>
        -- Disjunctions on the left can always be decomposed.
        cases h12
        case inl h13 =>
          -- Disjunctions on the left can always be decomposed.
          cases h13
          case inl h14 =>
            -- Show the left disjunct based on <expert-advice>.
            apply Or.inl
            -- One of the premise coincides with the conclusion.
            exact h7
          case inr h15 =>
            -- Show the left disjunct based on <expert-advice>.
            apply Or.inl
            -- One of the premise coincides with the conclusion.
            exact h7
        case inr h16 =>
          -- Show the left disjunct based on <expert-advice>.
          apply Or.inl
          -- One of the premise coincides with the conclusion.
          exact h7
      case inr h17 =>
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- One of the premise coincides with the conclusion.
        exact h7
    case inr h18 =>
      -- Conjunctions on the left can always be decomposed.
      let h19 := h6.left
      let h20 := h6.right
      -- Conjunctions on the left can always be decomposed.
      let h21 := h19.left
      let h22 := h19.right
      -- Disjunctions on the left can always be decomposed.
      cases h20
      case inl h23 =>
        -- Disjunctions on the left can always be decomposed.
        cases h23
        case inl h24 =>
          -- Disjunctions on the left can always be decomposed.
          cases h24
          case inl h25 =>
            -- Show the right disjunct based on <expert-advice>.
            apply Or.inr
            -- Implications on the right can always be decomposed.
            intro h26
            -- Disjunctions on the left can always be decomposed.
            cases h26
            case inl h27 =>
              -- False on the left can always be used.
              apply False.elim h27
            case inr h28 =>
              -- One of the premise coincides with the conclusion.
              exact h28
          case inr h29 =>
            -- Show the right disjunct based on <expert-advice>.
            apply Or.inr
            -- Implications on the right can always be decomposed.
            intro h30
            -- Disjunctions on the left can always be decomposed.
            cases h30
            case inl h31 =>
              -- False on the left can always be used.
              apply False.elim h31
            case inr h32 =>
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
            -- False on the left can always be used.
            apply False.elim h35
          case inr h36 =>
            -- One of the premise coincides with the conclusion.
            exact h36
      case inr h37 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- Implications on the right can always be decomposed.
        intro h38
        -- Disjunctions on the left can always be decomposed.
        cases h38
        case inl h39 =>
          -- False on the left can always be used.
          apply False.elim h39
        case inr h40 =>
          -- One of the premise coincides with the conclusion.
          exact h40
  case inr h41 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h42
    -- Disjunctions on the left can always be decomposed.
    cases h42
    case inl h43 =>
      -- False on the left can always be used.
      apply False.elim h43
    case inr h44 =>
      -- One of the premise coincides with the conclusion.
      exact h44
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_225165384527467954679204059678 : (((p3 ∧ p5) ∧ p3) ∨ ((((True ∧ ((p1 → False) ∨ False)) ∧ False) → ((p5 → p4) ∨ (p4 ∨ (True ∧ p5)))) ∧ (((p1 → p3) ∧ False) ∨ True))) := by
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
  -- Disjunctions on the left can always be decomposed.
  cases h5
  case inl h6 =>
    -- False on the left can always be used.
    apply False.elim h3
  case inr h7 =>
    -- False on the left can always be used.
    apply False.elim h7
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_200268696255607395127121481889 : (((p1 ∨ (p2 ∨ p4)) → ((False ∧ p5) ∨ False)) → (p2 → (((False ∧ p1) ∧ ((p2 ∨ (p4 ∨ (p4 ∨ p2))) → ((p5 ∨ False) ∨ False))) ∧ p5))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h3 : (p1 ∨ (p2 ∨ p4)) := by
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- One of the premise coincides with the conclusion.
    exact h2
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h4 := h1 h3
  -- Disjunctions on the left can always be decomposed.
  cases h4
  case inl h5 =>
    -- Conjunctions on the left can always be decomposed.
    let h6 := h5.left
    let h7 := h5.right
    -- False on the left can always be used.
    apply False.elim h6
  case inr h8 =>
    -- False on the left can always be used.
    apply False.elim h8
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h9 : (p1 ∨ (p2 ∨ p4)) := by
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- One of the premise coincides with the conclusion.
    exact h2
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h10 := h1 h9
  -- Disjunctions on the left can always be decomposed.
  cases h10
  case inl h11 =>
    -- Conjunctions on the left can always be decomposed.
    let h12 := h11.left
    let h13 := h11.right
    -- False on the left can always be used.
    apply False.elim h12
  case inr h14 =>
    -- False on the left can always be used.
    apply False.elim h14
  -- Implications on the right can always be decomposed.
  intro h15
  -- Disjunctions on the left can always be decomposed.
  cases h15
  case inl h16 =>
    -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
    have h17 : (p1 ∨ (p2 ∨ p4)) := by
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- One of the premise coincides with the conclusion.
      exact h2
    -- We have shown the premise of h1, we can now drive its conclusion.
    let h18 := h1 h17
    -- Disjunctions on the left can always be decomposed.
    cases h18
    case inl h19 =>
      -- Conjunctions on the left can always be decomposed.
      let h20 := h19.left
      let h21 := h19.right
      -- False on the left can always be used.
      apply False.elim h20
    case inr h22 =>
      -- False on the left can always be used.
      apply False.elim h22
  case inr h23 =>
    -- Disjunctions on the left can always be decomposed.
    cases h23
    case inl h24 =>
      -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
      have h25 : (p1 ∨ (p2 ∨ p4)) := by
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- One of the premise coincides with the conclusion.
        exact h2
      -- We have shown the premise of h1, we can now drive its conclusion.
      let h26 := h1 h25
      -- Disjunctions on the left can always be decomposed.
      cases h26
      case inl h27 =>
        -- Conjunctions on the left can always be decomposed.
        let h28 := h27.left
        let h29 := h27.right
        -- False on the left can always be used.
        apply False.elim h28
      case inr h30 =>
        -- False on the left can always be used.
        apply False.elim h30
    case inr h31 =>
      -- Disjunctions on the left can always be decomposed.
      cases h31
      case inl h32 =>
        -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
        have h33 : (p1 ∨ (p2 ∨ p4)) := by
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- Show the left disjunct based on <expert-advice>.
          apply Or.inl
          -- One of the premise coincides with the conclusion.
          exact h2
        -- We have shown the premise of h1, we can now drive its conclusion.
        let h34 := h1 h33
        -- Disjunctions on the left can always be decomposed.
        cases h34
        case inl h35 =>
          -- Conjunctions on the left can always be decomposed.
          let h36 := h35.left
          let h37 := h35.right
          -- False on the left can always be used.
          apply False.elim h36
        case inr h38 =>
          -- False on the left can always be used.
          apply False.elim h38
      case inr h39 =>
        -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
        have h40 : (p1 ∨ (p2 ∨ p4)) := by
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- Show the left disjunct based on <expert-advice>.
          apply Or.inl
          -- One of the premise coincides with the conclusion.
          exact h2
        -- We have shown the premise of h1, we can now drive its conclusion.
        let h41 := h1 h40
        -- Disjunctions on the left can always be decomposed.
        cases h41
        case inl h42 =>
          -- Conjunctions on the left can always be decomposed.
          let h43 := h42.left
          let h44 := h42.right
          -- False on the left can always be used.
          apply False.elim h43
        case inr h45 =>
          -- False on the left can always be used.
          apply False.elim h45
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h46 : (p1 ∨ (p2 ∨ p4)) := by
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- One of the premise coincides with the conclusion.
    exact h2
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h47 := h1 h46
  -- Disjunctions on the left can always be decomposed.
  cases h47
  case inl h48 =>
    -- Conjunctions on the left can always be decomposed.
    let h49 := h48.left
    let h50 := h48.right
    -- False on the left can always be used.
    apply False.elim h49
  case inr h51 =>
    -- False on the left can always be used.
    apply False.elim h51



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_192324130309330282627318008540 : (((p5 ∧ (p4 ∨ (False ∧ ((p1 → False) → p1)))) ∧ True) → (((p3 → ((p2 ∨ p2) ∧ p2)) ∧ False) ∨ ((False ∨ (p5 ∨ p1)) ∨ (p3 ∨ p2)))) := by
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
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- One of the premise coincides with the conclusion.
    exact h4
  case inr h7 =>
    -- Conjunctions on the left can always be decomposed.
    let h8 := h7.left
    let h9 := h7.right
    -- False on the left can always be used.
    apply False.elim h8



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_213409892645634633855584168969 : (((p2 ∨ (False ∧ True)) ∧ p5) ∨ (((((True ∨ p3) ∨ p4) ∧ p1) ∧ ((False → (p5 ∨ p5)) ∨ p4)) → ((p2 ∧ ((p5 → True) ∧ p2)) ∨ p1))) := by
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
  cases h4
  case inl h6 =>
    -- Disjunctions on the left can always be decomposed.
    cases h6
    case inl h7 =>
      -- Disjunctions on the left can always be decomposed.
      cases h3
      case inl h8 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- One of the premise coincides with the conclusion.
        exact h5
      case inr h9 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- One of the premise coincides with the conclusion.
        exact h5
    case inr h10 =>
      -- Disjunctions on the left can always be decomposed.
      cases h3
      case inl h11 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- One of the premise coincides with the conclusion.
        exact h5
      case inr h12 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- One of the premise coincides with the conclusion.
        exact h5
  case inr h13 =>
    -- Disjunctions on the left can always be decomposed.
    cases h3
    case inl h14 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- One of the premise coincides with the conclusion.
      exact h5
    case inr h15 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- One of the premise coincides with the conclusion.
      exact h5



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_266287090329960974150997899995 : (True ∧ (p5 → (p3 ∨ (((p2 ∨ (p5 → (p3 → p4))) → p1) → (p2 ∨ (((p4 ∨ (((True → (False ∨ True)) ∧ p3) ∨ p4)) ∨ p3) ∨ p5)))))) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h2
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_179218851073325943906765717889 : ((p4 ∧ (((p2 → (p4 ∧ p4)) → False) ∨ (((True ∨ p3) → p3) ∨ p1))) ∨ (p3 → (p1 → (((p5 ∨ p1) ∨ (p4 → p1)) → (p3 ∨ False))))) := by
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
    -- Disjunctions on the left can always be decomposed.
    cases h4
    case inl h5 =>
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- One of the premise coincides with the conclusion.
      exact h1
    case inr h6 =>
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- One of the premise coincides with the conclusion.
      exact h1
  case inr h7 =>
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- One of the premise coincides with the conclusion.
    exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_960372046070154795496280360828 : ((((p5 ∧ p4) ∧ ((p3 ∨ p5) → ((((False → p1) ∧ (p1 ∧ (False → p1))) ∨ ((p1 ∧ p1) → ((p3 ∨ False) ∨ (p2 ∨ p3)))) ∧ False))) → False) ∧ True) := by
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
  -- We want to use the implication h3 based on <expert-advice>. So we show its premise.
  have h6 : (p3 ∨ p5) := by
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h4
  -- We have shown the premise of h3, we can now drive its conclusion.
  let h7 := h3 h6
  -- We need to get the right conjuct of h7 based on <expert-advice>.
  let h8 := h7.right
  -- False on the left can always be used.
  apply False.elim h8
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_680788890750169467352460371865 : (((((p1 ∧ (p5 ∧ p1)) ∧ ((p3 ∨ True) ∧ (p1 ∧ (p3 → (True ∨ (p5 → ((p2 → p1) → p2))))))) → (p4 → (p1 → (p1 → p2)))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_218649691440796860967562106795 : ((True ∧ ((p2 ∨ True) → False)) → (p2 → ((p2 ∧ (True → ((False ∧ False) ∨ p5))) ∧ (p4 ∨ ((False ∨ True) ∨ (p1 ∧ ((p4 ∨ p1) → p2))))))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Conjunctions on the left can always be decomposed.
  let h3 := h1.left
  let h4 := h1.right
  -- One of the premise coincides with the conclusion.
  exact h2
  -- Implications on the right can always be decomposed.
  intro h5
  -- Conjunctions on the left can always be decomposed.
  let h6 := h1.left
  let h7 := h1.right
  -- We want to use the implication h7 based on <expert-advice>. So we show its premise.
  have h8 : (p2 ∨ True) := by
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- One of the premise coincides with the conclusion.
    exact h2
  -- We have shown the premise of h7, we can now drive its conclusion.
  let h9 := h7 h8
  -- False on the left can always be used.
  apply False.elim h9
  -- Conjunctions on the left can always be decomposed.
  let h10 := h1.left
  let h11 := h1.right
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_138467635411613490279227731493 : ((p5 → (p3 → (p1 ∨ (((p1 ∧ (((p1 ∨ False) → (False ∧ p3)) ∨ (True ∧ p4))) ∧ p2) ∨ ((p4 → True) → p5))))) ∨ ((p4 → p5) ∧ True)) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h3
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_2556582897285794470856103143 : ((((p1 ∨ p1) → p4) → ((p2 ∧ p5) → p1)) ∨ (((p2 ∧ ((p3 → (p4 ∨ p5)) ∨ (p3 ∧ p4))) ∨ True) ∨ ((p3 → p4) ∨ p4))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_167560266708998717693759278001 : (((((((p5 ∨ False) → p5) ∧ p2) ∧ (((True ∧ True) ∧ p4) ∨ p1)) → p1) ∨ (p3 ∨ p5)) → ((p1 → p1) ∧ (((p2 → p4) ∨ p2) ∨ True))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h2
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h3 =>
    -- One of the premise coincides with the conclusion.
    exact h2
  case inr h4 =>
    -- Disjunctions on the left can always be decomposed.
    cases h4
    case inl h5 =>
      -- One of the premise coincides with the conclusion.
      exact h2
    case inr h6 =>
      -- One of the premise coincides with the conclusion.
      exact h2
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h7 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro
  case inr h8 =>
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



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_684991344088700602974750353092 : ((((p4 ∧ (((((p1 ∧ True) ∨ False) ∨ True) ∧ (False ∧ ((p3 ∧ p3) → p5))) → (p4 ∧ p1))) ∨ (((p3 ∧ False) → True) → (p2 ∨ p1))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_780695069877308316680376648942 : (((p2 ∨ ((p2 ∨ (p3 ∨ (p1 ∧ ((p2 → p4) → p2)))) → (((p2 ∨ True) ∨ False) ∧ ((False ∨ (p5 ∧ (False ∨ (p2 ∨ True)))) ∨ True)))) ∨ False) ∧ True) := by
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
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h2 =>
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- One of the premise coincides with the conclusion.
    exact h2
  case inr h3 =>
    -- Disjunctions on the left can always be decomposed.
    cases h3
    case inl h4 =>
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- True on the right can always be proven directly.
      apply True.intro
    case inr h5 =>
      -- Conjunctions on the left can always be decomposed.
      let h6 := h5.left
      let h7 := h5.right
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- True on the right can always be proven directly.
      apply True.intro
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h8 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro
  case inr h9 =>
    -- Disjunctions on the left can always be decomposed.
    cases h9
    case inl h10 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- True on the right can always be proven directly.
      apply True.intro
    case inr h11 =>
      -- Conjunctions on the left can always be decomposed.
      let h12 := h11.left
      let h13 := h11.right
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- True on the right can always be proven directly.
      apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_784535138159371368980069356602 : (((p3 ∨ (False ∨ (((((p1 ∧ (p1 ∨ (p1 → p2))) ∨ p4) ∨ (p5 → (p1 → p5))) → ((False ∧ False) ∧ p5)) ∧ ((p5 → False) ∧ p1)))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_135560116150515473326738671465 : (((False ∨ ((p2 → p4) ∨ (((p1 → ((p2 ∨ p5) ∨ True)) ∧ (p2 ∨ True)) → p1))) ∧ ((p1 ∧ (p1 → p4)) → p3)) ∨ ((p1 ∧ p2) → True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_619373497383063516575439135479 : ((((((False → p3) → False) → (p4 ∨ ((p5 → (((p1 → (p3 ∧ ((p1 ∧ p4) ∧ p5))) ∨ p2) → (True → p4))) → (True ∧ p4)))) ∨ False) ∨ False) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h2 : (False → p3) := by
    -- Implications on the right can always be decomposed.
    intro h3
    -- False on the left can always be used.
    apply False.elim h3
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h4 := h1 h2
  -- False on the left can always be used.
  apply False.elim h4
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_134908983338585164711009934674 : ((((False ∨ ((p1 ∧ p4) ∧ (((p5 ∧ ((p1 ∧ ((p2 → p2) ∧ p3)) → True)) ∧ p1) → p2))) ∧ p5) ∧ (p4 ∨ True)) ∨ ((False → p5) ∨ p5)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_197007215721032315523288513470 : ((((p2 ∧ (p5 ∧ p4)) ∧ (p5 ∧ p5)) ∨ True) ∨ ((False → (True ∨ ((True → p4) → (((p4 → ((True ∨ False) ∨ p4)) → p4) → False)))) → p5)) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_113056419572028308467032752216 : (((p2 ∨ ((p1 → ((p2 → (p5 ∨ (((p4 → ((p5 ∨ p2) → p3)) ∨ p5) → p1))) → ((False ∨ p4) → False))) ∨ p2)) → p5) ∨ (True ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_740479232445829122541187210143 : ((((p1 ∨ p5) ∨ (((False ∨ (((((p1 ∨ p3) ∧ p5) → ((True ∧ p4) ∧ p5)) → True) → ((p5 → p5) ∧ p4))) ∨ p2) ∨ (p5 → True))) ∨ False) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
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
theorem thm_5_vars_117205874531093002915400169030 : ((True ∧ ((((p4 ∨ (p5 ∧ (p3 → False))) ∧ p1) → p4) → ((p5 ∧ p5) ∨ ((True → (p4 ∨ (p4 → (p2 ∧ p2)))) ∨ True)))) ∨ (p1 → False)) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_717620462602351053869708100110 : ((((p4 → (p4 → (False → True))) ∧ (((p2 ∨ (((p2 → p3) ∨ (p3 ∨ p4)) ∨ True)) → (p1 ∨ (p1 → (False ∨ p4)))) ∧ (p3 → p3))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_902482301270479853298862078466 : (((((((p2 ∧ (p2 → p2)) ∨ True) → ((False ∧ p4) → p5)) → ((p5 ∧ p5) ∨ (p5 ∧ (True → p3)))) ∧ (p3 ∨ ((False ∨ p5) → p4))) → p5) ∧ True) := by
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
    -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
    have h5 : (((p2 ∧ (p2 → p2)) ∨ True) → ((False ∧ p4) → p5)) := by
      -- Implications on the right can always be decomposed.
      intro h6
      -- Implications on the right can always be decomposed.
      intro h7
      -- Conjunctions on the left can always be decomposed.
      let h8 := h7.left
      let h9 := h7.right
      -- False on the left can always be used.
      apply False.elim h8
    -- We have shown the premise of h2, we can now drive its conclusion.
    let h10 := h2 h5
    -- Disjunctions on the left can always be decomposed.
    cases h10
    case inl h11 =>
      -- Conjunctions on the left can always be decomposed.
      let h12 := h11.left
      let h13 := h11.right
      -- One of the premise coincides with the conclusion.
      exact h13
    case inr h14 =>
      -- Conjunctions on the left can always be decomposed.
      let h15 := h14.left
      let h16 := h14.right
      -- One of the premise coincides with the conclusion.
      exact h15
  case inr h17 =>
    -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
    have h18 : (((p2 ∧ (p2 → p2)) ∨ True) → ((False ∧ p4) → p5)) := by
      -- Implications on the right can always be decomposed.
      intro h19
      -- Implications on the right can always be decomposed.
      intro h20
      -- Conjunctions on the left can always be decomposed.
      let h21 := h20.left
      let h22 := h20.right
      -- False on the left can always be used.
      apply False.elim h21
    -- We have shown the premise of h2, we can now drive its conclusion.
    let h23 := h2 h18
    -- Disjunctions on the left can always be decomposed.
    cases h23
    case inl h24 =>
      -- Conjunctions on the left can always be decomposed.
      let h25 := h24.left
      let h26 := h24.right
      -- One of the premise coincides with the conclusion.
      exact h26
    case inr h27 =>
      -- Conjunctions on the left can always be decomposed.
      let h28 := h27.left
      let h29 := h27.right
      -- One of the premise coincides with the conclusion.
      exact h28
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_172430494131631282541105173945 : (((p1 ∨ ((p5 → p5) ∧ p5)) ∧ (p1 ∧ (p1 ∨ ((False ∧ (p3 ∨ p3)) ∨ False)))) ∨ ((p1 ∧ ((p2 ∧ p4) ∧ False)) → (p5 ∨ (False ∨ False)))) := by
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
  -- False on the left can always be used.
  apply False.elim h5



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_53286586689004654010174739420 : (((p5 ∧ (p4 ∨ ((True → False) ∧ ((p5 ∨ True) ∨ (p2 → p5))))) ∨ (True ∧ (p4 → ((((p1 ∧ p5) ∧ True) ∨ True) ∧ (p2 ∨ p4))))) ∨ p4) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_147704504830651344036182209772 : (((((((True ∨ p4) ∨ (p1 ∨ p2)) ∧ p2) ∨ (True ∧ p1)) ∧ ((p2 ∨ (False → p3)) ∧ (p3 ∨ True))) → p5) ∨ ((p3 → p3) ∧ (False → p3))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h1
  -- One of the premise coincides with the conclusion.
  exact h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- False on the left can always be used.
  apply False.elim h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_138146903373361685785187490712 : ((p1 → (((p3 → ((p5 ∧ ((((p4 → (p3 ∧ False)) ∨ (p1 ∧ p1)) ∨ True) ∧ (False → p5))) → p2)) → p3) ∨ p2)) ∨ ((p4 ∨ True) → True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_56314294180309195002402005989 : ((((True ∨ (False → p1)) ∧ p4) → ((True → (((((False → p3) ∧ ((p4 ∨ (False → p3)) ∧ p5)) ∨ p4) ∧ p3) ∨ p2)) ∧ (True ∨ p1))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_351396162212895249342911177516 : (p4 → ((((p1 ∧ p5) → ((((True ∧ p3) ∧ ((p4 ∨ (p5 → p4)) ∧ p1)) ∧ (p4 → p1)) ∧ p1)) → p3) ∨ ((True → True) → (p5 ∨ True)))) := by
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
theorem thm_5_vars_58281673117171878270575337050 : (((True ∨ False) ∧ (((p2 ∨ (p2 ∧ p4)) ∨ (((p3 ∨ (((p1 ∧ p3) ∨ ((False ∧ p2) ∧ p1)) ∨ p2)) ∨ True) → (True ∧ p4))) ∧ p1)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_782396104839291434332152464348 : (((p3 ∨ (((((((False ∨ (p4 ∨ p4)) ∧ p3) ∨ (True ∧ p1)) ∨ p3) ∨ (True → (((p5 ∧ (True ∧ p4)) → p5) ∨ p5))) → p1) ∨ True)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_40399602280218005315534322867 : (((((False ∨ ((p1 → (False ∧ (True → p4))) → ((p3 → True) → (p2 ∧ (p3 ∧ (p4 ∧ p2)))))) ∧ ((False ∨ p3) ∧ p4)) ∨ p5) ∨ True) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_214871452297608428225031315980 : (((p1 → p3) ∨ (p5 ∨ p5)) ∨ ((p3 → (((((True → (p1 ∨ (p2 → (p2 ∨ p2)))) → (p2 ∨ p4)) ∨ p5) → p5) ∨ p3)) ∨ (p1 ∧ p1))) := by
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
theorem thm_5_vars_205295542547657652701991022636 : (((p4 ∧ (True ∨ True)) ∨ (p5 ∧ p5)) ∨ ((p4 → ((p3 ∧ (p1 ∧ (True ∧ p3))) ∨ (((p4 → (p1 ∨ (p1 ∧ True))) → p1) → p1))) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_206461206367543008605691869401 : ((p4 ∨ (p4 ∧ (False ∧ (p2 ∧ True)))) ∨ (((((True ∧ True) → False) ∨ p5) ∨ (p3 → False)) ∨ ((True ∨ (p3 ∨ ((p5 ∧ p3) ∨ p4))) ∨ p2))) := by
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
theorem thm_5_vars_254235136299785170067555950478 : ((p2 ∧ p2) → ((((False → p1) → p5) → (p4 ∨ p2)) ∧ (((p3 → (p1 ∧ ((p3 ∨ (False ∧ p1)) ∧ (p3 ∧ p1)))) → (False ∧ True)) ∨ True))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h2
  -- Conjunctions on the left can always be decomposed.
  let h3 := h1.left
  let h4 := h1.right
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h4
  -- Conjunctions on the left can always be decomposed.
  let h5 := h1.left
  let h6 := h1.right
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_136151695064000132147419531792 : ((((True ∧ p2) ∨ (((p1 → False) → p4) ∧ p3)) → (True ∧ (p4 ∨ ((p2 ∧ (False ∨ (p5 ∧ p1))) ∧ (p2 ∧ p1))))) ∨ (True → (p1 ∨ True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_69156610490635706168093708785 : ((p5 → ((((p2 ∨ (p2 → (p3 ∧ ((p3 ∧ (True → p4)) → p3)))) ∨ (False ∧ (p1 ∨ p4))) ∧ False) ∨ ((p3 → (p3 ∨ p4)) ∧ True))) ∨ p4) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h2
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- One of the premise coincides with the conclusion.
  exact h2
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_347026984213630634888994500285 : (p3 → ((p2 ∨ (p1 ∧ (((((p4 ∨ p2) ∧ (p4 ∧ p3)) ∨ p5) → (p2 → p5)) → False))) ∨ (((False → p3) → (False → (p2 ∧ False))) ∧ True))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h2
  -- Implications on the right can always be decomposed.
  intro h3
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- False on the left can always be used.
  apply False.elim h3
  -- False on the left can always be used.
  apply False.elim h3
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_650621174266606880488144919450 : ((((((p4 ∨ (p1 ∨ (p1 ∨ True))) ∧ ((p2 → p3) ∧ p1)) ∧ ((p2 ∧ False) ∧ ((p4 ∧ (p4 → p1)) → (p4 → p1)))) ∧ (p4 ∧ p1)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_624373302744400702643000062863 : ((((p3 ∨ ((p3 → p5) ∧ ((True ∨ ((p3 → (p5 ∧ p4)) → (True ∨ p4))) → (((p3 → False) → (p5 ∧ False)) ∧ (p3 → p3))))) ∨ p3) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_156871405352567017955709697934 : ((((False ∧ ((p4 ∧ ((p4 → ((False ∨ True) ∨ p3)) ∧ (p2 ∧ p5))) ∨ (p4 → p5))) ∧ p4) ∨ True) ∨ (p4 → (p1 → (p1 ∨ (p5 → p4))))) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_171377980448185799898390317425 : ((((False ∨ ((p3 ∨ False) ∧ (p1 ∨ (p5 ∧ p1)))) ∧ (p1 ∧ (p1 ∧ p4))) ∧ p2) ∨ (((p5 → p4) → True) → ((p4 ∧ (p2 ∧ p2)) → True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_165881850861560133670256123680 : ((((p5 ∧ p2) ∨ p5) → ((p1 ∧ ((((p1 ∨ p5) → p1) → p2) ∨ True)) ∧ (False ∧ p1))) ∨ (p1 → ((p4 → p5) ∨ ((False ∧ p2) ∨ p1)))) := by
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
theorem thm_5_vars_113077545758300069760725136253 : (((p4 ∨ (((((True ∨ p5) ∨ p1) ∧ (((True ∨ p1) ∧ (p3 ∧ p5)) ∨ (True ∨ (True → (p4 → True))))) ∧ True) ∨ p1)) → p1) ∨ (p4 ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_336130761535500771467203270149 : (p1 → ((((p5 ∨ p4) ∧ ((p5 ∧ ((p5 ∨ p2) ∧ (False ∨ (p2 ∧ False)))) ∨ (((False ∨ p2) ∧ (True ∨ (p1 → p3))) ∨ p1))) ∨ False) ∨ True)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_48685057040227347716588794504 : (((((((True ∨ False) → p4) ∧ (p2 → p3)) ∨ True) ∧ ((False ∧ ((p5 ∧ p3) → p2)) ∨ (p4 ∧ (True ∨ p4)))) ∧ (p1 ∨ (p1 ∧ p3))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_156917546870321645212880267479 : ((((((False → (p2 → False)) ∨ p3) → ((p2 ∨ ((p1 → True) → (p3 → True))) ∨ p3)) → False) ∨ p5) ∨ (((p3 ∨ (p3 → p2)) ∨ True) ∧ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_218997689842556738329856637928 : ((p4 ∧ (True ∨ (True ∨ p4))) → ((p3 ∧ p2) ∨ (((((p4 ∧ p2) → p4) ∨ (p3 → p2)) ∨ (True → ((p4 ∧ (True ∨ p2)) ∧ p1))) ∨ True))) := by
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
      -- True on the right can always be proven directly.
      apply True.intro
    case inr h7 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- True on the right can always be proven directly.
      apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_9360135920373744451233509949 : (((((False ∧ (p1 ∧ p4)) ∨ p3) ∧ (p1 → (p5 ∨ (p5 ∨ (p3 → (((False ∧ ((p4 → True) → p5)) → (p1 ∨ True)) ∧ p1)))))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_112735741542079701163631546992 : (((((p3 → ((False → (p4 ∨ True)) → True)) → ((p1 ∧ False) ∧ p1)) ∧ ((p2 → p5) ∧ ((p2 → (p2 ∨ p5)) ∨ p4))) → p5) ∨ (p2 ∧ True)) := by
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
    -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
    have h7 : (p3 → ((False → (p4 ∨ True)) → True)) := by
      -- Implications on the right can always be decomposed.
      intro h8
      -- Implications on the right can always be decomposed.
      intro h9
      -- True on the right can always be proven directly.
      apply True.intro
    -- We have shown the premise of h2, we can now drive its conclusion.
    let h10 := h2 h7
    -- We need to get the left conjuct of h10 based on <expert-advice>.
    let h11 := h10.left
    -- We need to get the right conjuct of h11 based on <expert-advice>.
    let h12 := h11.right
    -- False on the left can always be used.
    apply False.elim h12
  case inr h13 =>
    -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
    have h14 : (p3 → ((False → (p4 ∨ True)) → True)) := by
      -- Implications on the right can always be decomposed.
      intro h15
      -- Implications on the right can always be decomposed.
      intro h16
      -- True on the right can always be proven directly.
      apply True.intro
    -- We have shown the premise of h2, we can now drive its conclusion.
    let h17 := h2 h14
    -- We need to get the left conjuct of h17 based on <expert-advice>.
    let h18 := h17.left
    -- We need to get the right conjuct of h18 based on <expert-advice>.
    let h19 := h18.right
    -- False on the left can always be used.
    apply False.elim h19



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_777394747244775552377424001391 : (((p1 ∨ (((False → (p1 → ((((True ∧ ((p4 ∨ p5) ∧ False)) ∨ False) ∨ p2) → p3))) → p5) ∧ (p5 → (p4 → ((p5 ∧ p2) → False))))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_135970564724397459713521772788 : (((((((p1 → p3) ∨ p4) ∨ (p5 ∨ p3)) ∧ p1) ∧ p2) ∨ ((False → ((p2 → False) → True)) → ((True → p5) ∧ p4))) ∨ (False → (p5 ∧ p5))) := by
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



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_139685187019119124456240912901 : (((((p5 → True) ∨ p4) → ((False ∨ (False ∨ False)) ∨ (((((p4 ∧ p3) ∨ True) → (p2 ∧ p2)) ∨ True) ∨ p1))) → False) → (False ∧ (p3 ∨ p1))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h2 : (((p5 → True) ∨ p4) → ((False ∨ (False ∨ False)) ∨ (((((p4 ∧ p3) ∨ True) → (p2 ∧ p2)) ∨ True) ∨ p1))) := by
    -- Implications on the right can always be decomposed.
    intro h3
    -- Disjunctions on the left can always be decomposed.
    cases h3
    case inl h4 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- True on the right can always be proven directly.
      apply True.intro
    case inr h5 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- True on the right can always be proven directly.
      apply True.intro
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h6 := h1 h2
  -- False on the left can always be used.
  apply False.elim h6
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h7 : (((p5 → True) ∨ p4) → ((False ∨ (False ∨ False)) ∨ (((((p4 ∧ p3) ∨ True) → (p2 ∧ p2)) ∨ True) ∨ p1))) := by
    -- Implications on the right can always be decomposed.
    intro h8
    -- Disjunctions on the left can always be decomposed.
    cases h8
    case inl h9 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- True on the right can always be proven directly.
      apply True.intro
    case inr h10 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- True on the right can always be proven directly.
      apply True.intro
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h11 := h1 h7
  -- False on the left can always be used.
  apply False.elim h11



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_130104652298414162112003687205 : ((((p4 ∧ (p2 ∨ ((((((p3 ∨ p5) ∨ p5) ∨ p1) → True) → ((p2 → p3) ∧ p4)) → p3))) → p5) ∨ (p2 ∨ True)) ∧ (True ∨ (p4 → p1))) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_186105398958083763288667711531 : ((((p4 ∧ (p5 ∧ (p3 ∨ (p4 → True)))) ∨ (p1 ∨ False)) ∨ p5) → ((p5 ∧ (p5 ∧ (False ∧ (p2 → ((p2 → (p1 → p5)) → p4))))) ∨ True)) := by
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
      -- Conjunctions on the left can always be decomposed.
      let h6 := h5.left
      let h7 := h5.right
      -- Disjunctions on the left can always be decomposed.
      cases h7
      case inl h8 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- True on the right can always be proven directly.
        apply True.intro
      case inr h9 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- True on the right can always be proven directly.
        apply True.intro
    case inr h10 =>
      -- Disjunctions on the left can always be decomposed.
      cases h10
      case inl h11 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- True on the right can always be proven directly.
        apply True.intro
      case inr h12 =>
        -- False on the left can always be used.
        apply False.elim h12
  case inr h13 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_702990811287281246607475813320 : ((((((p3 → False) ∨ False) → ((p4 → (p1 ∧ False)) ∨ p2)) ∨ ((((p1 → p4) ∨ p5) ∨ (p4 → (False → p2))) ∨ ((p2 ∧ p4) → p4))) ∨ False) ∧ True) := by
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
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- False on the left can always be used.
  apply False.elim h2
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_115920494317045869887209514354 : ((((p2 ∧ p2) → (p2 ∧ p3)) ∨ ((((((False → p5) → p4) ∨ False) → (p4 ∨ p3)) → (p5 ∨ False)) ∨ ((p5 ∧ p4) → p4))) ∨ (p4 ∧ p4)) := by
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
  -- One of the premise coincides with the conclusion.
  exact h3



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_792330386983699591142727054226 : (((True → ((((p3 ∧ (True → p2)) → False) ∨ ((True ∧ p5) → (p1 ∧ ((False ∧ True) ∧ p1)))) → (((False ∨ (p2 → p3)) → p5) ∨ True))) ∨ p5) ∧ True) := by
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
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro
  case inr h4 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_923663968571910581079118493236 : (((((((False ∨ True) ∨ p4) ∨ p1) → (((True ∨ p2) ∧ p2) ∧ p4)) ∧ ((False → (((p4 → False) → True) → p4)) ∧ ((True ∧ p1) ∨ p4))) → p4) ∧ True) := by
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
  -- Disjunctions on the left can always be decomposed.
  cases h5
  case inl h6 =>
    -- Conjunctions on the left can always be decomposed.
    let h7 := h6.left
    let h8 := h6.right
    -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
    have h9 : (((False ∨ True) ∨ p4) ∨ p1) := by
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- One of the premise coincides with the conclusion.
      exact h8
    -- We have shown the premise of h2, we can now drive its conclusion.
    let h10 := h2 h9
    -- We need to get the right conjuct of h10 based on <expert-advice>.
    let h11 := h10.right
    -- One of the premise coincides with the conclusion.
    exact h11
  case inr h12 =>
    -- One of the premise coincides with the conclusion.
    exact h12
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_322261119662722774440217603432 : (p5 ∨ ((((p2 ∧ p3) ∧ ((True ∧ p2) → (((p3 → (((p4 ∧ p4) ∨ p1) → (p1 ∧ ((p5 → p1) → True)))) ∨ False) ∧ p3))) ∨ True) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_223834885889942103064591801134 : ((p3 ∨ (False ∨ True)) ∧ (((p2 ∨ (((p1 → (p4 ∧ (p2 ∧ (p2 ∨ p5)))) → p2) ∧ (((p2 → p5) ∨ True) → p1))) ∨ (True ∨ False)) ∨ True)) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_47437248698061397237644574776 : (((p2 ∧ (p1 ∨ (((p5 ∧ (p2 → p4)) ∨ (((p1 ∧ (False ∨ p2)) ∧ p2) ∧ (True ∧ ((p1 ∧ p3) ∨ p2)))) ∧ False))) ∨ (p5 ∧ p1)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_766353168708325648400796893985 : (((p4 ∧ (True ∧ (((p2 → (p2 ∨ (True ∧ (p3 ∧ (p4 → (p1 → p5)))))) → ((p5 ∧ (True ∧ ((p1 → True) ∨ p2))) → p2)) ∧ False))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_133724433701633076921092673279 : ((((p3 → (((p1 ∧ ((True → p3) ∨ p4)) ∧ (p5 ∨ False)) ∨ p2)) ∨ (p5 ∨ ((False ∨ (p2 ∨ p4)) → p5))) ∧ p3) ∨ (False → (True → p2))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_113118062531414713170031777185 : (((False → (p3 ∧ (((((p1 ∨ p2) ∧ ((False ∧ p4) → p2)) ∧ True) → (p3 ∧ (False ∨ (p5 ∧ p1)))) ∨ (p3 ∨ p3)))) → p1) ∨ (p2 → True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_229631955964339198240011800715 : ((p3 → (p1 ∨ p5)) ∨ ((False ∧ p3) ∨ ((((p3 → p2) → (p4 ∨ p3)) ∧ ((True ∨ False) → p4)) ∨ ((((p3 ∨ False) ∧ p5) → p5) ∨ p4)))) := by
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
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- Disjunctions on the left can always be decomposed.
  cases h2
  case inl h4 =>
    -- One of the premise coincides with the conclusion.
    exact h3
  case inr h5 =>
    -- False on the left can always be used.
    apply False.elim h5



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_339724726717770281367843797093 : (p1 → (p4 ∨ ((((p4 → (p2 ∧ p1)) ∧ ((p4 ∨ (((True → True) ∧ (p2 ∧ p1)) ∧ True)) ∨ (p5 ∧ p2))) → (p1 ∧ (p4 → p3))) ∨ p1))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_749221997049331858854772791513 : ((((p5 → p3) → ((p3 ∧ (p1 → (((p4 ∨ p3) → ((p4 ∧ (p2 ∨ (False ∨ p4))) ∧ p3)) ∨ p1))) ∨ ((True ∨ (p3 → True)) ∨ False))) ∨ False) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
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
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_136394891596043177934283240301 : (((p5 ∧ ((True → p2) ∨ True)) ∨ (p1 ∧ (((False ∨ p3) ∨ False) ∨ (((p5 → (p4 ∨ p4)) ∨ (True → p3)) → False)))) ∨ ((p3 ∧ p4) → p3)) := by
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
theorem thm_5_vars_53331891133355946148588111772 : ((((((False ∨ (((False ∧ p1) → p2) ∨ p4)) → True) ∨ p5) ∧ p3) → (p2 → ((False ∨ (p5 ∧ ((p2 ∧ False) ∧ p2))) ∨ (p2 ∧ True)))) ∨ False) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
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
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Conjunctions on the right can always be decomposed.
    apply And.intro
    -- One of the premise coincides with the conclusion.
    exact h2
    -- True on the right can always be proven directly.
    apply True.intro
  case inr h6 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Conjunctions on the right can always be decomposed.
    apply And.intro
    -- One of the premise coincides with the conclusion.
    exact h2
    -- True on the right can always be proven directly.
    apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_110952620185791796081115350965 : ((((((p2 ∨ p3) → ((p5 ∧ p1) ∨ ((((True ∧ False) ∨ ((True → p1) ∧ p4)) ∨ p5) → p1))) ∨ p5) ∨ (p4 → p3)) ∧ p5) ∨ (True ∨ p3)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_337391053718423961900376484932 : (p1 → ((False ∨ ((p5 ∨ (p5 → (p4 ∨ ((p2 ∧ ((False ∨ p2) ∧ True)) ∧ p2)))) → (((p2 ∧ False) → p3) → p4))) ∨ (False → (False ∧ p4)))) := by
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
theorem thm_5_vars_19553340178021227469513620166 : ((((p1 → ((p2 ∨ (True ∧ (p2 ∧ p3))) ∨ ((p3 ∧ p4) ∧ p5))) ∨ (p5 ∧ p5)) ∨ ((((p3 ∧ p2) ∧ p1) → p2) ∨ (True ∨ p4))) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
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
theorem thm_5_vars_1987981860220090429390767423 : ((((((True → (((p5 ∨ p4) → False) ∨ (True ∨ (True ∨ p3)))) ∨ p1) → (p1 ∧ True)) ∨ p1) ∨ p4) → ((True ∧ p4) ∨ (p3 → p1))) := by
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
      -- We want to use the implication h3 based on <expert-advice>. So we show its premise.
      have h5 : ((True → (((p5 ∨ p4) → False) ∨ (True ∨ (True ∨ p3)))) ∨ p1) := by
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- Implications on the right can always be decomposed.
        intro h6
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- True on the right can always be proven directly.
        apply True.intro
      -- We have shown the premise of h3, we can now drive its conclusion.
      let h7 := h3 h5
      -- We need to get the left conjuct of h7 based on <expert-advice>.
      let h8 := h7.left
      -- One of the premise coincides with the conclusion.
      exact h8
    case inr h9 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Implications on the right can always be decomposed.
      intro h10
      -- One of the premise coincides with the conclusion.
      exact h9
  case inr h11 =>
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Conjunctions on the right can always be decomposed.
    apply And.intro
    -- True on the right can always be proven directly.
    apply True.intro
    -- One of the premise coincides with the conclusion.
    exact h11



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_159510030067881770353709763522 : ((((True ∧ p5) ∨ ((p3 → ((p1 → p4) ∨ True)) ∧ (((p2 → p4) ∧ False) ∨ (p3 → True)))) ∧ p5) → (p4 ∨ (p3 ∨ ((True ∧ p1) → True)))) := by
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
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h7
    -- True on the right can always be proven directly.
    apply True.intro
  case inr h8 =>
    -- Conjunctions on the left can always be decomposed.
    let h9 := h8.left
    let h10 := h8.right
    -- Disjunctions on the left can always be decomposed.
    cases h10
    case inl h11 =>
      -- Conjunctions on the left can always be decomposed.
      let h12 := h11.left
      let h13 := h11.right
      -- False on the left can always be used.
      apply False.elim h13
    case inr h14 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Implications on the right can always be decomposed.
      intro h15
      -- True on the right can always be proven directly.
      apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_249194913758954969054287660300 : ((p4 ∨ p3) ∨ (((((p4 ∨ p1) ∧ p3) ∨ p2) ∨ True) ∨ (False ∧ (False ∨ ((((p5 ∧ p3) → False) ∨ False) → (p3 → (p4 → (p5 ∧ True)))))))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_178560412724422797981583044667 : (((((p4 → p5) ∧ p3) ∧ (p4 ∧ p5)) ∧ (p2 ∧ ((p1 ∧ p5) → p4))) ∨ (True ∨ (((True → (True → p3)) ∧ (p5 ∨ True)) → (p2 ∧ p5)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_37938003699725962094299020123 : ((((p1 ∨ (p2 ∧ ((p2 → p4) ∧ (p3 → (((p1 ∨ p1) ∨ (((True ∨ p5) → (p5 ∨ True)) → p4)) ∨ p3))))) ∧ (False ∨ p5)) ∧ p2) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_1786330137397773188166004892 : ((((p1 → (True → p1)) ∨ ((((p2 ∧ p4) ∨ (p3 ∧ p4)) ∨ p4) → False)) → ((p4 → (False ∨ p1)) ∨ True)) ∨ (p3 ∧ (p4 → True))) := by
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



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_117773332163793080629163300934 : ((p4 ∧ (((p5 → (p1 → (p3 → (True ∨ (p2 → (p5 → (((True ∧ False) ∨ (p1 → p5)) → p3))))))) ∧ True) → (False ∨ p5))) ∨ (False → p4)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_40581499721225400126684416756 : (((((((((p1 → False) ∧ p3) ∨ (p4 ∨ (((((p5 → p3) ∧ p2) ∨ False) → p4) ∨ p3))) ∨ p4) → (False ∧ p4)) ∧ p1) → p2) ∨ True) ∨ p1) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_689649387056932433184605032397 : (((((True ∧ (p3 → (False → True))) ∧ (((p2 ∧ False) ∨ (p5 ∨ True)) ∧ (p4 ∧ p1))) ∨ ((p3 ∧ (p2 → p4)) → (True ∨ (False → True)))) ∨ False) ∧ True) := by
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
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_738228247351304024537970991460 : ((((False ∧ p4) ∨ ((((False ∨ p5) → (((False ∨ (p2 ∧ p2)) ∨ (p5 ∨ p2)) ∨ (((False ∨ p4) → True) ∨ p1))) ∨ (p5 ∧ p3)) ∨ p1)) ∨ False) ∧ True) := by
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
  -- Implications on the right can always be decomposed.
  intro h1
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h2 =>
    -- False on the left can always be used.
    apply False.elim h2
  case inr h3 =>
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- One of the premise coincides with the conclusion.
    exact h3
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_64796210426431110843541145457 : ((p2 ∨ (((p3 ∨ False) ∧ (False ∧ (((p2 → p4) ∨ ((p3 ∧ True) ∧ p3)) ∧ (True → (p4 → (False ∧ (False → (p3 ∨ p2)))))))) ∨ p2)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_44714607113263719276752645818 : ((((False ∨ ((p5 → False) → p3)) ∧ ((p4 ∧ ((p3 → ((True ∨ p3) ∨ ((p3 ∨ (p2 ∨ p1)) ∨ p1))) ∧ (p4 ∨ False))) ∨ p4)) → p5) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



