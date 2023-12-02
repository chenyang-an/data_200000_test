variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_134591394842422613635757398415 : ((((p5 → (((p1 ∧ (((p3 ∨ True) ∧ p4) → p2)) ∨ p1) ∧ (True → (p4 ∨ (True → p2))))) ∨ (p1 ∧ p5)) → p3) ∨ (p3 → (True ∨ p2))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_137422322869309363517086291700 : ((p4 ∧ ((False ∧ (((p2 → True) → p5) ∧ (((False ∧ ((p3 → (True ∨ (p3 ∨ p5))) ∧ False)) ∨ p4) ∨ False))) ∨ p1)) ∨ (p5 ∨ (True ∨ p2))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_299261935508022516440287682254 : (False ∨ ((((((p3 ∨ False) → (p1 ∧ (p2 ∨ p1))) → p2) ∧ ((p2 ∧ p3) ∨ (p1 ∧ (p2 → False)))) → (p1 → (p4 ∨ (p2 ∧ p1)))) ∨ False)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
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
  cases h4
  case inl h5 =>
    -- Conjunctions on the left can always be decomposed.
    let h6 := h5.left
    let h7 := h5.right
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Conjunctions on the right can always be decomposed.
    apply And.intro
    -- One of the premise coincides with the conclusion.
    exact h6
    -- One of the premise coincides with the conclusion.
    exact h2
  case inr h8 =>
    -- Conjunctions on the left can always be decomposed.
    let h9 := h8.left
    let h10 := h8.right
    -- We want to use the implication h3 based on <expert-advice>. So we show its premise.
    have h11 : ((p3 ∨ False) → (p1 ∧ (p2 ∨ p1))) := by
      -- Implications on the right can always be decomposed.
      intro h12
      -- Conjunctions on the right can always be decomposed.
      apply And.intro
      -- Disjunctions on the left can always be decomposed.
      cases h12
      case inl h13 =>
        -- One of the premise coincides with the conclusion.
        exact h9
      case inr h14 =>
        -- False on the left can always be used.
        apply False.elim h14
      -- Disjunctions on the left can always be decomposed.
      cases h12
      case inl h15 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- One of the premise coincides with the conclusion.
        exact h9
      case inr h16 =>
        -- False on the left can always be used.
        apply False.elim h16
    -- We have shown the premise of h3, we can now drive its conclusion.
    let h17 := h3 h11
    -- We want to use the implication h10 based on <expert-advice>. So we show its premise.
    have h18 : p2 := by
      -- One of the premise coincides with the conclusion.
      exact h17
    -- We have shown the premise of h10, we can now drive its conclusion.
    let h19 := h10 h18
    -- False on the left can always be used.
    apply False.elim h19



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_250002314818188555246791881266 : ((True → p2) ∨ (p1 ∨ ((((p1 → True) ∧ ((True → p1) → p3)) ∨ p4) → (((False ∧ False) ∨ (p3 → ((p1 ∨ (False ∧ False)) ∨ p2))) ∨ True)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
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
theorem thm_5_vars_153298359986845906358777547251 : ((p1 ∨ ((((p1 ∧ p2) → (((((False ∧ p4) ∨ True) ∧ (p5 ∧ p5)) ∨ p3) ∧ p2)) ∧ p5) ∨ (p2 → True))) → ((p3 → False) ∨ (p3 → p3))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h2 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h3
    -- One of the premise coincides with the conclusion.
    exact h3
  case inr h4 =>
    -- Disjunctions on the left can always be decomposed.
    cases h4
    case inl h5 =>
      -- Conjunctions on the left can always be decomposed.
      let h6 := h5.left
      let h7 := h5.right
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Implications on the right can always be decomposed.
      intro h8
      -- One of the premise coincides with the conclusion.
      exact h8
    case inr h9 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Implications on the right can always be decomposed.
      intro h10
      -- One of the premise coincides with the conclusion.
      exact h10



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_199888774738440185839191361879 : ((((False → (p5 ∧ p3)) ∧ p4) ∨ (p5 → p4)) → (p4 → ((p5 → (p1 ∨ (((p5 ∨ p5) ∨ p1) ∧ p5))) ∧ ((True → (p4 → True)) ∨ p1)))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h3
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h4 =>
    -- Conjunctions on the left can always be decomposed.
    let h5 := h4.left
    let h6 := h4.right
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Conjunctions on the right can always be decomposed.
    apply And.intro
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- One of the premise coincides with the conclusion.
    exact h3
    -- One of the premise coincides with the conclusion.
    exact h3
  case inr h7 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Conjunctions on the right can always be decomposed.
    apply And.intro
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- One of the premise coincides with the conclusion.
    exact h3
    -- One of the premise coincides with the conclusion.
    exact h3
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h8 =>
    -- Conjunctions on the left can always be decomposed.
    let h9 := h8.left
    let h10 := h8.right
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Implications on the right can always be decomposed.
    intro h11
    -- Implications on the right can always be decomposed.
    intro h12
    -- True on the right can always be proven directly.
    apply True.intro
  case inr h13 =>
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Implications on the right can always be decomposed.
    intro h14
    -- Implications on the right can always be decomposed.
    intro h15
    -- True on the right can always be proven directly.
    apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_774458714688527215190676577808 : (((False ∨ ((p3 ∨ (((((p2 ∧ (p3 ∨ p4)) ∨ p5) ∨ (True ∨ p2)) ∨ (False → p4)) ∧ p5)) ∨ ((p4 → (p5 ∧ p3)) → (p3 → p3)))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_2129378874706293251869405491 : (((p2 ∨ p1) ∨ (((p2 ∧ ((p1 ∧ p5) ∨ (p1 ∧ ((p3 ∨ p4) ∧ True)))) ∧ p2) ∨ p1)) → (p5 ∨ (p1 ∨ (p4 → (p2 ∨ p3))))) := by
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
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- One of the premise coincides with the conclusion.
      exact h3
    case inr h5 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- One of the premise coincides with the conclusion.
      exact h5
  case inr h6 =>
    -- Disjunctions on the left can always be decomposed.
    cases h6
    case inl h7 =>
      -- Conjunctions on the left can always be decomposed.
      let h8 := h7.left
      let h9 := h7.right
      -- Conjunctions on the left can always be decomposed.
      let h10 := h8.left
      let h11 := h8.right
      -- Disjunctions on the left can always be decomposed.
      cases h11
      case inl h12 =>
        -- Conjunctions on the left can always be decomposed.
        let h13 := h12.left
        let h14 := h12.right
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- One of the premise coincides with the conclusion.
        exact h14
      case inr h15 =>
        -- Conjunctions on the left can always be decomposed.
        let h16 := h15.left
        let h17 := h15.right
        -- Conjunctions on the left can always be decomposed.
        let h18 := h17.left
        let h19 := h17.right
        -- Disjunctions on the left can always be decomposed.
        cases h18
        case inl h20 =>
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- Show the left disjunct based on <expert-advice>.
          apply Or.inl
          -- One of the premise coincides with the conclusion.
          exact h16
        case inr h21 =>
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- Show the left disjunct based on <expert-advice>.
          apply Or.inl
          -- One of the premise coincides with the conclusion.
          exact h16
    case inr h22 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- One of the premise coincides with the conclusion.
      exact h22



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_91080125391883030067801212733 : (((p3 → False) ∧ (p4 ∧ ((((False ∨ p3) ∧ p4) ∨ True) ∧ ((((p3 ∧ ((p4 ∨ False) ∨ (p2 ∨ (p5 ∨ True)))) ∧ p1) ∧ True) ∧ p3)))) → p5) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- Conjunctions on the left can always be decomposed.
  let h4 := h3.left
  let h5 := h3.right
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
    cases h9
    case inl h11 =>
      -- False on the left can always be used.
      apply False.elim h11
    case inr h12 =>
      -- Conjunctions on the left can always be decomposed.
      let h13 := h7.left
      let h14 := h7.right
      -- Conjunctions on the left can always be decomposed.
      let h15 := h13.left
      let h16 := h13.right
      -- Conjunctions on the left can always be decomposed.
      let h17 := h15.left
      let h18 := h15.right
      -- Conjunctions on the left can always be decomposed.
      let h19 := h17.left
      let h20 := h17.right
      -- Disjunctions on the left can always be decomposed.
      cases h20
      case inl h21 =>
        -- Disjunctions on the left can always be decomposed.
        cases h21
        case inl h22 =>
          -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
          have h23 : p3 := by
            -- One of the premise coincides with the conclusion.
            exact h14
          -- We have shown the premise of h2, we can now drive its conclusion.
          let h24 := h2 h23
          -- False on the left can always be used.
          apply False.elim h24
        case inr h25 =>
          -- False on the left can always be used.
          apply False.elim h25
      case inr h26 =>
        -- Disjunctions on the left can always be decomposed.
        cases h26
        case inl h27 =>
          -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
          have h28 : p3 := by
            -- One of the premise coincides with the conclusion.
            exact h14
          -- We have shown the premise of h2, we can now drive its conclusion.
          let h29 := h2 h28
          -- False on the left can always be used.
          apply False.elim h29
        case inr h30 =>
          -- Disjunctions on the left can always be decomposed.
          cases h30
          case inl h31 =>
            -- One of the premise coincides with the conclusion.
            exact h31
          case inr h32 =>
            -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
            have h33 : p3 := by
              -- One of the premise coincides with the conclusion.
              exact h14
            -- We have shown the premise of h2, we can now drive its conclusion.
            let h34 := h2 h33
            -- False on the left can always be used.
            apply False.elim h34
  case inr h35 =>
    -- Conjunctions on the left can always be decomposed.
    let h36 := h7.left
    let h37 := h7.right
    -- Conjunctions on the left can always be decomposed.
    let h38 := h36.left
    let h39 := h36.right
    -- Conjunctions on the left can always be decomposed.
    let h40 := h38.left
    let h41 := h38.right
    -- Conjunctions on the left can always be decomposed.
    let h42 := h40.left
    let h43 := h40.right
    -- Disjunctions on the left can always be decomposed.
    cases h43
    case inl h44 =>
      -- Disjunctions on the left can always be decomposed.
      cases h44
      case inl h45 =>
        -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
        have h46 : p3 := by
          -- One of the premise coincides with the conclusion.
          exact h37
        -- We have shown the premise of h2, we can now drive its conclusion.
        let h47 := h2 h46
        -- False on the left can always be used.
        apply False.elim h47
      case inr h48 =>
        -- False on the left can always be used.
        apply False.elim h48
    case inr h49 =>
      -- Disjunctions on the left can always be decomposed.
      cases h49
      case inl h50 =>
        -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
        have h51 : p3 := by
          -- One of the premise coincides with the conclusion.
          exact h37
        -- We have shown the premise of h2, we can now drive its conclusion.
        let h52 := h2 h51
        -- False on the left can always be used.
        apply False.elim h52
      case inr h53 =>
        -- Disjunctions on the left can always be decomposed.
        cases h53
        case inl h54 =>
          -- One of the premise coincides with the conclusion.
          exact h54
        case inr h55 =>
          -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
          have h56 : p3 := by
            -- One of the premise coincides with the conclusion.
            exact h37
          -- We have shown the premise of h2, we can now drive its conclusion.
          let h57 := h2 h56
          -- False on the left can always be used.
          apply False.elim h57



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_609494591570663517959517936869 : (((((p1 ∧ ((p2 → ((((p4 → True) ∨ (p4 ∧ True)) ∨ (p2 → p4)) → (p5 ∨ (True ∧ p3)))) → ((False ∧ p5) ∨ p4))) ∨ True) ∨ p4) ∨ p4) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
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
theorem thm_5_vars_63169347234184923330807451810 : ((p5 ∧ ((p3 ∨ ((p1 ∧ (((False ∧ (False → (p1 ∨ True))) → (True ∧ p4)) → p5)) → (False ∧ ((True ∨ p5) ∨ True)))) ∨ (True → p3))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_11287471722649757818045547650 : (((((((p3 ∨ (((p2 ∨ (p1 ∨ p3)) ∧ ((p1 ∨ p4) → p3)) ∧ p3)) → p2) ∨ (False → False)) ∧ (True ∨ (p2 ∨ True))) → False) → p3) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h1
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h2 : ((((p3 ∨ (((p2 ∨ (p1 ∨ p3)) ∧ ((p1 ∨ p4) → p3)) ∧ p3)) → p2) ∨ (False → False)) ∧ (True ∨ (p2 ∨ True))) := by
    -- Conjunctions on the right can always be decomposed.
    apply And.intro
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h3
    -- False on the left can always be used.
    apply False.elim h3
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h4 := h1 h2
  -- False on the left can always be used.
  apply False.elim h4
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_55106336524948176801018566685 : (((p5 → (p4 ∨ ((False ∧ True) ∧ True))) ∧ (((p1 → False) ∧ p2) → ((p5 → (((p4 ∧ p3) ∧ (True ∧ (p3 ∨ p3))) ∧ p1)) ∧ p2))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_729932644431763572643638308661 : (((((p3 ∧ p5) → p4) → (p2 ∨ (False ∨ (p4 ∨ ((True ∧ (p5 ∨ (p2 → (False → False)))) ∨ ((True → (p1 ∧ p5)) ∧ (p3 ∨ p3))))))) ∨ p1) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
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
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h2
  -- Implications on the right can always be decomposed.
  intro h3
  -- False on the left can always be used.
  apply False.elim h3
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_163398647196739186727774581251 : (((p5 ∧ ((p1 ∨ False) ∨ False)) ∨ (((p1 ∨ p1) → (((True ∨ p2) ∧ True) → p1)) ∨ p4)) ∧ (((p4 ∨ (p3 ∨ True)) ∨ p3) ∨ (p2 ∧ p4))) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Conjunctions on the left can always be decomposed.
  let h3 := h2.left
  let h4 := h2.right
  -- Disjunctions on the left can always be decomposed.
  cases h3
  case inl h5 =>
    -- Disjunctions on the left can always be decomposed.
    cases h1
    case inl h6 =>
      -- One of the premise coincides with the conclusion.
      exact h6
    case inr h7 =>
      -- One of the premise coincides with the conclusion.
      exact h7
  case inr h8 =>
    -- Disjunctions on the left can always be decomposed.
    cases h1
    case inl h9 =>
      -- One of the premise coincides with the conclusion.
      exact h9
    case inr h10 =>
      -- One of the premise coincides with the conclusion.
      exact h10
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
theorem thm_5_vars_119339163870066055529984763412 : ((p3 → ((p4 → (False → (p5 ∧ p1))) → (((p5 → (p2 ∧ True)) → p2) ∨ (False ∨ ((False ∧ ((p2 ∧ True) → p5)) ∧ p4))))) ∨ (True ∨ p4)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_209554217242615136606133682429 : ((p5 → ((p4 ∨ (p1 → p5)) ∧ False)) → ((((p5 ∨ p3) ∨ (True ∨ (p4 ∨ False))) → ((p4 ∧ False) ∨ p4)) → ((p2 → (p5 → p1)) ∧ p4))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h3
  -- Implications on the right can always be decomposed.
  intro h4
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h5 : p5 := by
    -- One of the premise coincides with the conclusion.
    exact h4
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h6 := h1 h5
  -- We need to get the right conjuct of h6 based on <expert-advice>.
  let h7 := h6.right
  -- False on the left can always be used.
  apply False.elim h7
  -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
  have h8 : ((p5 ∨ p3) ∨ (True ∨ (p4 ∨ False))) := by
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h2, we can now drive its conclusion.
  let h9 := h2 h8
  -- Disjunctions on the left can always be decomposed.
  cases h9
  case inl h10 =>
    -- Conjunctions on the left can always be decomposed.
    let h11 := h10.left
    let h12 := h10.right
    -- False on the left can always be used.
    apply False.elim h12
  case inr h13 =>
    -- One of the premise coincides with the conclusion.
    exact h13



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_687589418841401382952768398745 : ((((((p5 ∧ (((p5 ∧ False) → ((p2 → p3) → True)) ∨ p3)) → (p5 ∧ p4)) → False) ∧ ((((p2 → (p5 ∧ p4)) ∨ p1) → p5) → p1)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_217950123576211658970008424047 : (((p1 ∧ True) ∧ (True ∧ p3)) → (((False ∨ (((True ∨ (True ∧ True)) ∧ (((p5 → (p1 ∨ (True ∧ p2))) → False) ∧ True)) ∧ p3)) ∨ p4) ∨ True)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- Conjunctions on the left can always be decomposed.
  let h4 := h2.left
  let h5 := h2.right
  -- Conjunctions on the left can always be decomposed.
  let h6 := h3.left
  let h7 := h3.right
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_351926420485556399926758066987 : (p4 → (((((p3 ∨ p2) → p3) ∧ (False ∨ (p5 ∨ p1))) ∧ p2) → (((p3 → p1) ∨ ((p5 ∧ False) ∨ True)) ∧ ((p5 → (True ∨ p2)) ∧ p3)))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Conjunctions on the left can always be decomposed.
  let h3 := h2.left
  let h4 := h2.right
  -- Conjunctions on the left can always be decomposed.
  let h5 := h3.left
  let h6 := h3.right
  -- Disjunctions on the left can always be decomposed.
  cases h6
  case inl h7 =>
    -- False on the left can always be used.
    apply False.elim h7
  case inr h8 =>
    -- Disjunctions on the left can always be decomposed.
    cases h8
    case inl h9 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- True on the right can always be proven directly.
      apply True.intro
    case inr h10 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- True on the right can always be proven directly.
      apply True.intro
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h11
  -- Conjunctions on the left can always be decomposed.
  let h12 := h2.left
  let h13 := h2.right
  -- Conjunctions on the left can always be decomposed.
  let h14 := h12.left
  let h15 := h12.right
  -- Disjunctions on the left can always be decomposed.
  cases h15
  case inl h16 =>
    -- False on the left can always be used.
    apply False.elim h16
  case inr h17 =>
    -- Disjunctions on the left can always be decomposed.
    cases h17
    case inl h18 =>
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- True on the right can always be proven directly.
      apply True.intro
    case inr h19 =>
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- True on the right can always be proven directly.
      apply True.intro
  -- Conjunctions on the left can always be decomposed.
  let h20 := h2.left
  let h21 := h2.right
  -- Conjunctions on the left can always be decomposed.
  let h22 := h20.left
  let h23 := h20.right
  -- Disjunctions on the left can always be decomposed.
  cases h23
  case inl h24 =>
    -- False on the left can always be used.
    apply False.elim h24
  case inr h25 =>
    -- Disjunctions on the left can always be decomposed.
    cases h25
    case inl h26 =>
      -- We want to use the implication h22 based on <expert-advice>. So we show its premise.
      have h27 : (p3 ∨ p2) := by
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- One of the premise coincides with the conclusion.
        exact h21
      -- We have shown the premise of h22, we can now drive its conclusion.
      let h28 := h22 h27
      -- One of the premise coincides with the conclusion.
      exact h28
    case inr h29 =>
      -- We want to use the implication h22 based on <expert-advice>. So we show its premise.
      have h30 : (p3 ∨ p2) := by
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- One of the premise coincides with the conclusion.
        exact h21
      -- We have shown the premise of h22, we can now drive its conclusion.
      let h31 := h22 h30
      -- One of the premise coincides with the conclusion.
      exact h31



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_190660523126451374723769826263 : (((p5 ∨ ((True → True) ∨ ((p5 ∨ False) → p1))) → False) ∨ (p5 → (((True ∧ (False ∧ p4)) → (((p1 ∧ (p3 → p2)) → p3) ∨ p5)) ∨ p3))) := by
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
  -- Conjunctions on the left can always be decomposed.
  let h5 := h4.left
  let h6 := h4.right
  -- False on the left can always be used.
  apply False.elim h5



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_165346250827109814733761923377 : ((((False ∨ (True → p4)) → ((p3 → True) ∧ (p4 → (p3 ∨ False)))) ∧ ((p3 → p3) → p5)) ∨ (p3 → ((((p4 ∨ p3) ∧ False) → p3) → True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_46580909826378720898108285653 : (((False ∧ ((((((True ∨ p1) ∧ (p3 ∨ p3)) ∧ p2) ∧ p3) ∨ (p1 ∧ ((p4 ∧ (False ∨ True)) → (p2 ∨ p3)))) ∨ p1)) ∧ (p1 → False)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_44846509269433501333494706097 : (((((p3 ∨ p3) → p4) ∨ (p2 → (p4 → ((False ∨ ((p2 ∧ (p3 ∧ p2)) ∨ (((p2 → p1) ∨ p2) ∧ (p3 ∧ p5)))) → False)))) → p1) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_336179407771978743859365070956 : (p1 → (((p5 ∨ ((((p5 ∧ p3) → (False ∧ False)) → ((p5 ∧ ((p3 → False) → (True → (p5 → False)))) ∧ (False ∨ True))) ∧ p1)) → p3) ∨ True)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_118603676762082995853146730957 : ((p4 ∨ (((p2 ∨ (p1 ∧ (p1 ∨ (p3 ∨ p4)))) ∨ (((p5 ∧ (True ∧ p4)) → (p5 ∧ p4)) ∨ p5)) ∧ ((True ∨ False) → True))) ∨ (True → p2)) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
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
  -- One of the premise coincides with the conclusion.
  exact h2
  -- Conjunctions on the left can always be decomposed.
  let h6 := h1.left
  let h7 := h1.right
  -- Conjunctions on the left can always be decomposed.
  let h8 := h7.left
  let h9 := h7.right
  -- One of the premise coincides with the conclusion.
  exact h9
  -- Implications on the right can always be decomposed.
  intro h10
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_40420854271411943704448382702 : (((((((((p4 ∧ ((False ∨ p2) ∨ p5)) ∨ False) ∧ p4) ∧ p4) ∧ (p5 → p1)) ∨ (True ∨ (True ∨ ((p3 → p3) ∨ False)))) ∨ p5) ∨ p1) ∨ False) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
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
theorem thm_5_vars_148347380644719604830122860413 : (((((p2 ∧ p1) ∨ p5) ∨ (p1 → (((True ∧ p5) ∧ p3) ∧ (p1 ∧ p2)))) ∧ ((p1 ∧ p5) ∧ (p2 ∧ p5))) ∨ ((False ∧ (p4 ∨ p5)) → p4)) := by
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
theorem thm_5_vars_300097739877701074211989699442 : (False ∨ ((((p5 ∧ (p3 ∧ (p3 ∧ ((p2 ∧ True) ∨ p3)))) ∧ (((True ∧ False) ∧ p3) → True)) ∧ (p3 → ((p1 → p3) ∨ p2))) ∨ (False → p3))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_784183576160878814966714851889 : (((p3 ∨ ((True → p5) → ((((p5 ∨ p3) ∨ (True ∧ True)) → p3) ∨ (p4 ∨ ((((False ∧ p5) ∨ ((p5 ∨ p3) → p1)) → False) ∨ True))))) ∨ p1) ∧ True) := by
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
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_673003897381079067072995215406 : ((((((p1 ∨ True) ∧ ((p1 ∧ (p2 ∧ ((p5 ∨ p1) ∨ (p5 ∨ True)))) → True)) ∨ (p4 → ((p3 ∨ False) ∨ p4))) → (p5 ∨ (False ∨ True))) ∨ p1) ∧ True) := by
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
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_137719227124627420685194237932 : ((p1 ∨ ((p5 ∨ True) ∧ (((p2 ∨ ((p2 ∧ p2) → p5)) ∨ (True ∧ ((p3 ∧ False) ∧ (p4 ∧ p2)))) ∨ (True → True)))) ∨ ((p4 → p3) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_60543725540867713326197291277 : ((True ∧ (((p1 ∧ (p1 → True)) ∨ ((p1 ∧ ((False ∧ (p1 ∨ p1)) ∧ (p2 → ((p4 ∧ p1) ∨ (p2 → p2))))) ∨ (False → p5))) ∨ p3)) ∨ False) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_640585688565938684522711285276 : (((((False ∨ p1) ∧ (p2 ∨ (((p1 → (p4 ∨ (p5 ∨ p5))) → ((False ∧ (p4 ∧ p4)) ∧ p2)) ∨ ((False → p3) ∨ (False → True))))) → p3) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_68820649337568651685450523326 : ((p4 → (((True ∧ p4) → False) ∨ (((((p5 ∨ False) → p2) ∨ (((p3 ∨ p3) ∨ (p2 → p3)) ∧ (p4 ∨ p5))) → (p5 → p4)) → p1))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_343223022272723983075066121572 : (p2 → (((p4 → p2) → False) → (((p4 ∨ (((((False ∨ p4) ∨ (p5 ∧ (((False → p5) ∧ True) → p2))) → True) → p2) ∧ p1)) ∧ p3) ∨ p5))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
  have h3 : (p4 → p2) := by
    -- Implications on the right can always be decomposed.
    intro h4
    -- One of the premise coincides with the conclusion.
    exact h1
  -- We have shown the premise of h2, we can now drive its conclusion.
  let h5 := h2 h3
  -- False on the left can always be used.
  apply False.elim h5



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_57362724193781586175316120310 : (((p4 ∧ (p2 ∧ p1)) ∨ (((p5 ∨ (False → True)) ∧ p2) ∨ ((((p4 ∨ p4) ∨ (p1 ∧ (p2 ∧ p2))) ∨ (False → (p4 → p2))) ∧ True))) ∨ False) := by
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
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- False on the left can always be used.
  apply False.elim h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_384763254342827366363073075968 : ((((((p5 ∨ p3) ∨ ((((True → ((p3 ∧ True) ∧ ((p2 ∧ p4) → ((p1 ∨ p5) ∨ False)))) → p4) ∨ (p4 → p4)) → p1)) → p4) ∨ True) ∧ True) ∧ True) := by
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
theorem thm_5_vars_114190207219624008177436202526 : ((((((p3 ∧ p1) ∧ False) ∧ ((((False ∧ False) → p3) ∨ p4) → True)) → ((p3 → p3) → (True ∨ p1))) → ((p5 → p3) → p5)) ∨ (p5 → p5)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_65286778272221690743923791162 : ((p3 ∨ ((((((p5 ∨ (False ∨ ((p3 → p5) → True))) ∧ (p4 ∨ p3)) ∧ p1) → ((p3 → (False → False)) → p4)) ∨ True) ∨ (False → True))) ∨ False) := by
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



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_807450462544356121803214982030 : (((p4 → (((True → True) → (p5 ∨ ((False ∨ p5) ∧ False))) ∨ ((p1 → ((p1 → (p3 → p3)) ∨ True)) ∧ (False → ((False ∨ False) ∧ p1))))) ∨ p1) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
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
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
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
theorem thm_5_vars_116251291720701626620498868524 : ((((p4 → p3) → False) ∨ (((p2 → (p3 ∧ (((False ∧ (True → False)) → p5) ∨ p1))) ∧ p5) ∧ (p1 → ((p3 ∨ p3) → p4)))) ∨ (True ∨ p1)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_650231586485918657522633919357 : (((((p1 ∨ ((p3 ∨ p1) ∧ ((p2 ∧ p2) → ((p2 → p3) ∧ (False ∧ (False ∧ p3)))))) ∨ ((p5 ∨ (p4 → p2)) ∨ p5)) ∧ (True → True)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_826093971815157857010506769 : ((p4 ∧ (p2 ∧ ((((False ∧ (p4 ∨ (p2 ∨ p2))) ∨ (p5 → (p4 → (True → p4)))) ∨ p4) ∧ (((p2 ∧ p1) → True) → p5)))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_610364970189974712541633375872 : (((((((p5 ∨ (p1 ∨ (((((p4 ∧ ((p3 → p1) → True)) ∧ p5) ∧ p5) → False) ∧ (p2 ∧ (p1 → p2))))) ∨ p3) → p5) → False) ∨ True) ∨ p4) ∧ True) := by
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
theorem thm_5_vars_49120976711764142723133743714 : ((((p4 ∨ ((((False ∧ False) → p3) → False) ∨ (((p1 ∨ p2) ∧ p2) → p2))) → ((p2 → p3) → (p4 ∧ p2))) ∨ (False ∧ (p4 ∨ p3))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_264536024954738731033553333250 : (True ∧ (((p5 ∧ True) ∧ p2) ∨ ((p5 ∧ ((p1 ∧ ((p1 ∨ False) ∨ ((p1 ∧ p5) → p5))) → ((True → p3) ∨ (True → p3)))) ∨ (True ∨ False)))) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_172270076385200182426999832756 : ((((((p3 ∨ p3) ∧ p3) ∧ p1) ∨ (True ∧ p4)) ∨ (((p5 → True) ∧ p1) ∧ p5)) ∨ (((False ∨ True) → p4) → ((p2 ∨ p2) ∨ (False → p3)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h2
  -- False on the left can always be used.
  apply False.elim h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_67452929773371890181381255665 : ((p1 → (((False ∧ ((p5 ∧ ((True ∧ ((p4 → p5) ∨ p2)) ∨ (p2 ∧ True))) ∨ p2)) ∧ (True → p3)) ∧ (p5 ∨ (p3 → (p3 ∨ p1))))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_180652056575749148526709470705 : (((p1 ∧ ((False ∧ (p5 ∧ p5)) ∧ p2)) ∨ (p2 ∧ ((False → True) ∨ False))) → ((((p2 → (p1 ∧ True)) ∧ (False → p3)) ∨ (p2 → p5)) ∨ p2)) := by
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
    -- Conjunctions on the left can always be decomposed.
    let h7 := h5.left
    let h8 := h5.right
    -- False on the left can always be used.
    apply False.elim h7
  case inr h9 =>
    -- Conjunctions on the left can always be decomposed.
    let h10 := h9.left
    let h11 := h9.right
    -- Disjunctions on the left can always be decomposed.
    cases h11
    case inl h12 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- One of the premise coincides with the conclusion.
      exact h10
    case inr h13 =>
      -- False on the left can always be used.
      apply False.elim h13



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_42037378585016458058506531946 : ((((p4 ∧ p3) ∨ ((p5 → p5) → ((p5 ∨ (p4 ∨ p5)) ∧ (p4 ∨ (p4 → (p3 → (p3 → ((p4 → p2) → (p5 ∧ p1))))))))) ∨ True) ∨ p1) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_234676143519740875851575921352 : ((p4 → (p2 ∧ p5)) → (p4 → ((p3 → (p1 ∧ (((p2 ∧ False) ∧ False) ∧ p1))) → ((((p5 ∧ p5) ∧ ((p1 → p3) ∧ p5)) ∧ True) ∨ p2)))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Implications on the right can always be decomposed.
  intro h3
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h4 : p4 := by
    -- One of the premise coincides with the conclusion.
    exact h2
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h5 := h1 h4
  -- We need to get the left conjuct of h5 based on <expert-advice>.
  let h6 := h5.left
  -- One of the premise coincides with the conclusion.
  exact h6



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_358580725651314073644463377413 : (p5 → (p3 → ((((p5 ∨ p5) ∧ (p1 ∨ (p4 ∧ (((p3 → (((p5 ∧ p4) ∧ (True ∧ p4)) ∨ True)) → False) ∨ p2)))) ∧ (p5 → p4)) ∨ True))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_233220538322433129426068008428 : ((p5 ∧ (p3 → True)) → (p2 → (((True → True) ∨ True) ∧ (((((False ∧ p2) → p5) ∨ ((True ∧ p5) ∧ (p4 ∧ p5))) → p1) ∨ (False → p4))))) := by
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
  -- Conjunctions on the left can always be decomposed.
  let h5 := h1.left
  let h6 := h1.right
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h7
  -- False on the left can always be used.
  apply False.elim h7



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_213164964472846523277491967380 : ((((p4 ∧ p2) ∨ p2) ∧ True) ∨ (p2 ∨ (((True → p3) ∨ ((False ∨ p5) ∨ (p3 ∧ (p1 ∧ p5)))) ∨ ((p4 ∧ ((p5 ∨ True) ∧ False)) → p1)))) := by
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
  -- Conjunctions on the left can always be decomposed.
  let h4 := h3.left
  let h5 := h3.right
  -- Disjunctions on the left can always be decomposed.
  cases h4
  case inl h6 =>
    -- False on the left can always be used.
    apply False.elim h5
  case inr h7 =>
    -- False on the left can always be used.
    apply False.elim h5



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_164525813152874517986494184696 : ((((p3 ∧ ((((False → p5) → True) ∧ p3) ∧ ((True → False) → False))) → (p1 ∧ p4)) ∧ p1) ∨ ((((True ∧ p4) → p3) ∨ (p5 → p1)) → True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_345196665850349446169776722763 : (p3 → ((True ∧ ((p4 → (p5 → (p3 ∨ (p4 → p3)))) → (((p2 → ((p4 ∨ (p2 ∧ p5)) → p4)) ∧ (p2 ∧ (p2 → p4))) ∨ p3))) ∧ p3)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- Implications on the right can always be decomposed.
  intro h2
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h1
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_232950090551441702210927532618 : ((p3 ∧ (p4 ∨ True)) → (((p5 ∨ (p4 ∨ ((p2 ∧ p4) ∨ (((False ∧ (p2 → ((p1 ∨ False) ∨ p1))) → p4) ∨ False)))) ∨ p2) ∧ (p2 → p2))) := by
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
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- One of the premise coincides with the conclusion.
    exact h4
  case inr h5 =>
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
    -- Implications on the right can always be decomposed.
    intro h6
    -- Conjunctions on the left can always be decomposed.
    let h7 := h6.left
    let h8 := h6.right
    -- False on the left can always be used.
    apply False.elim h7
  -- Implications on the right can always be decomposed.
  intro h9
  -- Conjunctions on the left can always be decomposed.
  let h10 := h1.left
  let h11 := h1.right
  -- Disjunctions on the left can always be decomposed.
  cases h11
  case inl h12 =>
    -- One of the premise coincides with the conclusion.
    exact h9
  case inr h13 =>
    -- One of the premise coincides with the conclusion.
    exact h9



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_111055685108113309367760624968 : ((((p1 ∨ ((p2 → (p1 ∧ p5)) ∧ (((p4 ∧ False) → (p3 → False)) ∧ (p2 ∨ True)))) → (((p5 ∧ p3) ∧ p5) ∨ p4)) ∧ p3) ∨ (True ∨ p5)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_468542243610803453239717593801 : (((((p3 → (False ∨ (((p2 ∨ (True ∧ p4)) ∧ p4) ∨ (p2 ∨ p3)))) ∧ p1) → (((True ∧ ((p4 → (p1 → True)) → p3)) ∧ p2) ∨ True)) ∧ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_159524313385592072163598672686 : ((((p5 → p1) → ((p5 ∨ (p4 ∧ (p2 ∨ ((True ∨ (True ∧ p4)) → (p1 ∨ p4))))) → p2)) ∧ True) → (((p4 ∨ True) → p1) ∨ (False → p1))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h4
  -- False on the left can always be used.
  apply False.elim h4



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_196977482387323223337680886511 : ((((((p1 ∨ p4) ∧ p2) → p5) → False) ∨ p3) ∨ (((p4 ∧ p5) ∨ (((p3 → p2) ∨ (False ∨ (True → p2))) → (p1 → p1))) ∨ (p1 ∧ False))) := by
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
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h3 =>
    -- One of the premise coincides with the conclusion.
    exact h2
  case inr h4 =>
    -- Disjunctions on the left can always be decomposed.
    cases h4
    case inl h5 =>
      -- False on the left can always be used.
      apply False.elim h5
    case inr h6 =>
      -- One of the premise coincides with the conclusion.
      exact h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_180936622711461894248120933440 : (((p5 ∧ p3) ∧ (((((False ∧ p5) → False) ∧ p5) ∧ True) ∨ (p4 ∧ p5))) → (((p3 ∧ (((True ∨ p1) → (p3 ∧ p5)) ∧ p3)) → False) ∨ p5)) := by
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
    -- Conjunctions on the left can always be decomposed.
    let h7 := h6.left
    let h8 := h6.right
    -- Conjunctions on the left can always be decomposed.
    let h9 := h7.left
    let h10 := h7.right
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h10
  case inr h11 =>
    -- Conjunctions on the left can always be decomposed.
    let h12 := h11.left
    let h13 := h11.right
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h13



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_138349146405553968243984802671 : ((p4 → ((p5 ∨ (p3 ∧ ((p5 → ((p5 → p4) → p3)) ∨ ((p3 ∧ (False ∨ True)) ∨ (p4 → (False → p4)))))) ∨ p4)) ∨ (p3 ∨ (p5 ∨ p3))) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_156713432994531081035942132698 : (((((True → (p5 → ((False → p4) → True))) ∧ p2) ∧ (p1 ∧ (((p2 ∧ True) ∨ False) ∨ True))) ∧ p4) ∨ (False ∨ (((False ∨ False) → p5) ∨ True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_209096339820741036775146650615 : ((p2 ∨ (((p2 → True) ∨ p5) → p3)) → (((((((p3 ∨ p4) ∧ (p2 → p4)) → ((True ∧ False) ∨ True)) ∧ p3) ∧ p2) ∨ (p2 ∨ p5)) ∨ True)) := by
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
theorem thm_5_vars_739394821247297555076635754667 : ((((p4 ∧ p5) ∨ (p2 ∧ ((True → (False ∨ (True → ((p3 → ((p5 ∨ True) → False)) ∧ (p2 ∧ ((p3 ∨ False) → (True ∧ False))))))) ∧ p1))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_612079992290009916366027218507 : ((((((p4 ∧ (((((True → False) ∨ False) → p5) → p2) ∨ (p1 ∨ (((p3 ∧ p5) ∧ p5) → p5)))) ∨ (True ∧ p2)) ∧ (p4 ∧ p3)) ∨ p3) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_112756413599858988825923691336 : (((((p2 ∧ p5) ∧ (p3 → (False → (True ∧ (True ∧ True))))) ∧ ((True ∨ ((True → True) → p4)) ∧ ((True → p4) → p2))) → p3) ∨ (p2 → p2)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_246163387435939532730647500498 : ((p4 ∧ p2) ∨ (((p1 ∧ True) → False) → (((p5 ∧ (((p1 ∧ p5) ∧ p3) ∧ True)) ∧ (p5 ∨ p3)) → (p2 ∨ ((p5 → (p1 → p5)) → p4))))) := by
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
  let h5 := h3.left
  let h6 := h3.right
  -- Conjunctions on the left can always be decomposed.
  let h7 := h6.left
  let h8 := h6.right
  -- Conjunctions on the left can always be decomposed.
  let h9 := h7.left
  let h10 := h7.right
  -- Conjunctions on the left can always be decomposed.
  let h11 := h9.left
  let h12 := h9.right
  -- Disjunctions on the left can always be decomposed.
  cases h4
  case inl h13 =>
    -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
    have h14 : (p1 ∧ True) := by
      -- Conjunctions on the right can always be decomposed.
      apply And.intro
      -- One of the premise coincides with the conclusion.
      exact h11
      -- True on the right can always be proven directly.
      apply True.intro
    -- We have shown the premise of h1, we can now drive its conclusion.
    let h15 := h1 h14
    -- False on the left can always be used.
    apply False.elim h15
  case inr h16 =>
    -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
    have h17 : (p1 ∧ True) := by
      -- Conjunctions on the right can always be decomposed.
      apply And.intro
      -- One of the premise coincides with the conclusion.
      exact h11
      -- True on the right can always be proven directly.
      apply True.intro
    -- We have shown the premise of h1, we can now drive its conclusion.
    let h18 := h1 h17
    -- False on the left can always be used.
    apply False.elim h18



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_40261658120650773669686292497 : ((((p3 ∨ (((((p4 ∨ (p1 ∨ p1)) ∧ p2) ∨ p3) ∧ (False → ((p2 ∨ p4) ∧ (p1 ∨ (False → p4))))) ∨ (p2 ∨ p1))) ∧ p1) ∨ p1) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_148774411054535131349523039803 : ((((p3 → (p3 ∧ (p2 ∧ p1))) → False) ∨ ((p2 ∨ (p4 → p1)) ∨ (((True ∨ False) ∨ (p1 → p5)) ∨ p3))) ∨ ((p1 → (p4 ∧ p2)) ∧ p4)) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
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
theorem thm_5_vars_252778854390254233545908378089 : ((True ∧ True) → ((p4 ∨ (p1 → ((False ∧ True) → True))) → (((True → ((p5 → p1) ∧ p3)) ∨ True) ∨ ((False ∨ p1) ∧ ((p3 ∨ False) ∧ p2))))) := by
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
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro
  case inr h6 =>
    -- Conjunctions on the left can always be decomposed.
    let h7 := h1.left
    let h8 := h1.right
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_312985750139388584297058502966 : (p3 ∨ (((p5 ∨ ((p2 ∧ (p1 → p1)) → ((False → ((p1 ∧ False) ∨ ((p1 → (True → p4)) → p3))) → ((p5 ∨ p4) → p4)))) ∧ False) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_56756789692906969740796268617 : ((((p3 → p2) ∨ p4) ∧ (False ∧ (((p3 ∧ p4) ∧ p5) ∨ ((((p5 ∧ p4) → (p2 → p1)) → False) ∨ ((True → p1) ∧ (False ∨ p3)))))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_629068841203723251870591162579 : (((((((p2 ∨ (p3 ∧ (((p2 ∧ (p3 → True)) ∨ ((p3 ∧ p3) → ((p1 ∨ p4) ∧ p5))) ∧ (p4 ∧ p5)))) ∧ p2) ∨ p5) ∨ False) → p1) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_60384447002092862087629553097 : (((p3 → p3) → ((((((p2 → (p2 ∨ (False ∧ p4))) ∧ (p4 ∨ ((p3 → p1) ∧ p1))) ∧ ((p2 → p3) ∧ p2)) ∧ p5) ∨ p2) ∧ p4)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_122614652638510647635217336530 : ((((((((True ∧ (p2 ∨ True)) ∧ p3) → p5) → ((p2 ∨ ((True → p2) ∨ (False ∨ p4))) ∨ True)) → False) → False) → (p5 ∧ p2)) → (p4 → p5)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h3 : ((((((True ∧ (p2 ∨ True)) ∧ p3) → p5) → ((p2 ∨ ((True → p2) ∨ (False ∨ p4))) ∨ True)) → False) → False) := by
    -- Implications on the right can always be decomposed.
    intro h4
    -- We want to use the implication h4 based on <expert-advice>. So we show its premise.
    have h5 : ((((True ∧ (p2 ∨ True)) ∧ p3) → p5) → ((p2 ∨ ((True → p2) ∨ (False ∨ p4))) ∨ True)) := by
      -- Implications on the right can always be decomposed.
      intro h6
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- True on the right can always be proven directly.
      apply True.intro
    -- We have shown the premise of h4, we can now drive its conclusion.
    let h7 := h4 h5
    -- False on the left can always be used.
    apply False.elim h7
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h8 := h1 h3
  -- We need to get the left conjuct of h8 based on <expert-advice>.
  let h9 := h8.left
  -- One of the premise coincides with the conclusion.
  exact h9



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_785901128028464254107254789276 : (((p4 ∨ (((p2 → ((True ∧ p4) ∧ (p5 ∨ p4))) ∨ ((((p3 → (False → False)) ∧ (p3 ∧ p2)) ∧ p4) ∧ (p2 ∨ p3))) ∧ (p3 ∧ p5))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_148297907171848789120434848592 : ((((p4 → ((p1 ∧ (p3 ∧ p2)) ∨ True)) ∨ ((p3 ∧ ((p1 ∧ p4) ∨ False)) → p5)) → ((p3 ∧ p5) ∨ p4)) ∨ ((p2 ∨ False) ∨ (True → True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_241846752883344902766316875351 : ((p1 → p1) ∧ (((False ∨ (p3 ∨ p4)) ∧ (p2 ∨ p3)) ∨ ((False → True) ∨ ((p5 ∧ (p3 ∧ ((p5 ∧ p2) → (p4 ∧ p5)))) → (p3 → p4))))) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h1
  -- One of the premise coincides with the conclusion.
  exact h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h2
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_681913952873197698959290760082 : ((((((False ∨ ((False → ((p4 → p3) → (False → ((p1 ∧ True) ∧ p2)))) ∧ p5)) ∧ p4) ∨ p2) ∧ (((p1 → False) → p4) ∨ (False ∨ p2))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_52891436728098344168864830222 : (((p3 ∨ ((False ∨ False) → (((p4 ∧ True) → ((False ∧ p1) ∧ p5)) ∧ True))) → (p5 ∨ ((p1 ∧ ((p1 ∨ p1) ∨ True)) → (True ∨ p5)))) ∨ p1) := by
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
    -- Conjunctions on the left can always be decomposed.
    let h4 := h3.left
    let h5 := h3.right
    -- Disjunctions on the left can always be decomposed.
    cases h5
    case inl h6 =>
      -- Disjunctions on the left can always be decomposed.
      cases h6
      case inl h7 =>
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- True on the right can always be proven directly.
        apply True.intro
      case inr h8 =>
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- True on the right can always be proven directly.
        apply True.intro
    case inr h9 =>
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- True on the right can always be proven directly.
      apply True.intro
  case inr h10 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h11
    -- Conjunctions on the left can always be decomposed.
    let h12 := h11.left
    let h13 := h11.right
    -- Disjunctions on the left can always be decomposed.
    cases h13
    case inl h14 =>
      -- Disjunctions on the left can always be decomposed.
      cases h14
      case inl h15 =>
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- True on the right can always be proven directly.
        apply True.intro
      case inr h16 =>
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- True on the right can always be proven directly.
        apply True.intro
    case inr h17 =>
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- True on the right can always be proven directly.
      apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_462659067274808315193134455673 : ((((((((p5 ∨ (p5 ∧ p1)) → False) → (p1 ∨ p5)) → ((False ∨ False) → p1)) → p5) ∨ (((p5 → (p2 ∨ (p5 ∨ p4))) ∧ p4) → p4)) ∧ True) ∧ True) := by
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
  -- One of the premise coincides with the conclusion.
  exact h3
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_624117434939718787065471746420 : ((((p2 ∨ (False ∧ ((((((False ∧ p5) ∧ (p1 ∧ (True ∨ (p1 ∧ True)))) ∨ True) ∨ (True ∧ ((p4 → p2) ∨ p2))) ∨ p2) → p5))) ∨ p2) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_136572947861790973590919547164 : ((((False → p1) → p3) ∨ (((p4 → p2) ∨ (False ∨ ((p4 → (p2 → (p1 ∧ p2))) ∨ (True → False)))) ∧ (False → p5))) ∨ (p1 ∨ (False → p2))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_234240136973515845584708848393 : ((False → (p2 ∨ p2)) → (((p4 → (p3 → (((((p3 ∨ p2) ∧ True) → p2) → True) → ((p2 ∨ False) ∨ (p5 → (p3 ∧ p4)))))) → False) → p1)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
  have h3 : (p4 → (p3 → (((((p3 ∨ p2) ∧ True) → p2) → True) → ((p2 ∨ False) ∨ (p5 → (p3 ∧ p4)))))) := by
    -- Implications on the right can always be decomposed.
    intro h4
    -- Implications on the right can always be decomposed.
    intro h5
    -- Implications on the right can always be decomposed.
    intro h6
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h7
    -- Conjunctions on the right can always be decomposed.
    apply And.intro
    -- One of the premise coincides with the conclusion.
    exact h5
    -- One of the premise coincides with the conclusion.
    exact h4
  -- We have shown the premise of h2, we can now drive its conclusion.
  let h8 := h2 h3
  -- False on the left can always be used.
  apply False.elim h8



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_191931688781122417261166992939 : ((True → (((p1 → (p5 → p2)) ∧ False) ∧ (p5 ∨ False))) ∨ (((True → (p2 ∧ (False ∨ True))) ∧ ((((True ∧ p4) ∧ p3) ∨ p3) ∨ p1)) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_184779403473463439453480679625 : (((((p3 ∨ p1) → False) ∨ p3) ∨ ((True ∨ (p2 ∧ p5)) → p2)) ∨ ((((False ∨ (p2 → p2)) ∨ (p1 ∨ p5)) ∨ (p1 ∧ (p4 → p2))) ∨ p4)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
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
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_191116228233671521440938353174 : (((p1 ∨ (p5 ∨ True)) ∧ (((p4 → False) → p5) ∧ p1)) ∨ (True ∨ (((p5 ∨ ((p3 ∧ (True ∨ p3)) → False)) ∧ (True → (p4 ∧ p2))) → False))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_763002294590323827330715998602 : (((p3 ∧ ((p1 ∧ ((p3 ∨ p5) → p1)) → ((p3 ∧ (((False ∧ p1) → p1) ∧ p2)) → (((((p4 → p3) ∧ p1) ∨ p2) ∨ p5) → p5)))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_49286647137509248785314337348 : (((p5 ∧ ((((p2 → (((False ∨ (((p2 → (p2 → p5)) ∨ p5) ∨ p5)) ∨ p3) ∧ p5)) → p1) → p5) → p4)) ∨ (p1 ∨ (p1 ∧ p5))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_643835584860681547743881002055 : ((((p5 ∧ ((p3 ∧ p4) → (p5 → (((((p3 → (p1 → (False ∧ p4))) ∨ p5) ∧ p4) → (p2 → (p5 ∧ p3))) → (p3 ∧ False))))) → p4) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_701002160102640737570975535839 : (((((p2 → (((p4 ∨ True) → (p3 → p1)) ∨ p4)) ∨ True) ∧ (((((p1 ∨ (p3 ∧ ((p5 ∧ True) ∧ p2))) ∨ True) ∨ p1) → False) ∨ p3)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_248038444468467559469641679104 : ((p1 ∨ p5) ∨ (((p2 ∨ ((p4 ∨ False) → p1)) ∨ ((p1 ∧ p5) ∨ True)) ∨ ((((((p4 → False) ∧ p2) ∧ p2) ∧ (p5 → p2)) ∨ p3) ∧ True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_710149707246455798406978793284 : ((((((p1 ∨ (p2 ∧ p4)) ∨ True) ∨ False) ∧ ((False → True) ∧ (((p1 ∧ (((p1 ∧ (p5 ∨ p2)) → (True ∨ False)) ∨ p4)) ∧ True) ∨ False))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_164835868105600388058794506235 : (((p1 ∧ (((p3 ∧ False) ∨ (p1 ∧ (p3 → (False ∧ True)))) ∨ (p1 ∧ (False ∧ p3)))) ∨ p5) ∨ (((p3 ∧ p3) → ((p5 ∧ p1) → p1)) ∧ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
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
  -- One of the premise coincides with the conclusion.
  exact h4
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_229760836080431195517432877580 : ((p4 → (p3 ∨ p5)) ∨ (((((p4 → p5) → (p4 ∧ False)) ∨ (((True → ((p2 → p5) ∨ p2)) ∧ p2) ∧ ((True ∨ True) → p1))) ∨ True) ∨ p3)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_308856044218123314974386529161 : (p2 ∨ ((((p4 ∧ (p5 ∧ True)) → ((p5 ∧ ((p2 ∨ True) ∨ (p5 ∨ (p3 ∨ p3)))) ∧ (False ∨ (p2 ∨ (p3 ∨ (p1 ∨ p5)))))) → p5) → p5)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h2 : ((p4 ∧ (p5 ∧ True)) → ((p5 ∧ ((p2 ∨ True) ∨ (p5 ∨ (p3 ∨ p3)))) ∧ (False ∨ (p2 ∨ (p3 ∨ (p1 ∨ p5)))))) := by
    -- Implications on the right can always be decomposed.
    intro h3
    -- Conjunctions on the right can always be decomposed.
    apply And.intro
    -- Conjunctions on the right can always be decomposed.
    apply And.intro
    -- Conjunctions on the left can always be decomposed.
    let h4 := h3.left
    let h5 := h3.right
    -- Conjunctions on the left can always be decomposed.
    let h6 := h5.left
    let h7 := h5.right
    -- One of the premise coincides with the conclusion.
    exact h6
    -- Conjunctions on the left can always be decomposed.
    let h8 := h3.left
    let h9 := h3.right
    -- Conjunctions on the left can always be decomposed.
    let h10 := h9.left
    let h11 := h9.right
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro
    -- Conjunctions on the left can always be decomposed.
    let h12 := h3.left
    let h13 := h3.right
    -- Conjunctions on the left can always be decomposed.
    let h14 := h13.left
    let h15 := h13.right
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h14
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h16 := h1 h2
  -- One of the premise coincides with the conclusion.
  exact h16



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_360925776308196147004671987272 : ((((((((True ∨ ((True ∨ (p4 ∨ p2)) ∧ ((p1 ∧ (False → (False ∨ (p5 ∧ p4)))) → p4))) ∨ False) → (p3 ∨ p1)) ∨ p2) ∨ True) ∧ True) ∧ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
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
  -- True on the right can always be proven directly.
  apply True.intro



