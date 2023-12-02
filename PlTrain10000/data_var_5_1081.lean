variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_168710363087136505232669043989 : ((True ∨ (((((True ∧ False) ∧ False) → (p1 ∧ p4)) → p4) ∨ ((p3 ∨ p4) ∧ (p1 → p3)))) → (p3 ∨ (p4 → (p1 → (p4 → (True → p1)))))) := by
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
    -- Implications on the right can always be decomposed.
    intro h5
    -- Implications on the right can always be decomposed.
    intro h6
    -- One of the premise coincides with the conclusion.
    exact h4
  case inr h7 =>
    -- Disjunctions on the left can always be decomposed.
    cases h7
    case inl h8 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Implications on the right can always be decomposed.
      intro h9
      -- Implications on the right can always be decomposed.
      intro h10
      -- Implications on the right can always be decomposed.
      intro h11
      -- Implications on the right can always be decomposed.
      intro h12
      -- One of the premise coincides with the conclusion.
      exact h10
    case inr h13 =>
      -- Conjunctions on the left can always be decomposed.
      let h14 := h13.left
      let h15 := h13.right
      -- Disjunctions on the left can always be decomposed.
      cases h14
      case inl h16 =>
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- One of the premise coincides with the conclusion.
        exact h16
      case inr h17 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- Implications on the right can always be decomposed.
        intro h18
        -- Implications on the right can always be decomposed.
        intro h19
        -- Implications on the right can always be decomposed.
        intro h20
        -- Implications on the right can always be decomposed.
        intro h21
        -- One of the premise coincides with the conclusion.
        exact h19



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_202032946035819149986919485902 : ((((p1 ∧ (p4 ∨ True)) ∧ p3) → p1) ∧ ((p3 ∨ (p3 → (((True ∨ p3) → ((False ∧ p1) ∧ (p3 ∨ True))) ∨ ((p5 → True) ∨ True)))) ∨ p5)) := by
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
    -- One of the premise coincides with the conclusion.
    exact h4
  case inr h7 =>
    -- One of the premise coincides with the conclusion.
    exact h4
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h8
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_52525637359797606324715549291 : ((((((p1 ∨ ((p5 → False) → p4)) ∧ (True ∧ (p1 ∧ p1))) → False) ∨ p2) ∨ (((p4 ∨ False) → True) → ((True ∨ p4) ∨ (p3 ∨ True)))) ∨ p3) := by
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
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_657293199845961694107064757428 : (((((p2 ∧ False) ∧ ((p4 → ((((p1 → True) ∨ (p1 → True)) ∧ p2) ∨ (p2 ∨ (p1 → ((p1 → p3) ∧ True))))) ∨ True)) ∨ (p3 → p2)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_310322633066516680046661142604 : (p2 ∨ ((((p3 ∨ p2) ∨ ((True ∧ p4) ∧ (False ∨ p5))) ∨ True) → (False ∨ (((p3 ∨ p2) → (True ∧ (((p5 ∧ p2) → p1) → p1))) ∨ True)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
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
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- True on the right can always be proven directly.
        apply True.intro
      case inr h5 =>
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
      -- Conjunctions on the left can always be decomposed.
      let h9 := h7.left
      let h10 := h7.right
      -- Disjunctions on the left can always be decomposed.
      cases h8
      case inl h11 =>
        -- False on the left can always be used.
        apply False.elim h11
      case inr h12 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- True on the right can always be proven directly.
        apply True.intro
  case inr h13 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_113746514611231219903640676928 : (((((p2 ∨ (True ∧ (p1 ∨ ((p4 ∨ (p1 ∨ True)) → False)))) → p1) → ((p3 → True) ∧ (p5 ∧ (p2 ∧ p4)))) → (p2 ∧ p2)) ∨ (True ∧ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_137821070565730419731070754325 : ((p3 ∨ (((((True ∨ (p2 ∨ p1)) ∨ False) → (p1 ∨ (((((p5 ∨ p1) → p1) → True) ∨ True) ∧ False))) ∧ True) → False)) ∨ (p1 → (True → p1))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_257262338222862516419316194343 : ((p2 ∨ p3) → (((True → p4) ∨ ((p4 ∨ (((True → p1) ∨ p3) ∧ True)) ∧ ((p2 ∧ p3) ∨ (False → (p4 ∨ p3))))) → (p5 ∨ (False → p1)))) := by
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
    -- Conjunctions on the left can always be decomposed.
    let h9 := h8.left
    let h10 := h8.right
    -- Disjunctions on the left can always be decomposed.
    cases h9
    case inl h11 =>
      -- Disjunctions on the left can always be decomposed.
      cases h10
      case inl h12 =>
        -- Conjunctions on the left can always be decomposed.
        let h13 := h12.left
        let h14 := h12.right
        -- Disjunctions on the left can always be decomposed.
        cases h1
        case inl h15 =>
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- Implications on the right can always be decomposed.
          intro h16
          -- False on the left can always be used.
          apply False.elim h16
        case inr h17 =>
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- Implications on the right can always be decomposed.
          intro h18
          -- False on the left can always be used.
          apply False.elim h18
      case inr h19 =>
        -- Disjunctions on the left can always be decomposed.
        cases h1
        case inl h20 =>
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- Implications on the right can always be decomposed.
          intro h21
          -- False on the left can always be used.
          apply False.elim h21
        case inr h22 =>
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- Implications on the right can always be decomposed.
          intro h23
          -- False on the left can always be used.
          apply False.elim h23
    case inr h24 =>
      -- Conjunctions on the left can always be decomposed.
      let h25 := h24.left
      let h26 := h24.right
      -- Disjunctions on the left can always be decomposed.
      cases h25
      case inl h27 =>
        -- Disjunctions on the left can always be decomposed.
        cases h10
        case inl h28 =>
          -- Conjunctions on the left can always be decomposed.
          let h29 := h28.left
          let h30 := h28.right
          -- Disjunctions on the left can always be decomposed.
          cases h1
          case inl h31 =>
            -- Show the right disjunct based on <expert-advice>.
            apply Or.inr
            -- Implications on the right can always be decomposed.
            intro h32
            -- False on the left can always be used.
            apply False.elim h32
          case inr h33 =>
            -- Show the right disjunct based on <expert-advice>.
            apply Or.inr
            -- Implications on the right can always be decomposed.
            intro h34
            -- False on the left can always be used.
            apply False.elim h34
        case inr h35 =>
          -- Disjunctions on the left can always be decomposed.
          cases h1
          case inl h36 =>
            -- Show the right disjunct based on <expert-advice>.
            apply Or.inr
            -- Implications on the right can always be decomposed.
            intro h37
            -- False on the left can always be used.
            apply False.elim h37
          case inr h38 =>
            -- Show the right disjunct based on <expert-advice>.
            apply Or.inr
            -- Implications on the right can always be decomposed.
            intro h39
            -- False on the left can always be used.
            apply False.elim h39
      case inr h40 =>
        -- Disjunctions on the left can always be decomposed.
        cases h10
        case inl h41 =>
          -- Conjunctions on the left can always be decomposed.
          let h42 := h41.left
          let h43 := h41.right
          -- Disjunctions on the left can always be decomposed.
          cases h1
          case inl h44 =>
            -- Show the right disjunct based on <expert-advice>.
            apply Or.inr
            -- Implications on the right can always be decomposed.
            intro h45
            -- False on the left can always be used.
            apply False.elim h45
          case inr h46 =>
            -- Show the right disjunct based on <expert-advice>.
            apply Or.inr
            -- Implications on the right can always be decomposed.
            intro h47
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
            -- False on the left can always be used.
            apply False.elim h50
          case inr h51 =>
            -- Show the right disjunct based on <expert-advice>.
            apply Or.inr
            -- Implications on the right can always be decomposed.
            intro h52
            -- False on the left can always be used.
            apply False.elim h52



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_233033881771099226791323833833 : ((p4 ∧ (p4 ∧ p5)) → ((p1 ∨ ((p3 ∨ True) ∧ p4)) → ((p4 → p2) → ((p2 ∧ ((p4 ∨ True) ∨ p2)) ∧ (((False ∨ False) ∨ p2) ∨ True))))) := by
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
  -- Disjunctions on the left can always be decomposed.
  cases h2
  case inl h4 =>
    -- Conjunctions on the left can always be decomposed.
    let h5 := h1.left
    let h6 := h1.right
    -- Conjunctions on the left can always be decomposed.
    let h7 := h6.left
    let h8 := h6.right
    -- We want to use the implication h3 based on <expert-advice>. So we show its premise.
    have h9 : p4 := by
      -- One of the premise coincides with the conclusion.
      exact h7
    -- We have shown the premise of h3, we can now drive its conclusion.
    let h10 := h3 h9
    -- One of the premise coincides with the conclusion.
    exact h10
  case inr h11 =>
    -- Conjunctions on the left can always be decomposed.
    let h12 := h11.left
    let h13 := h11.right
    -- Disjunctions on the left can always be decomposed.
    cases h12
    case inl h14 =>
      -- Conjunctions on the left can always be decomposed.
      let h15 := h1.left
      let h16 := h1.right
      -- Conjunctions on the left can always be decomposed.
      let h17 := h16.left
      let h18 := h16.right
      -- We want to use the implication h3 based on <expert-advice>. So we show its premise.
      have h19 : p4 := by
        -- One of the premise coincides with the conclusion.
        exact h17
      -- We have shown the premise of h3, we can now drive its conclusion.
      let h20 := h3 h19
      -- One of the premise coincides with the conclusion.
      exact h20
    case inr h21 =>
      -- Conjunctions on the left can always be decomposed.
      let h22 := h1.left
      let h23 := h1.right
      -- Conjunctions on the left can always be decomposed.
      let h24 := h23.left
      let h25 := h23.right
      -- We want to use the implication h3 based on <expert-advice>. So we show its premise.
      have h26 : p4 := by
        -- One of the premise coincides with the conclusion.
        exact h24
      -- We have shown the premise of h3, we can now drive its conclusion.
      let h27 := h3 h26
      -- One of the premise coincides with the conclusion.
      exact h27
  -- Disjunctions on the left can always be decomposed.
  cases h2
  case inl h28 =>
    -- Conjunctions on the left can always be decomposed.
    let h29 := h1.left
    let h30 := h1.right
    -- Conjunctions on the left can always be decomposed.
    let h31 := h30.left
    let h32 := h30.right
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- One of the premise coincides with the conclusion.
    exact h31
  case inr h33 =>
    -- Conjunctions on the left can always be decomposed.
    let h34 := h33.left
    let h35 := h33.right
    -- Disjunctions on the left can always be decomposed.
    cases h34
    case inl h36 =>
      -- Conjunctions on the left can always be decomposed.
      let h37 := h1.left
      let h38 := h1.right
      -- Conjunctions on the left can always be decomposed.
      let h39 := h38.left
      let h40 := h38.right
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- One of the premise coincides with the conclusion.
      exact h39
    case inr h41 =>
      -- Conjunctions on the left can always be decomposed.
      let h42 := h1.left
      let h43 := h1.right
      -- Conjunctions on the left can always be decomposed.
      let h44 := h43.left
      let h45 := h43.right
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- One of the premise coincides with the conclusion.
      exact h44
  -- Disjunctions on the left can always be decomposed.
  cases h2
  case inl h46 =>
    -- Conjunctions on the left can always be decomposed.
    let h47 := h1.left
    let h48 := h1.right
    -- Conjunctions on the left can always be decomposed.
    let h49 := h48.left
    let h50 := h48.right
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro
  case inr h51 =>
    -- Conjunctions on the left can always be decomposed.
    let h52 := h51.left
    let h53 := h51.right
    -- Disjunctions on the left can always be decomposed.
    cases h52
    case inl h54 =>
      -- Conjunctions on the left can always be decomposed.
      let h55 := h1.left
      let h56 := h1.right
      -- Conjunctions on the left can always be decomposed.
      let h57 := h56.left
      let h58 := h56.right
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- True on the right can always be proven directly.
      apply True.intro
    case inr h59 =>
      -- Conjunctions on the left can always be decomposed.
      let h60 := h1.left
      let h61 := h1.right
      -- Conjunctions on the left can always be decomposed.
      let h62 := h61.left
      let h63 := h61.right
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- True on the right can always be proven directly.
      apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_247922093055875967229358058226 : ((p1 ∨ p3) ∨ (((False ∨ p1) ∧ (p3 → p5)) → (((p3 → p3) → (((p3 ∧ False) ∧ (((p5 ∧ p5) → (False → p3)) ∧ True)) ∧ p3)) → p3))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
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
    -- False on the left can always be used.
    apply False.elim h5
  case inr h6 =>
    -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
    have h7 : (p3 → p3) := by
      -- Implications on the right can always be decomposed.
      intro h8
      -- One of the premise coincides with the conclusion.
      exact h8
    -- We have shown the premise of h2, we can now drive its conclusion.
    let h9 := h2 h7
    -- We need to get the left conjuct of h9 based on <expert-advice>.
    let h10 := h9.left
    -- We need to get the left conjuct of h10 based on <expert-advice>.
    let h11 := h10.left
    -- We need to get the right conjuct of h11 based on <expert-advice>.
    let h12 := h11.right
    -- False on the left can always be used.
    apply False.elim h12



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_136178446930424368386723190477 : ((((p2 → ((True ∧ p3) → True)) ∨ p5) ∧ ((True → True) ∧ ((((p1 → True) → (p4 → p5)) ∨ p2) → (p3 ∧ p3)))) ∨ (False → (p4 → p1))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_321112455348481499069541513843 : (p4 ∨ (p2 ∨ (((False ∧ p4) ∧ (((p4 ∨ (p1 ∨ p3)) ∨ (p1 → (False ∧ (p5 → (((p2 ∨ True) → p4) ∧ (True ∧ False)))))) ∨ p3)) ∨ True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_309367196917831021995797484595 : (p2 ∨ (((p2 ∨ (p2 → p2)) ∧ ((p3 ∨ p3) → (p1 → ((((True ∨ p3) ∨ True) → ((p4 ∨ p4) ∨ (p3 ∧ p4))) ∨ p1)))) ∨ (p1 ∧ False))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- One of the premise coincides with the conclusion.
  exact h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Implications on the right can always be decomposed.
  intro h3
  -- Disjunctions on the left can always be decomposed.
  cases h2
  case inl h4 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h3
  case inr h5 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h3



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_193281852562330176478932366060 : ((((p5 → False) ∧ p4) ∨ (((p4 ∧ False) → False) → p1)) → (((((p5 → p1) → p1) → ((False ∧ (False → True)) ∨ p4)) ∨ p1) ∨ (p2 ∧ p1))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h2 =>
    -- Conjunctions on the left can always be decomposed.
    let h3 := h2.left
    let h4 := h2.right
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Implications on the right can always be decomposed.
    intro h5
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h4
  case inr h6 =>
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- We want to use the implication h6 based on <expert-advice>. So we show its premise.
    have h7 : ((p4 ∧ False) → False) := by
      -- Implications on the right can always be decomposed.
      intro h8
      -- Conjunctions on the left can always be decomposed.
      let h9 := h8.left
      let h10 := h8.right
      -- False on the left can always be used.
      apply False.elim h10
    -- We have shown the premise of h6, we can now drive its conclusion.
    let h11 := h6 h7
    -- One of the premise coincides with the conclusion.
    exact h11



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_264568980235906483312907079481 : (True ∧ ((False ∧ (p5 → True)) ∨ ((p4 → ((((((p2 ∧ False) → (p2 ∧ False)) ∨ True) → (p3 → p2)) ∧ (p4 → p2)) ∧ (True → False))) ∨ True))) := by
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
theorem thm_5_vars_185028498578407773150872080495 : (((p5 ∨ p3) ∧ ((False → (p4 ∨ p1)) → (p5 ∧ (p5 ∨ False)))) ∨ (((p5 ∧ False) → p1) → (((False → p4) → (p2 ∨ (True ∨ p5))) ∨ p4))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h2
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_43637154046062222637570293498 : (((((((p3 ∧ p2) ∧ True) ∧ (((p4 ∧ p2) ∨ p5) ∧ ((p2 ∧ (p3 ∨ ((p5 ∨ p4) ∧ p3))) → True))) ∨ (p3 ∧ p3)) → False) → p4) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_341885549722442175397422115786 : (p2 → ((p1 → ((p2 ∧ (p5 ∨ (p2 ∨ (p5 → (p4 ∧ ((False → (p1 ∧ p2)) → (p1 ∧ (p3 → (False ∨ False))))))))) → p4)) → (p4 → p4))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Implications on the right can always be decomposed.
  intro h3
  -- One of the premise coincides with the conclusion.
  exact h3



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_54682135580136091713669427325 : (((((p5 ∨ p2) ∧ ((p2 → True) ∧ p3)) → p3) → (((p1 ∧ ((((p2 → p2) ∧ False) → ((True ∨ p4) ∧ True)) ∨ p2)) ∨ p2) ∨ False)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_319166471633061091204964379440 : (p4 ∨ (((p1 ∨ (p2 → ((p3 ∧ (p5 ∨ p5)) ∨ (p1 → ((p5 ∧ p1) ∧ False))))) ∨ (p1 ∧ p3)) ∨ ((p2 → True) ∧ ((p1 → True) ∨ p5)))) := by
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
  -- Implications on the right can always be decomposed.
  intro h2
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_178635501191476612252045762392 : ((((True ∨ p1) → (p1 ∧ (False → p5))) → ((p5 → True) ∧ (p5 ∧ p5))) ∨ ((p1 ∨ ((p1 ∨ ((True → False) ∧ (p5 ∨ p3))) ∨ True)) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_40736643855433418315839534706 : (((((p2 → ((p5 → False) ∧ False)) → (((p1 → p3) ∨ ((p3 ∨ p2) ∧ ((p3 ∨ p2) ∧ True))) → (True → (p5 → p4)))) → p4) ∨ p3) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_198089664750691008344633934945 : (((p5 ∨ p5) ∨ ((p2 ∨ (p5 ∧ p1)) ∨ p3)) ∨ (((((p5 ∧ (p1 ∧ (p5 → p2))) ∨ True) ∧ ((p3 ∧ p1) → False)) ∧ (p2 ∨ p3)) → True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_244311200939352593222406245463 : ((False ∧ False) ∨ ((((p1 → False) ∨ ((p1 ∧ p3) → ((p4 ∧ p1) ∨ (p2 ∧ p4)))) ∧ (False → (p2 ∨ ((True ∨ (p4 → False)) → p5)))) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_21524900235744029462867222050 : ((((p3 → p5) → ((p5 ∨ (True ∧ (False ∧ p1))) ∨ p1)) ∨ (((p2 ∨ (False ∧ p2)) ∧ ((((p4 ∨ p2) → False) ∧ p3) ∨ False)) → p2)) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
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
      -- One of the premise coincides with the conclusion.
      exact h4
    case inr h8 =>
      -- False on the left can always be used.
      apply False.elim h8
  case inr h9 =>
    -- Conjunctions on the left can always be decomposed.
    let h10 := h9.left
    let h11 := h9.right
    -- False on the left can always be used.
    apply False.elim h10
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_656967096101883213627683530289 : ((((((p2 ∧ (p3 ∧ p3)) → p3) → (p4 ∨ ((p4 ∨ (p5 ∨ True)) ∧ (((p1 ∨ p2) ∧ (p2 ∨ True)) → (False ∨ True))))) ∨ (p1 ∧ p1)) ∨ p5) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
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
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- Implications on the right can always be decomposed.
  intro h2
  -- Conjunctions on the left can always be decomposed.
  let h3 := h2.left
  let h4 := h2.right
  -- Disjunctions on the left can always be decomposed.
  cases h3
  case inl h5 =>
    -- Disjunctions on the left can always be decomposed.
    cases h4
    case inl h6 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- True on the right can always be proven directly.
      apply True.intro
    case inr h7 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- True on the right can always be proven directly.
      apply True.intro
  case inr h8 =>
    -- Disjunctions on the left can always be decomposed.
    cases h4
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
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_150159001874082146921051261360 : ((p1 → ((p3 → ((p3 → (p2 → ((p2 ∨ (p5 ∧ p4)) → False))) → False)) ∧ ((p5 ∨ (True → p1)) → p3))) ∨ (p2 ∨ ((p5 ∧ False) ∨ True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_116770497776617138470218997699 : (((False ∨ False) ∨ (((((False ∨ p5) ∨ p3) ∧ ((p4 ∨ ((p5 ∨ p1) → p3)) → ((True → (p4 ∨ p1)) ∨ p4))) → p2) → p3)) ∨ (False → p1)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_225686842776939223398448739928 : (((p3 → False) ∧ p1) ∨ ((p5 ∨ ((p3 ∧ True) ∧ (p5 → p4))) ∨ ((((False → p5) → (p5 → p2)) ∨ (p3 → ((False → p2) ∨ p5))) ∨ p1))) := by
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
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h2
  -- False on the left can always be used.
  apply False.elim h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_258461220738716708891663733360 : ((p5 ∨ p2) → (((p1 ∧ ((((False ∨ ((p1 ∨ p3) ∨ p3)) ∧ p5) ∧ p2) → p5)) ∧ (((False ∧ p4) ∧ False) ∧ (p3 → (False ∨ True)))) ∨ True)) := by
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
theorem thm_5_vars_37554489254453628744664953373 : ((((p1 ∨ ((True → (p2 ∨ ((p3 → (p5 ∨ (True → False))) ∧ (p1 → (p4 ∧ p4))))) ∨ (True ∨ ((p3 ∨ p5) ∨ p4)))) ∨ p1) ∧ p5) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_189275182238841302625395007142 : (((True ∨ p2) → ((p5 ∧ (p3 ∧ (p4 ∨ p3))) ∨ True)) ∧ (False ∨ (((True ∨ p4) ∨ p4) ∨ (((((p1 ∧ p1) → True) ∧ p3) ∧ p1) ∨ p4)))) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
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
theorem thm_5_vars_314548484340754086358919721490 : (p3 ∨ ((((((p4 ∨ p1) ∧ p5) ∧ (p3 ∨ False)) ∧ True) ∨ (((p4 → p1) ∨ p2) ∨ (p2 → p3))) ∨ ((p3 ∧ p3) ∨ ((True ∨ p3) ∨ p3)))) := by
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
theorem thm_5_vars_53873888454833144305165039750 : ((((p3 ∧ p5) ∨ (p5 ∨ ((True → p5) ∧ (p1 → p5)))) ∨ ((True ∨ p3) → (p2 → ((p2 ∧ (p3 → ((p3 → False) ∨ p3))) ∨ p4)))) ∨ p1) := by
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
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Conjunctions on the right can always be decomposed.
    apply And.intro
    -- One of the premise coincides with the conclusion.
    exact h2
    -- Implications on the right can always be decomposed.
    intro h4
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h4
  case inr h5 =>
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Conjunctions on the right can always be decomposed.
    apply And.intro
    -- One of the premise coincides with the conclusion.
    exact h2
    -- Implications on the right can always be decomposed.
    intro h6
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h6



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_204601447320332354330219849652 : ((((p4 → p2) ∨ (p5 ∧ p5)) ∨ p3) ∨ ((((True → (p5 ∧ p2)) ∨ p1) ∧ (False ∨ p3)) ∨ ((p3 ∨ (True ∨ (p3 ∨ (False → p5)))) ∨ p4))) := by
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
theorem thm_5_vars_229524955880747248819204208100 : ((p2 → (p3 ∨ p5)) ∨ (((True ∧ p5) ∨ (p1 → (((False ∨ False) ∨ (False → True)) ∨ True))) ∧ (p4 ∨ (((p2 → p1) → (p5 → True)) ∨ p5)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
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
theorem thm_5_vars_38442108447110405367443451079 : ((((True ∧ (p3 ∨ (p3 ∨ (p1 ∧ (True ∧ (False ∧ (p5 → (p2 ∧ p1)))))))) ∨ ((p3 → (p4 → ((p2 ∧ p5) ∨ p1))) ∧ p2)) ∧ p3) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_196682517251010785456120151323 : (((((p1 ∧ (p3 ∧ False)) ∨ p3) ∨ p4) ∧ True) ∨ (p3 ∨ (False → (True → ((p4 ∧ (p2 ∨ False)) → ((p3 ∧ ((True → p5) ∨ p5)) → p4)))))) := by
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
  -- Implications on the right can always be decomposed.
  intro h4
  -- Conjunctions on the left can always be decomposed.
  let h5 := h4.left
  let h6 := h4.right
  -- Disjunctions on the left can always be decomposed.
  cases h6
  case inl h7 =>
    -- Conjunctions on the left can always be decomposed.
    let h8 := h3.left
    let h9 := h3.right
    -- Disjunctions on the left can always be decomposed.
    cases h9
    case inl h10 =>
      -- False on the left can always be used.
      apply False.elim h1
    case inr h11 =>
      -- False on the left can always be used.
      apply False.elim h11
  case inr h12 =>
    -- Conjunctions on the left can always be decomposed.
    let h13 := h3.left
    let h14 := h3.right
    -- Disjunctions on the left can always be decomposed.
    cases h14
    case inl h15 =>
      -- False on the left can always be used.
      apply False.elim h1
    case inr h16 =>
      -- False on the left can always be used.
      apply False.elim h16



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_165073657538049745688068497492 : (((p4 ∧ (p2 ∧ ((((False → (True → False)) ∨ p3) → (p3 → p4)) ∨ (p1 ∨ p2)))) → False) ∨ ((p3 → ((p5 ∨ (p2 ∧ p1)) ∧ p5)) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_705066717661645870378170961386 : ((((p4 → (((p2 ∨ (p2 ∧ p4)) ∧ (p3 ∧ p3)) ∧ p4)) → (((((p1 ∨ p3) ∧ (p2 ∨ p3)) ∨ p5) ∧ p4) ∨ (False → (p1 → False)))) ∨ p2) ∧ True) := by
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
  -- Implications on the right can always be decomposed.
  intro h3
  -- False on the left can always be used.
  apply False.elim h2
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_112055777403464741847231956705 : ((((p2 ∧ p2) ∧ (((True ∨ (((((p3 ∨ p4) ∨ True) ∨ p5) ∨ True) ∧ (((True ∨ p1) → p5) ∨ False))) ∨ p4) → p5)) ∨ True) ∨ (p5 ∧ False)) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_394242797885354490109045766044 : (((((p4 ∧ p5) → ((p4 → (False → p2)) ∧ (((p3 ∧ (((p4 ∧ (p2 → ((p1 → p5) ∨ True))) ∧ p5) ∧ p2)) ∧ p2) → p1))) ∨ True) ∧ True) ∧ True) := by
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
theorem thm_5_vars_773218470757566737786872616284 : (((False ∨ ((((p1 ∧ p1) ∧ (p1 ∧ ((False ∨ (((p4 ∧ p1) ∧ False) → (False ∨ p2))) ∧ (p4 → (False → True))))) ∨ (p1 → False)) ∧ p3)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_313069648554800475196497776501 : (p3 ∨ (((((True ∧ (((((p3 ∨ p5) ∨ p4) ∧ p4) ∧ p3) ∨ (((False ∧ p2) ∨ (True ∧ p2)) → p3))) → p4) ∨ p3) ∧ (p3 → p3)) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_113420590720962692878352085817 : ((((((p1 ∨ True) ∨ True) → ((p4 → p1) → (p2 ∨ ((p3 ∨ (((p2 ∧ p1) ∨ True) → p4)) ∧ p2)))) ∧ p1) ∨ (False → p2)) ∨ (p3 ∧ p1)) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_347972153103568315750986115300 : (p3 → ((p1 → p1) ∧ (p3 ∧ (p1 ∨ (((p4 → p1) ∨ ((((True → ((False ∨ (True ∧ (True → p5))) → False)) ∨ p4) ∨ p4) ∨ p3)) ∨ False))))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h2
  -- One of the premise coincides with the conclusion.
  exact h2
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- One of the premise coincides with the conclusion.
  exact h1
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
theorem thm_5_vars_141414456813588955362735265132 : (((p3 ∨ (p5 → (True ∨ False))) → (((p4 ∧ p2) ∨ ((True → (True ∨ p5)) ∨ (p1 ∧ (True ∧ (False ∧ p4))))) ∧ False)) → ((p5 → p4) → p4)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h3 : (p3 ∨ (p5 → (True ∨ False))) := by
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h4
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h5 := h1 h3
  -- We need to get the right conjuct of h5 based on <expert-advice>.
  let h6 := h5.right
  -- False on the left can always be used.
  apply False.elim h6



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_783771527944157186310721703712 : (((p3 ∨ ((p3 ∧ (False ∧ (p2 ∧ p3))) ∧ (((((p3 ∧ ((p5 ∨ p4) ∨ ((p4 ∧ True) ∧ False))) → True) → p3) ∧ p5) ∨ (p4 → False)))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_728260766447189013643369543415 : ((((True → (p5 → p4)) ∨ ((p1 ∨ (False → ((p3 ∨ True) ∧ (p4 ∧ (p4 → ((p3 ∧ p2) → (p5 → (p1 → (p2 → p3))))))))) → p3)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_709111892783276906216885261509 : ((((((True ∧ p1) ∧ p5) → ((p4 ∧ True) ∨ False)) → (p2 ∧ (p2 → (p5 ∨ (p5 ∧ (True → ((True ∨ p4) → ((p5 → p4) ∨ p1)))))))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_8305702197088956374448172775 : (((((((p4 → False) ∧ (p5 → ((((p1 ∧ (False ∧ False)) ∨ True) ∧ True) → (p3 ∧ p2)))) → (p3 → p4)) → (p1 ∧ p5)) → p4) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_258888785595581544785408012182 : ((True → p2) → ((True → (((((((p2 → p4) ∨ p4) → p5) ∨ ((p3 ∨ (p2 ∨ True)) ∨ False)) → ((p5 → False) ∧ p5)) ∨ p4) ∧ p3)) ∨ True)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_178329863069442090080219687612 : ((((False ∨ ((p5 ∧ p1) → p1)) ∧ (p4 ∨ (p5 ∧ False))) ∨ (p3 ∧ True)) ∨ (p1 → ((p5 ∧ (True ∨ (True → ((p1 → p5) → p2)))) → True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_53302554597175713522761154038 : (((p4 ∨ ((p2 ∨ (((p1 ∨ p3) ∨ p4) ∨ (True ∨ p4))) ∨ p5)) ∨ ((p4 ∧ ((p3 ∧ (p3 ∧ p5)) → p3)) → (p2 → (p1 → p4)))) ∨ False) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
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
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_166712257458892907697822943294 : ((p3 → (((p4 ∨ (p1 ∨ (p3 ∧ p2))) ∧ (True → p5)) ∧ (False ∨ ((p2 → p4) ∨ p2)))) ∨ (((True ∧ False) ∧ p1) → ((p2 ∧ p2) ∨ True))) := by
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
theorem thm_5_vars_117888699476879994273170848942 : ((p5 ∧ (((((True ∧ True) ∨ ((p5 ∧ (p5 ∨ ((p5 ∨ p5) ∨ (p2 ∨ p5)))) → p4)) ∨ (p5 ∨ p2)) → p2) ∨ (False ∧ True))) ∨ (False → p2)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_300972383379225155542117764083 : (False ∨ (((p3 ∧ True) → (((p2 → ((p4 → p2) ∧ p3)) → p4) ∧ p2)) ∨ ((p2 ∧ (p3 ∨ p4)) → ((p4 → (p4 ∨ (False ∧ p5))) ∨ p2)))) := by
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
  cases h3
  case inl h4 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h2
  case inr h5 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_741706396788589175090701844297 : ((((True → p1) ∨ ((True → ((((True ∧ p1) → (p2 → (True ∧ p4))) ∧ True) → p2)) → (p4 ∧ (((p1 ∧ p2) ∨ (p2 → p1)) ∨ p5)))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_19061305404155546943202447985 : ((((((((p2 → p5) ∨ (p1 ∨ (p5 ∧ (False → p3)))) ∧ p2) ∨ p4) ∨ p1) ∧ (p2 ∧ p5)) → ((p4 ∨ p4) ∨ (p2 ∧ (True ∨ p5)))) ∧ True) := by
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
      -- Conjunctions on the left can always be decomposed.
      let h6 := h5.left
      let h7 := h5.right
      -- Disjunctions on the left can always be decomposed.
      cases h6
      case inl h8 =>
        -- Conjunctions on the left can always be decomposed.
        let h9 := h3.left
        let h10 := h3.right
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- Conjunctions on the right can always be decomposed.
        apply And.intro
        -- One of the premise coincides with the conclusion.
        exact h9
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- True on the right can always be proven directly.
        apply True.intro
      case inr h11 =>
        -- Disjunctions on the left can always be decomposed.
        cases h11
        case inl h12 =>
          -- Conjunctions on the left can always be decomposed.
          let h13 := h3.left
          let h14 := h3.right
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- Conjunctions on the right can always be decomposed.
          apply And.intro
          -- One of the premise coincides with the conclusion.
          exact h13
          -- Show the left disjunct based on <expert-advice>.
          apply Or.inl
          -- True on the right can always be proven directly.
          apply True.intro
        case inr h15 =>
          -- Conjunctions on the left can always be decomposed.
          let h16 := h15.left
          let h17 := h15.right
          -- Conjunctions on the left can always be decomposed.
          let h18 := h3.left
          let h19 := h3.right
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- Conjunctions on the right can always be decomposed.
          apply And.intro
          -- One of the premise coincides with the conclusion.
          exact h18
          -- Show the left disjunct based on <expert-advice>.
          apply Or.inl
          -- True on the right can always be proven directly.
          apply True.intro
    case inr h20 =>
      -- Conjunctions on the left can always be decomposed.
      let h21 := h3.left
      let h22 := h3.right
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- One of the premise coincides with the conclusion.
      exact h20
  case inr h23 =>
    -- Conjunctions on the left can always be decomposed.
    let h24 := h3.left
    let h25 := h3.right
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Conjunctions on the right can always be decomposed.
    apply And.intro
    -- One of the premise coincides with the conclusion.
    exact h24
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- True on the right can always be proven directly.
    apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_698485813035067679985043280943 : (((((((False ∧ False) ∨ (p4 → False)) → p5) → (p3 → (True ∧ False))) ∨ (p1 ∨ (((p5 ∨ (p1 ∨ p4)) → (p3 ∧ False)) ∨ (p4 → p3)))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_349938703832848638169675980433 : (p4 → ((((((((True ∨ (False ∨ (p3 → p4))) → p3) ∨ ((p3 ∧ (((p2 → p3) ∧ p4) ∧ p1)) ∨ p5)) ∨ False) ∨ p4) ∨ p4) ∧ False) ∨ p4)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_112672951281233860524282538471 : (((((p3 ∧ (p5 ∨ ((p1 ∧ p5) ∨ ((False → (p2 → (p5 ∨ (False ∧ p3)))) ∧ p3)))) ∨ False) → ((p5 ∧ p2) → p5)) → p5) ∨ (True ∨ p4)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_173123274122517381825043774379 : ((p2 ∨ ((p3 ∨ p5) ∧ (((False ∨ p4) ∨ False) ∨ (((p3 ∧ p2) → p2) → p2)))) ∨ ((False ∧ p4) → (True ∧ ((p5 → (p1 ∨ True)) → p3)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- Implications on the right can always be decomposed.
  intro h2
  -- Conjunctions on the left can always be decomposed.
  let h3 := h1.left
  let h4 := h1.right
  -- False on the left can always be used.
  apply False.elim h3



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_255504312436627028669782704207 : ((p5 ∧ p2) → ((False ∨ (p2 ∧ ((True → (p3 ∨ (p1 ∧ False))) ∧ (((p4 ∨ p4) ∧ p4) ∧ p3)))) ∨ (((p5 ∨ p5) → p2) ∧ (p5 → p5)))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h4
  -- Disjunctions on the left can always be decomposed.
  cases h4
  case inl h5 =>
    -- One of the premise coincides with the conclusion.
    exact h3
  case inr h6 =>
    -- One of the premise coincides with the conclusion.
    exact h3
  -- Implications on the right can always be decomposed.
  intro h7
  -- One of the premise coincides with the conclusion.
  exact h7



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_733038300693567479398784525655 : ((((p2 ∧ p5) ∧ ((True → (((True → False) ∨ ((p4 ∨ ((p3 ∨ (p2 → p4)) → (p1 ∨ p2))) ∨ p4)) ∨ (p3 ∧ (p4 → False)))) → p2)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_303525864158646346752355878743 : (p1 ∨ ((((p2 ∨ (p1 ∧ p1)) ∧ False) ∨ (((True → ((True ∨ ((p1 ∨ p4) ∨ p5)) ∧ p1)) → (p4 ∧ p3)) → ((False ∧ p5) → p2))) ∧ True)) := by
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
  -- Conjunctions on the left can always be decomposed.
  let h3 := h2.left
  let h4 := h2.right
  -- False on the left can always be used.
  apply False.elim h3
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_200352229997036804092445859383 : (((True → False) ∧ ((True → (p4 ∧ p2)) ∨ p4)) → ((p4 → (p3 ∧ (p4 ∨ (p3 ∧ (p3 ∨ ((p1 → False) ∨ (False ∧ p3))))))) ∧ (p2 ∧ p3))) := by
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
  -- Disjunctions on the left can always be decomposed.
  cases h4
  case inl h5 =>
    -- We want to use the implication h3 based on <expert-advice>. So we show its premise.
    have h6 : True := by
      -- True on the right can always be proven directly.
      apply True.intro
    -- We have shown the premise of h3, we can now drive its conclusion.
    let h7 := h3 h6
    -- False on the left can always be used.
    apply False.elim h7
  case inr h8 =>
    -- We want to use the implication h3 based on <expert-advice>. So we show its premise.
    have h9 : True := by
      -- True on the right can always be proven directly.
      apply True.intro
    -- We have shown the premise of h3, we can now drive its conclusion.
    let h10 := h3 h9
    -- False on the left can always be used.
    apply False.elim h10
  -- Conjunctions on the left can always be decomposed.
  let h11 := h1.left
  let h12 := h1.right
  -- Disjunctions on the left can always be decomposed.
  cases h12
  case inl h13 =>
    -- We want to use the implication h11 based on <expert-advice>. So we show its premise.
    have h14 : True := by
      -- True on the right can always be proven directly.
      apply True.intro
    -- We have shown the premise of h11, we can now drive its conclusion.
    let h15 := h11 h14
    -- False on the left can always be used.
    apply False.elim h15
  case inr h16 =>
    -- We want to use the implication h11 based on <expert-advice>. So we show its premise.
    have h17 : True := by
      -- True on the right can always be proven directly.
      apply True.intro
    -- We have shown the premise of h11, we can now drive its conclusion.
    let h18 := h11 h17
    -- False on the left can always be used.
    apply False.elim h18
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Conjunctions on the left can always be decomposed.
  let h19 := h1.left
  let h20 := h1.right
  -- Disjunctions on the left can always be decomposed.
  cases h20
  case inl h21 =>
    -- We want to use the implication h21 based on <expert-advice>. So we show its premise.
    have h22 : True := by
      -- True on the right can always be proven directly.
      apply True.intro
    -- We have shown the premise of h21, we can now drive its conclusion.
    let h23 := h21 h22
    -- We need to get the right conjuct of h23 based on <expert-advice>.
    let h24 := h23.right
    -- One of the premise coincides with the conclusion.
    exact h24
  case inr h25 =>
    -- We want to use the implication h19 based on <expert-advice>. So we show its premise.
    have h26 : True := by
      -- True on the right can always be proven directly.
      apply True.intro
    -- We have shown the premise of h19, we can now drive its conclusion.
    let h27 := h19 h26
    -- False on the left can always be used.
    apply False.elim h27
  -- Conjunctions on the left can always be decomposed.
  let h28 := h1.left
  let h29 := h1.right
  -- Disjunctions on the left can always be decomposed.
  cases h29
  case inl h30 =>
    -- We want to use the implication h28 based on <expert-advice>. So we show its premise.
    have h31 : True := by
      -- True on the right can always be proven directly.
      apply True.intro
    -- We have shown the premise of h28, we can now drive its conclusion.
    let h32 := h28 h31
    -- False on the left can always be used.
    apply False.elim h32
  case inr h33 =>
    -- We want to use the implication h28 based on <expert-advice>. So we show its premise.
    have h34 : True := by
      -- True on the right can always be proven directly.
      apply True.intro
    -- We have shown the premise of h28, we can now drive its conclusion.
    let h35 := h28 h34
    -- False on the left can always be used.
    apply False.elim h35



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_46659731388085119834871022171 : (((False ∨ (((p2 ∨ ((p4 ∨ p3) ∧ (((p4 → ((p1 ∨ p5) → False)) ∧ p1) → p3))) → (True → p2)) ∧ (False → p1))) ∧ (True ∨ p2)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_336126501356922135527962532801 : (p1 → (((((p2 ∧ p2) ∨ (p4 ∧ (False ∧ p1))) ∨ (((p4 → p3) ∧ ((p3 → (((p2 ∧ p1) ∨ False) ∨ p4)) ∨ True)) ∨ True)) ∨ p4) ∨ p2)) := by
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
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_134341733462673796787094745364 : (((p4 ∧ (True → ((((p3 → p1) ∨ False) → (((p3 ∨ p5) ∨ (p2 → p3)) → (p3 ∧ (p5 ∧ p5)))) ∨ p4))) ∨ p5) ∨ (p1 → (True ∨ True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_856423322783431383450405162899 : (((((((p1 → (p5 ∨ ((p4 ∨ p2) → p2))) ∧ p3) → ((p4 ∧ ((((p5 ∧ p4) ∧ p2) ∨ (p5 ∨ False)) → p1)) ∨ p3)) ∨ p4) → p2) → p2) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h1
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h2 : ((((p1 → (p5 ∨ ((p4 ∨ p2) → p2))) ∧ p3) → ((p4 ∧ ((((p5 ∧ p4) ∧ p2) ∨ (p5 ∨ False)) → p1)) ∨ p3)) ∨ p4) := by
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Implications on the right can always be decomposed.
    intro h3
    -- Conjunctions on the left can always be decomposed.
    let h4 := h3.left
    let h5 := h3.right
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h5
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h6 := h1 h2
  -- One of the premise coincides with the conclusion.
  exact h6
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_175207603290796510822119066825 : ((False ∨ ((p1 → p5) → ((((p3 → True) ∧ p5) ∨ p4) → (p5 ∨ (p2 → False))))) → ((((p4 ∨ ((p2 → p5) ∧ p5)) ∧ p4) ∨ p3) ∨ True)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h2 =>
    -- False on the left can always be used.
    apply False.elim h2
  case inr h3 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_158004169316715519453276935062 : (((p1 → (((False → (p4 → p1)) → True) ∨ p5)) → ((((p4 ∧ p2) ∨ False) ∧ p1) ∧ (True ∧ p2))) ∨ (True → (p5 ∨ ((p3 → p2) ∨ True)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_207491940998749463661957970277 : (((p4 → ((p2 ∨ p3) ∨ p4)) ∨ p4) → (p2 → ((((p2 ∧ True) ∨ (p3 ∧ (((((False ∧ p3) → True) ∨ p2) → p4) ∨ True))) → False) → p1))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Implications on the right can always be decomposed.
  intro h3
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h4 =>
    -- We want to use the implication h3 based on <expert-advice>. So we show its premise.
    have h5 : ((p2 ∧ True) ∨ (p3 ∧ (((((False ∧ p3) → True) ∨ p2) → p4) ∨ True))) := by
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- Conjunctions on the right can always be decomposed.
      apply And.intro
      -- One of the premise coincides with the conclusion.
      exact h2
      -- True on the right can always be proven directly.
      apply True.intro
    -- We have shown the premise of h3, we can now drive its conclusion.
    let h6 := h3 h5
    -- False on the left can always be used.
    apply False.elim h6
  case inr h7 =>
    -- We want to use the implication h3 based on <expert-advice>. So we show its premise.
    have h8 : ((p2 ∧ True) ∨ (p3 ∧ (((((False ∧ p3) → True) ∨ p2) → p4) ∨ True))) := by
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- Conjunctions on the right can always be decomposed.
      apply And.intro
      -- One of the premise coincides with the conclusion.
      exact h2
      -- True on the right can always be proven directly.
      apply True.intro
    -- We have shown the premise of h3, we can now drive its conclusion.
    let h9 := h3 h8
    -- False on the left can always be used.
    apply False.elim h9



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_183945145589812532048309852270 : (((p2 ∨ (p1 ∧ (p3 ∧ ((p5 ∨ (p5 ∧ p4)) ∨ p1)))) ∧ p4) ∨ (False → ((False ∨ p1) ∧ (p1 → (False → ((False ∧ True) ∨ (p2 ∨ p2))))))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- False on the left can always be used.
  apply False.elim h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Implications on the right can always be decomposed.
  intro h3
  -- False on the left can always be used.
  apply False.elim h3



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_450846270890079552756497619677 : (((((((p2 ∧ False) ∧ (False ∧ ((False ∨ (False → ((False ∧ (False ∨ p4)) ∧ p2))) → p5))) ∧ True) ∨ p3) ∨ ((p2 ∧ p4) ∨ (False → p3))) ∧ True) ∧ True) := by
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
  -- False on the left can always be used.
  apply False.elim h1
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_238151526650935263418429561606 : ((True ∨ p3) ∧ ((p1 ∨ p4) → (((((p3 ∧ ((((p4 ∧ p1) ∨ p1) → p5) ∧ (p1 ∨ p2))) ∨ False) → (p1 ∨ p4)) → (p5 → p4)) ∨ p1))) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro
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
    -- Implications on the right can always be decomposed.
    intro h5
    -- One of the premise coincides with the conclusion.
    exact h3



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_117009475258501462523008791725 : (((False ∨ p4) → (p5 → ((p3 ∨ ((p2 → p4) → False)) ∧ ((False ∧ p1) ∧ (((False ∨ p1) → (p1 ∨ (True ∨ p2))) ∧ p4))))) ∨ (p4 → True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_112060954275523616617403434318 : ((((False ∨ p2) ∧ ((((p3 ∨ p2) ∨ (p1 ∧ (((p3 → p1) ∧ p1) ∧ (False ∧ ((p5 ∨ True) ∧ p4))))) ∨ p4) ∨ p5)) ∨ p2) ∨ (p4 → p4)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_809248552920991923483915993192 : (((p5 → (((p5 → ((p1 → p2) → (p1 ∧ (p4 ∧ ((p3 ∨ p1) ∧ True))))) → ((p4 ∨ (((p4 → p4) ∧ p2) → p3)) → p3)) ∨ p2)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_119442527283920836014544756293 : ((p4 → ((p1 ∨ (((p3 → p5) → p5) ∧ ((p1 → p3) ∨ (p3 ∨ p3)))) ∧ (((p3 → ((p5 → False) → True)) ∨ p1) ∨ True))) ∨ (p5 → p5)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_197099961432460004872055018401 : (((p4 ∧ (p2 ∧ ((p2 ∨ p2) → p1))) ∨ p4) ∨ (((((p2 ∨ True) ∧ p1) ∨ ((p4 → (p2 ∨ False)) → p2)) ∨ (True ∨ p1)) ∧ (True ∨ p1))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_354636081239153059763353500654 : (p5 → (((p5 → (((True ∨ (p4 ∧ ((False ∨ True) ∨ (((False → p1) ∧ p5) ∧ (p4 ∨ p1))))) → p2) ∨ ((p4 ∧ p2) ∧ p3))) ∨ p1) ∨ p5)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_51095148733076897617503101258 : ((((((p2 → (True → (((p3 ∧ p1) ∧ False) ∨ p5))) → p3) → ((True ∨ True) → False)) ∧ p3) ∨ (p3 ∨ ((False ∧ True) ∨ (p5 → True)))) ∨ p1) := by
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
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_248889088513324472640097886665 : ((p3 ∨ p5) ∨ (((p1 ∨ (p4 ∧ (p2 ∨ p2))) ∨ ((p1 ∧ p1) → p2)) → (p5 ∨ (p3 → (p1 → (p1 → ((False → True) → (True ∨ p1)))))))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
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
      -- Implications on the right can always be decomposed.
      intro h5
      -- Implications on the right can always be decomposed.
      intro h6
      -- Implications on the right can always be decomposed.
      intro h7
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- True on the right can always be proven directly.
      apply True.intro
    case inr h8 =>
      -- Conjunctions on the left can always be decomposed.
      let h9 := h8.left
      let h10 := h8.right
      -- Disjunctions on the left can always be decomposed.
      cases h10
      case inl h11 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- Implications on the right can always be decomposed.
        intro h12
        -- Implications on the right can always be decomposed.
        intro h13
        -- Implications on the right can always be decomposed.
        intro h14
        -- Implications on the right can always be decomposed.
        intro h15
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- True on the right can always be proven directly.
        apply True.intro
      case inr h16 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- Implications on the right can always be decomposed.
        intro h17
        -- Implications on the right can always be decomposed.
        intro h18
        -- Implications on the right can always be decomposed.
        intro h19
        -- Implications on the right can always be decomposed.
        intro h20
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- True on the right can always be proven directly.
        apply True.intro
  case inr h21 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h22
    -- Implications on the right can always be decomposed.
    intro h23
    -- Implications on the right can always be decomposed.
    intro h24
    -- Implications on the right can always be decomposed.
    intro h25
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- True on the right can always be proven directly.
    apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_257864706520080668566182852977 : ((p4 ∨ True) → ((((((p5 ∧ (p1 ∨ p3)) ∨ ((False ∨ p4) → p4)) ∨ (p2 ∧ True)) ∧ (p2 ∨ p4)) ∨ ((p4 ∧ p3) → p3)) ∨ (False → False))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h2 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h3
    -- False on the left can always be used.
    apply False.elim h3
  case inr h4 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h5
    -- False on the left can always be used.
    apply False.elim h5



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_117106120598886769580649523514 : (((p2 → p3) → ((p2 ∨ ((p1 ∨ True) ∨ (((p5 → True) ∧ ((False ∨ p3) ∧ (p2 ∧ True))) ∨ p3))) ∧ ((p2 ∧ p5) ∨ p2))) ∨ (False → p3)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_149512328487179383633445543344 : ((p1 ∧ (((True → p3) ∨ p4) ∧ ((((p3 ∨ p4) ∨ (p5 ∨ p5)) ∨ False) ∧ (True → ((p4 ∨ p5) ∨ p4))))) ∨ ((False ∨ True) ∨ (p5 ∧ p2))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_778323784196603229887267943551 : (((p1 ∨ (False ∧ (p2 ∧ ((((p5 ∨ p4) ∨ ((p3 → p2) ∨ True)) → (((p3 ∧ ((p3 ∨ p2) ∨ p3)) → True) → p1)) ∧ (p1 ∧ p1))))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_125708174575798584670082894586 : (((p1 ∨ True) ∨ (False ∨ (((p4 ∨ ((False → (False ∨ p4)) ∨ ((((p2 → p2) ∨ p2) ∨ (p3 → p2)) → p3))) ∨ p1) ∧ p1))) → (p3 ∨ True)) := by
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
      -- True on the right can always be proven directly.
      apply True.intro
    case inr h4 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- True on the right can always be proven directly.
      apply True.intro
  case inr h5 =>
    -- Disjunctions on the left can always be decomposed.
    cases h5
    case inl h6 =>
      -- False on the left can always be used.
      apply False.elim h6
    case inr h7 =>
      -- Conjunctions on the left can always be decomposed.
      let h8 := h7.left
      let h9 := h7.right
      -- Disjunctions on the left can always be decomposed.
      cases h8
      case inl h10 =>
        -- Disjunctions on the left can always be decomposed.
        cases h10
        case inl h11 =>
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- True on the right can always be proven directly.
          apply True.intro
        case inr h12 =>
          -- Disjunctions on the left can always be decomposed.
          cases h12
          case inl h13 =>
            -- Show the right disjunct based on <expert-advice>.
            apply Or.inr
            -- True on the right can always be proven directly.
            apply True.intro
          case inr h14 =>
            -- Show the right disjunct based on <expert-advice>.
            apply Or.inr
            -- True on the right can always be proven directly.
            apply True.intro
      case inr h15 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- True on the right can always be proven directly.
        apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_60358691833091122388731929843 : (((p2 → p5) → ((((True ∨ ((p2 → p2) → p4)) → ((p1 ∧ (p4 ∧ p3)) → (p3 ∨ True))) → p1) → ((p2 ∨ (p1 ∧ True)) ∧ True))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_52962688535301788911710652904 : ((((((p1 ∨ p2) ∧ (True ∨ ((p3 ∨ p1) → p2))) ∧ p2) → False) ∧ (((p1 → False) ∧ p2) ∧ (((False → p2) → (p3 ∨ False)) ∧ False))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_51162015315544946445851436288 : ((((((((p3 ∨ p4) → p3) → p1) ∧ ((p3 → p3) → (p5 ∨ p1))) → p5) ∧ (p1 ∨ p4)) ∨ (((p5 ∧ (p5 → p1)) → p2) ∧ p3)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_260069368817757032908012469856 : ((p2 → False) → (((p3 ∨ p5) ∧ p4) ∨ (((p2 ∨ (p2 ∨ p3)) → (p4 ∨ ((p2 → p3) ∨ ((True → p5) ∧ (p3 → p2))))) ∨ (p4 → p3)))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h2
  -- Disjunctions on the left can always be decomposed.
  cases h2
  case inl h3 =>
    -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
    have h4 : p2 := by
      -- One of the premise coincides with the conclusion.
      exact h3
    -- We have shown the premise of h1, we can now drive its conclusion.
    let h5 := h1 h4
    -- False on the left can always be used.
    apply False.elim h5
  case inr h6 =>
    -- Disjunctions on the left can always be decomposed.
    cases h6
    case inl h7 =>
      -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
      have h8 : p2 := by
        -- One of the premise coincides with the conclusion.
        exact h7
      -- We have shown the premise of h1, we can now drive its conclusion.
      let h9 := h1 h8
      -- False on the left can always be used.
      apply False.elim h9
    case inr h10 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- Implications on the right can always be decomposed.
      intro h11
      -- One of the premise coincides with the conclusion.
      exact h10



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_49011760330931697634095093424 : ((((((True → (p3 ∨ ((p5 ∨ p4) ∨ ((p5 ∨ (p1 → ((p4 ∨ p4) → p2))) ∧ False)))) ∧ p5) → True) → False) ∨ (p1 ∧ (p2 ∨ p4))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_313957310359078317596697215620 : (p3 ∨ (((False ∨ (((p3 ∧ (p2 ∨ p2)) → (p5 ∨ ((True ∨ (False → (p2 → (False → p5)))) ∨ p3))) → p4)) ∨ (p2 → p2)) ∨ (p5 ∧ p2))) := by
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
theorem thm_5_vars_165646427604847303045603121863 : ((((((False ∧ p4) → p5) → p1) ∧ p2) ∨ ((True ∨ p4) → (p2 ∨ (False → (p3 → p4))))) ∨ ((True ∧ True) ∨ ((p1 ∨ (p2 → p3)) ∨ True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_264810863455839111344372623887 : (True ∧ ((p3 ∧ p5) ∨ (((p3 ∧ (p4 ∧ p3)) ∧ (p4 → ((p2 → (p3 → (p1 ∧ p2))) ∧ False))) → ((p4 ∨ p3) ∧ ((p5 → p5) → p2))))) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- True on the right can always be proven directly.
  apply True.intro
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
  let h6 := h5.left
  let h7 := h5.right
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- One of the premise coincides with the conclusion.
  exact h6
  -- Implications on the right can always be decomposed.
  intro h8
  -- Conjunctions on the left can always be decomposed.
  let h9 := h1.left
  let h10 := h1.right
  -- Conjunctions on the left can always be decomposed.
  let h11 := h9.left
  let h12 := h9.right
  -- Conjunctions on the left can always be decomposed.
  let h13 := h12.left
  let h14 := h12.right
  -- We want to use the implication h10 based on <expert-advice>. So we show its premise.
  have h15 : p4 := by
    -- One of the premise coincides with the conclusion.
    exact h13
  -- We have shown the premise of h10, we can now drive its conclusion.
  let h16 := h10 h15
  -- We need to get the right conjuct of h16 based on <expert-advice>.
  let h17 := h16.right
  -- False on the left can always be used.
  apply False.elim h17



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_156112217288150937692517693262 : ((False ∨ ((p1 ∨ (p1 ∧ ((False ∧ (p5 → (p4 ∨ ((p4 → (p2 ∨ p2)) → p1)))) ∧ p3))) ∨ True)) ∧ ((False ∨ (True ∨ (p4 → p5))) ∨ p4)) := by
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
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_49068376641305371289219804923 : ((((p1 ∧ (((p5 ∧ p3) ∨ (((p5 ∧ ((True ∨ (p3 → True)) ∨ p2)) → p3) → p4)) ∨ p4)) ∨ (False ∨ p1)) ∨ (p2 ∧ (p4 ∧ p3))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



