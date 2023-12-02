variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_50466005032825300008253426935 : (((True → ((p2 ∨ (((p3 ∧ p3) ∨ (p5 ∧ (True ∨ ((p3 ∨ p3) ∧ p1)))) → p1)) ∧ (p2 ∨ p5))) ∨ (p3 ∧ ((p4 → False) ∧ True))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_58836928263047103091990097261 : (((True ∧ False) ∨ (p5 ∧ (((((p2 ∧ (p3 → False)) ∨ (False ∧ (((False ∨ False) ∨ p3) ∧ ((p1 → p5) → p2)))) ∧ p2) ∨ p3) → p1))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_142905524504869058424647786428 : ((p5 ∨ ((p3 ∨ (((p4 ∧ ((((p2 → p5) ∧ p1) → (p5 → (p3 ∧ p4))) ∨ True)) ∧ (p2 ∨ True)) → False)) ∧ p3)) → ((p1 → p4) ∨ True)) := by
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
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- True on the right can always be proven directly.
      apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_207338819682842075784194119661 : ((((p2 ∨ True) ∨ (p3 ∧ True)) ∨ False) → ((p2 ∧ (True → (p1 ∨ (p2 ∧ ((p4 ∨ p1) ∨ p1))))) → (False ∨ (p1 ∨ ((p3 → p1) ∨ p4))))) := by
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
    -- Disjunctions on the left can always be decomposed.
    cases h5
    case inl h6 =>
      -- Disjunctions on the left can always be decomposed.
      cases h6
      case inl h7 =>
        -- We want to use the implication h4 based on <expert-advice>. So we show its premise.
        have h8 : True := by
          -- True on the right can always be proven directly.
          apply True.intro
        -- We have shown the premise of h4, we can now drive its conclusion.
        let h9 := h4 h8
        -- Disjunctions on the left can always be decomposed.
        cases h9
        case inl h10 =>
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- Show the left disjunct based on <expert-advice>.
          apply Or.inl
          -- One of the premise coincides with the conclusion.
          exact h10
        case inr h11 =>
          -- Conjunctions on the left can always be decomposed.
          let h12 := h11.left
          let h13 := h11.right
          -- Disjunctions on the left can always be decomposed.
          cases h13
          case inl h14 =>
            -- Disjunctions on the left can always be decomposed.
            cases h14
            case inl h15 =>
              -- Show the right disjunct based on <expert-advice>.
              apply Or.inr
              -- Show the right disjunct based on <expert-advice>.
              apply Or.inr
              -- Show the right disjunct based on <expert-advice>.
              apply Or.inr
              -- One of the premise coincides with the conclusion.
              exact h15
            case inr h16 =>
              -- Show the right disjunct based on <expert-advice>.
              apply Or.inr
              -- Show the left disjunct based on <expert-advice>.
              apply Or.inl
              -- One of the premise coincides with the conclusion.
              exact h16
          case inr h17 =>
            -- Show the right disjunct based on <expert-advice>.
            apply Or.inr
            -- Show the left disjunct based on <expert-advice>.
            apply Or.inl
            -- One of the premise coincides with the conclusion.
            exact h17
      case inr h18 =>
        -- We want to use the implication h4 based on <expert-advice>. So we show its premise.
        have h19 : True := by
          -- True on the right can always be proven directly.
          apply True.intro
        -- We have shown the premise of h4, we can now drive its conclusion.
        let h20 := h4 h19
        -- Disjunctions on the left can always be decomposed.
        cases h20
        case inl h21 =>
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- Show the left disjunct based on <expert-advice>.
          apply Or.inl
          -- One of the premise coincides with the conclusion.
          exact h21
        case inr h22 =>
          -- Conjunctions on the left can always be decomposed.
          let h23 := h22.left
          let h24 := h22.right
          -- Disjunctions on the left can always be decomposed.
          cases h24
          case inl h25 =>
            -- Disjunctions on the left can always be decomposed.
            cases h25
            case inl h26 =>
              -- Show the right disjunct based on <expert-advice>.
              apply Or.inr
              -- Show the right disjunct based on <expert-advice>.
              apply Or.inr
              -- Show the right disjunct based on <expert-advice>.
              apply Or.inr
              -- One of the premise coincides with the conclusion.
              exact h26
            case inr h27 =>
              -- Show the right disjunct based on <expert-advice>.
              apply Or.inr
              -- Show the left disjunct based on <expert-advice>.
              apply Or.inl
              -- One of the premise coincides with the conclusion.
              exact h27
          case inr h28 =>
            -- Show the right disjunct based on <expert-advice>.
            apply Or.inr
            -- Show the left disjunct based on <expert-advice>.
            apply Or.inl
            -- One of the premise coincides with the conclusion.
            exact h28
    case inr h29 =>
      -- Conjunctions on the left can always be decomposed.
      let h30 := h29.left
      let h31 := h29.right
      -- We want to use the implication h4 based on <expert-advice>. So we show its premise.
      have h32 : True := by
        -- True on the right can always be proven directly.
        apply True.intro
      -- We have shown the premise of h4, we can now drive its conclusion.
      let h33 := h4 h32
      -- Disjunctions on the left can always be decomposed.
      cases h33
      case inl h34 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- One of the premise coincides with the conclusion.
        exact h34
      case inr h35 =>
        -- Conjunctions on the left can always be decomposed.
        let h36 := h35.left
        let h37 := h35.right
        -- Disjunctions on the left can always be decomposed.
        cases h37
        case inl h38 =>
          -- Disjunctions on the left can always be decomposed.
          cases h38
          case inl h39 =>
            -- Show the right disjunct based on <expert-advice>.
            apply Or.inr
            -- Show the right disjunct based on <expert-advice>.
            apply Or.inr
            -- Show the right disjunct based on <expert-advice>.
            apply Or.inr
            -- One of the premise coincides with the conclusion.
            exact h39
          case inr h40 =>
            -- Show the right disjunct based on <expert-advice>.
            apply Or.inr
            -- Show the left disjunct based on <expert-advice>.
            apply Or.inl
            -- One of the premise coincides with the conclusion.
            exact h40
        case inr h41 =>
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- Show the left disjunct based on <expert-advice>.
          apply Or.inl
          -- One of the premise coincides with the conclusion.
          exact h41
  case inr h42 =>
    -- False on the left can always be used.
    apply False.elim h42



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_62987609376356315345812031012 : ((p4 ∧ (p5 ∨ (((True ∧ (True ∨ True)) ∧ ((False → ((p5 → (((True ∨ p3) ∨ True) ∧ True)) ∧ p3)) ∨ (True → p4))) → (p5 → p1)))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_348739881596703081078380796800 : (p3 → (False ∨ ((p4 ∨ ((p1 ∨ p3) ∧ ((p4 ∧ (((p4 → p4) ∧ p5) ∨ ((False ∧ p3) ∧ p1))) → ((p2 ∨ p3) → False)))) ∨ (p5 ∨ True)))) := by
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



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_56394621482243421115063091739 : ((((False ∧ (p1 ∧ True)) → p5) → (p1 ∧ (p1 ∨ (p2 ∧ (((True ∧ False) ∧ (((p3 → False) ∧ p5) ∨ (p5 ∧ p1))) ∨ (p1 ∨ p1)))))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_217441481717945433325154568391 : (((p3 → (p2 → p5)) ∨ p1) → (p5 → ((((((p5 ∨ p5) ∧ (((p3 ∧ p4) → p4) ∨ True)) ∨ p1) ∧ p2) ∧ (p1 ∧ (p3 → p5))) → p5))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
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
        let h13 := h5.left
        let h14 := h5.right
        -- Disjunctions on the left can always be decomposed.
        cases h1
        case inl h15 =>
          -- One of the premise coincides with the conclusion.
          exact h2
        case inr h16 =>
          -- One of the premise coincides with the conclusion.
          exact h2
      case inr h17 =>
        -- Conjunctions on the left can always be decomposed.
        let h18 := h5.left
        let h19 := h5.right
        -- Disjunctions on the left can always be decomposed.
        cases h1
        case inl h20 =>
          -- One of the premise coincides with the conclusion.
          exact h2
        case inr h21 =>
          -- One of the premise coincides with the conclusion.
          exact h2
    case inr h22 =>
      -- Disjunctions on the left can always be decomposed.
      cases h10
      case inl h23 =>
        -- Conjunctions on the left can always be decomposed.
        let h24 := h5.left
        let h25 := h5.right
        -- Disjunctions on the left can always be decomposed.
        cases h1
        case inl h26 =>
          -- One of the premise coincides with the conclusion.
          exact h2
        case inr h27 =>
          -- One of the premise coincides with the conclusion.
          exact h2
      case inr h28 =>
        -- Conjunctions on the left can always be decomposed.
        let h29 := h5.left
        let h30 := h5.right
        -- Disjunctions on the left can always be decomposed.
        cases h1
        case inl h31 =>
          -- One of the premise coincides with the conclusion.
          exact h2
        case inr h32 =>
          -- One of the premise coincides with the conclusion.
          exact h2
  case inr h33 =>
    -- Conjunctions on the left can always be decomposed.
    let h34 := h5.left
    let h35 := h5.right
    -- Disjunctions on the left can always be decomposed.
    cases h1
    case inl h36 =>
      -- One of the premise coincides with the conclusion.
      exact h2
    case inr h37 =>
      -- One of the premise coincides with the conclusion.
      exact h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_159004871611542430285995480310 : ((p4 ∨ ((False ∧ (((p2 ∨ True) ∧ (((((p2 → False) → False) → p1) ∨ p4) → p1)) → False)) ∧ p3)) ∨ ((p5 ∨ ((False ∧ p1) ∧ True)) → p5)) := by
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
    -- Conjunctions on the left can always be decomposed.
    let h6 := h4.left
    let h7 := h4.right
    -- False on the left can always be used.
    apply False.elim h6



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_231239304334720138298773287956 : (((p4 ∨ False) ∨ p4) → ((p5 ∨ (p3 → (p3 ∧ p3))) → ((False → ((p5 → p4) ∨ p5)) → (p1 → ((p2 → p3) ∨ (p5 ∨ (p3 ∨ p4))))))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Implications on the right can always be decomposed.
  intro h3
  -- Implications on the right can always be decomposed.
  intro h4
  -- Disjunctions on the left can always be decomposed.
  cases h2
  case inl h5 =>
    -- Disjunctions on the left can always be decomposed.
    cases h1
    case inl h6 =>
      -- Disjunctions on the left can always be decomposed.
      cases h6
      case inl h7 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- One of the premise coincides with the conclusion.
        exact h5
      case inr h8 =>
        -- False on the left can always be used.
        apply False.elim h8
    case inr h9 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- One of the premise coincides with the conclusion.
      exact h5
  case inr h10 =>
    -- Disjunctions on the left can always be decomposed.
    cases h1
    case inl h11 =>
      -- Disjunctions on the left can always be decomposed.
      cases h11
      case inl h12 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- One of the premise coincides with the conclusion.
        exact h12
      case inr h13 =>
        -- False on the left can always be used.
        apply False.elim h13
    case inr h14 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- One of the premise coincides with the conclusion.
      exact h14



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_238128272918105364484635612506 : ((True ∨ p3) ∧ ((False ∨ (p5 ∨ ((p5 ∧ (((p4 ∧ True) → p5) ∨ ((((p3 → p4) → (True → p1)) ∨ True) ∨ p1))) → p3))) ∨ (p5 ∨ True))) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_160040102004820463946620600438 : ((((p5 → False) ∨ ((((((True ∧ (True → p5)) ∧ (p1 → p1)) ∨ p4) ∨ p3) → False) ∨ True)) → False) → ((p4 → False) → ((p1 → p1) ∧ False))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h3
  -- One of the premise coincides with the conclusion.
  exact h3
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h4 : ((p5 → False) ∨ ((((((True ∧ (True → p5)) ∧ (p1 → p1)) ∨ p4) ∨ p3) → False) ∨ True)) := by
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h5 := h1 h4
  -- False on the left can always be used.
  apply False.elim h5



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_180903978294675304448154432314 : (((True ∨ (p4 ∨ p5)) → (p3 ∧ (p4 ∧ ((p5 → (False → True)) ∧ True)))) → (p3 ∧ (((p5 ∧ True) ∨ p4) ∨ ((p3 → (True ∧ p1)) ∧ p4)))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h2 : (True ∨ (p4 ∨ p5)) := by
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h3 := h1 h2
  -- We need to get the left conjuct of h3 based on <expert-advice>.
  let h4 := h3.left
  -- One of the premise coincides with the conclusion.
  exact h4
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h5 : (True ∨ (p4 ∨ p5)) := by
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h6 := h1 h5
  -- We need to get the right conjuct of h6 based on <expert-advice>.
  let h7 := h6.right
  -- We need to get the left conjuct of h7 based on <expert-advice>.
  let h8 := h7.left
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h8



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_660270611085740522660523027367 : ((((((p5 ∨ p4) → ((False ∨ (((p4 → ((p2 ∧ ((p2 → p3) ∨ False)) → False)) ∨ p3) ∧ (True ∨ p5))) → True)) ∨ p3) → (False ∧ p4)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_731260254698703452837214690702 : ((((p3 ∨ (p3 → False)) → ((p2 → (((p3 ∨ p1) ∧ (p5 → (p3 → False))) ∨ p1)) ∨ (False ∧ (True → ((p1 ∨ p4) → (p3 → p1)))))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_185917778060324705606638888978 : (((((p4 → False) ∧ (True ∨ p5)) → (False ∨ (p3 → p1))) ∧ p4) → ((((p1 ∧ (p2 ∨ p2)) ∨ (p5 → False)) → False) → ((True → False) → p5))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Implications on the right can always be decomposed.
  intro h3
  -- Conjunctions on the left can always be decomposed.
  let h4 := h1.left
  let h5 := h1.right
  -- We want to use the implication h3 based on <expert-advice>. So we show its premise.
  have h6 : True := by
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h3, we can now drive its conclusion.
  let h7 := h3 h6
  -- False on the left can always be used.
  apply False.elim h7



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_352020111410329657804819062312 : (p4 → (((((p2 → True) → (p2 → p4)) ∧ p3) ∧ p1) → ((((((True ∧ (p4 ∨ False)) → p1) ∧ (p1 ∨ p4)) ∧ p4) → p5) ∨ (False ∨ True)))) := by
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
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_134163088335322686529099118293 : (((((p2 ∧ (((p1 ∧ p2) ∧ p4) ∧ ((p1 ∨ p5) ∨ (p1 → p1)))) ∧ p2) ∧ ((p3 ∧ (p5 ∨ p4)) ∧ p3)) ∨ p4) ∨ ((p1 ∧ False) → True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_67592487041665335772244148241 : ((p1 → (True ∧ ((p5 → p5) ∧ ((((p2 ∧ p1) ∨ (((p3 ∨ p1) ∧ False) ∨ (p4 ∧ (True ∨ p2)))) ∨ (p2 → True)) ∧ (False ∧ p4))))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_64255403587199013889990719324 : ((False ∨ (p4 ∨ (((((False → False) → ((p3 → (p4 ∨ ((p4 ∨ p3) ∨ False))) → (True → (False → (p3 ∨ True))))) ∧ False) ∨ False) ∧ p3))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_165421112078740349890113402606 : (((((((p4 → p1) ∨ p3) → p2) → False) → ((p3 ∧ False) ∧ False)) → (p3 ∨ (p1 ∧ p4))) ∨ (((False → p2) ∨ True) ∧ ((p2 ∧ p1) → True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
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



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_208292353630368436921124479686 : (((p3 ∨ False) ∧ (True ∨ (p5 ∨ p1))) → (((p3 → (((False ∨ (False ∧ (True ∧ (p2 ∨ p5)))) ∨ p5) ∧ p5)) → p2) ∨ ((False ∨ True) ∧ True))) := by
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
      -- Conjunctions on the right can always be decomposed.
      apply And.intro
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- True on the right can always be proven directly.
      apply True.intro
      -- True on the right can always be proven directly.
      apply True.intro
    case inr h6 =>
      -- Disjunctions on the left can always be decomposed.
      cases h6
      case inl h7 =>
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
      case inr h8 =>
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
  case inr h9 =>
    -- False on the left can always be used.
    apply False.elim h9



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_68088662296479565686523926159 : ((p2 → (p5 ∨ ((p3 → (False ∧ ((((p3 ∨ (p3 → ((p4 ∨ p4) ∨ True))) → p4) → (p5 → p2)) → (True ∨ p5)))) ∧ (p3 ∨ p2)))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_783564796303561763802071019931 : (((p3 ∨ ((p3 → (((True ∨ p2) ∨ p4) → ((p1 ∧ True) → p2))) ∧ (((p1 → False) → (p3 → ((p3 ∧ p1) ∨ p4))) ∧ (p1 ∨ p5)))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_53048614924340012016401925598 : ((((p1 ∧ p2) ∨ ((True ∧ (False ∨ (p4 ∨ False))) ∧ (p2 ∨ p4))) ∧ ((p4 ∨ p1) ∨ ((True ∧ ((False ∨ (p5 ∧ p1)) ∧ p4)) ∨ p4))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_690966041421579971671622212130 : (((((((False → (p2 → (((p5 ∨ p2) → p2) ∧ p3))) → p3) ∨ p1) → (p4 → p5)) → (False ∨ (True → (p2 ∨ ((True → False) ∨ p3))))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_65623862271986165013711701052 : ((p4 ∨ (((p3 ∨ (p4 ∧ (((False ∨ True) ∧ (((((False ∧ ((p5 ∨ p4) ∨ p5)) ∧ p1) ∧ False) → p2) ∨ p4)) ∨ p1))) ∧ False) ∨ True)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_167320489431558370429622317203 : (((((False → (False ∨ False)) → (False → (((p4 → p3) → p1) → p5))) ∧ (p3 ∨ p2)) → p1) → ((((p1 ∨ p5) ∨ p2) ∨ (p3 ∨ True)) ∧ True)) := by
  -- Implications on the right can always be decomposed.
  intro h1
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
theorem thm_5_vars_319057644504695432224531819834 : (p4 ∨ ((p1 ∧ ((p4 → ((p1 → (((p3 ∨ p4) → (p3 ∨ p5)) ∨ p5)) → ((True → False) ∨ p3))) ∨ p3)) ∨ ((p3 ∨ (True ∧ p2)) ∨ True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_164517774581012429074101387323 : ((((((p4 → p2) ∧ False) ∨ (p1 → (((p5 ∧ p2) ∨ p4) ∧ False))) ∨ (p5 → p2)) ∧ p5) ∨ ((True ∨ (p1 ∧ ((p5 ∨ False) ∨ p3))) ∨ False)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_228103620203952753819184491469 : ((p4 ∧ (p3 ∨ False)) ∨ ((((((((p3 ∧ p3) ∨ (p2 ∧ p1)) ∨ p5) → ((False → p4) ∧ p1)) ∧ ((False → p4) ∧ p5)) → p1) ∨ p2) ∨ p1)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
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
  -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
  have h6 : (((p3 ∧ p3) ∨ (p2 ∧ p1)) ∨ p5) := by
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h5
  -- We have shown the premise of h2, we can now drive its conclusion.
  let h7 := h2 h6
  -- We need to get the right conjuct of h7 based on <expert-advice>.
  let h8 := h7.right
  -- One of the premise coincides with the conclusion.
  exact h8



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_180229863740753437199607881184 : (((p1 ∧ (((False → p3) ∨ (True ∧ (p1 → (p1 ∨ p1)))) ∧ True)) → p2) → (((p1 ∧ (p4 → (((True → p1) → False) ∧ p2))) → p5) ∨ True)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_171577896006691339133540321621 : ((((p2 → ((((False ∨ True) → True) ∨ False) → (p2 → p3))) ∨ (p2 ∧ True)) ∨ p1) ∨ ((((p3 → p1) ∨ p4) ∨ True) ∨ (p4 ∧ (p1 ∨ p3)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_685619789848554790460866650274 : ((((((p4 → (((p1 ∨ p2) ∨ (p4 ∧ p2)) → (p5 ∨ (True ∨ p2)))) ∧ (p4 → p4)) ∨ False) → ((p5 ∨ (p3 ∧ (p4 ∧ p3))) → p2)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_185305675930098457390395192726 : ((p3 ∧ ((((False ∨ (p5 → (p3 ∨ p2))) → p5) ∧ p4) ∧ p1)) ∨ (((False ∨ p5) ∧ p2) ∨ ((p1 ∨ ((p5 ∨ True) ∧ p2)) → (p5 → p5)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
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
    -- Conjunctions on the left can always be decomposed.
    let h5 := h4.left
    let h6 := h4.right
    -- Disjunctions on the left can always be decomposed.
    cases h5
    case inl h7 =>
      -- One of the premise coincides with the conclusion.
      exact h7
    case inr h8 =>
      -- One of the premise coincides with the conclusion.
      exact h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_316379390223724254731338473609 : (p3 ∨ (False ∨ (((False → (((p5 → (((p2 ∧ p5) ∧ (p5 ∨ False)) ∧ p3)) ∨ False) → p3)) ∧ ((p3 ∨ p1) ∧ (True → p1))) → (p4 ∨ p1)))) := by
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
    -- We want to use the implication h5 based on <expert-advice>. So we show its premise.
    have h7 : True := by
      -- True on the right can always be proven directly.
      apply True.intro
    -- We have shown the premise of h5, we can now drive its conclusion.
    let h8 := h5 h7
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h8
  case inr h9 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h9



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_702991919777412312617180742614 : ((((((True ∧ p5) → p2) → (True ∧ ((p1 ∨ p1) ∧ p3))) ∨ ((p5 ∨ ((p3 ∧ (p1 ∨ p4)) ∨ p3)) → (p1 ∨ ((p4 → False) → True)))) ∨ p1) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
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
    -- Disjunctions on the left can always be decomposed.
    cases h4
    case inl h5 =>
      -- Conjunctions on the left can always be decomposed.
      let h6 := h5.left
      let h7 := h5.right
      -- Disjunctions on the left can always be decomposed.
      cases h7
      case inl h8 =>
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- One of the premise coincides with the conclusion.
        exact h8
      case inr h9 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- Implications on the right can always be decomposed.
        intro h10
        -- True on the right can always be proven directly.
        apply True.intro
    case inr h11 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Implications on the right can always be decomposed.
      intro h12
      -- True on the right can always be proven directly.
      apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_48172481248429385104413675961 : ((((False → p4) ∧ ((p3 → (((False → (p1 ∨ p5)) ∧ True) ∧ (((((p4 ∨ p4) ∨ True) ∨ True) ∨ True) ∨ True))) → p5)) → (False ∨ p5)) ∨ False) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- We want to use the implication h3 based on <expert-advice>. So we show its premise.
  have h4 : (p3 → (((False → (p1 ∨ p5)) ∧ True) ∧ (((((p4 ∨ p4) ∨ True) ∨ True) ∨ True) ∨ True))) := by
    -- Implications on the right can always be decomposed.
    intro h5
    -- Conjunctions on the right can always be decomposed.
    apply And.intro
    -- Conjunctions on the right can always be decomposed.
    apply And.intro
    -- Implications on the right can always be decomposed.
    intro h6
    -- False on the left can always be used.
    apply False.elim h6
    -- True on the right can always be proven directly.
    apply True.intro
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h3, we can now drive its conclusion.
  let h7 := h3 h4
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h7



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_212650943374430098424998176937 : ((True → (False ∨ (True ∨ False))) ∧ ((True ∨ ((False ∧ (p1 ∧ True)) → (p2 → False))) ∧ (((p2 → (p1 ∨ p2)) → False) → (p5 ∨ (p3 ∨ p3))))) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro
  -- Implications on the right can always be decomposed.
  intro h2
  -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
  have h3 : (p2 → (p1 ∨ p2)) := by
    -- Implications on the right can always be decomposed.
    intro h4
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h4
  -- We have shown the premise of h2, we can now drive its conclusion.
  let h5 := h2 h3
  -- False on the left can always be used.
  apply False.elim h5



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_46544404961301772715252876863 : ((((p3 → p5) ∨ ((True → p2) ∧ (True ∧ (((p1 ∧ p5) ∧ ((((p1 ∨ p3) ∧ p4) ∨ True) → (False ∨ p1))) → p2)))) ∧ (p3 ∧ p4)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_50306054957965499683607741257 : ((((((True → (p5 → ((p5 ∧ p2) → (p1 → True)))) → p2) → p5) ∧ (p1 ∨ ((p1 ∧ p4) ∨ p3))) ∨ (True → ((p3 ∨ p4) → p1))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_249666798035827121486724483002 : ((p5 ∨ p4) ∨ ((p2 ∧ (((p3 ∧ (False ∨ p4)) ∨ (True ∧ (True ∨ (p5 ∧ p1)))) ∨ ((((p3 ∨ p1) ∨ p5) → p2) ∨ p4))) ∨ (p2 ∨ True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_307499527723921574148297023692 : (p1 ∨ (True → (((((p5 ∨ p5) ∧ p5) → ((((p4 ∧ p1) ∨ p2) ∧ ((p2 → (p3 → p2)) → False)) ∨ True)) ∧ True) ∨ (p5 → (p3 ∧ p4))))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h2
  -- Conjunctions on the left can always be decomposed.
  let h3 := h2.left
  let h4 := h2.right
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
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_346802858029168442948111679845 : (p3 → ((p5 ∨ ((p3 → (((True ∨ p3) → (False ∨ False)) ∨ ((p4 ∨ p2) ∧ (p2 ∧ (p3 ∧ p1))))) ∧ p2)) ∨ ((p3 ∧ (p1 → p2)) ∨ True))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_186494690283807132485789169916 : (((p3 ∧ (((p3 → p5) ∨ (p4 ∧ True)) ∨ True)) ∧ (p3 ∨ False)) → ((p5 → (p5 ∧ (((False → ((p3 → p5) ∧ p2)) ∨ p3) → False))) ∨ p3)) := by
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
      -- Disjunctions on the left can always be decomposed.
      cases h3
      case inl h8 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- One of the premise coincides with the conclusion.
        exact h8
      case inr h9 =>
        -- False on the left can always be used.
        apply False.elim h9
    case inr h10 =>
      -- Conjunctions on the left can always be decomposed.
      let h11 := h10.left
      let h12 := h10.right
      -- Disjunctions on the left can always be decomposed.
      cases h3
      case inl h13 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- One of the premise coincides with the conclusion.
        exact h13
      case inr h14 =>
        -- False on the left can always be used.
        apply False.elim h14
  case inr h15 =>
    -- Disjunctions on the left can always be decomposed.
    cases h3
    case inl h16 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- One of the premise coincides with the conclusion.
      exact h16
    case inr h17 =>
      -- False on the left can always be used.
      apply False.elim h17



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_111990278965463403419569295157 : ((((((p3 ∨ p4) ∧ p5) → p5) ∧ (((p5 ∧ (p4 → False)) → False) → ((p1 ∧ p4) ∨ (p4 ∨ ((p4 ∧ p4) ∨ p2))))) ∨ p5) ∨ (p5 → p5)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_134711350033563557657785245601 : (((((p1 ∧ False) → p4) ∧ ((p4 ∧ p1) ∨ (p1 ∨ ((p4 ∧ ((p2 ∧ p2) → (True ∨ p2))) → (p4 → p5))))) → p2) ∨ (p2 → (p3 → p2))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_301796805013996295483816072415 : (False ∨ ((p4 ∧ False) ∨ (((((((p4 ∨ ((p3 → (p1 ∨ False)) → p2)) → p1) ∨ p1) ∨ p1) ∨ p1) → True) ∧ ((p2 → (p1 ∨ p4)) ∨ True)))) := by
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
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_637681637247855465909482649118 : ((((((p2 ∧ (p1 → (p5 ∧ (True ∨ (p4 → p5))))) ∨ p5) → ((p1 → ((((p3 ∧ True) ∧ p2) ∧ p5) ∧ (False → p1))) ∨ p1)) → p4) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_113813606902821041994447669646 : (((p1 ∧ (p5 ∨ (((p4 ∨ True) ∨ p5) → ((((True ∧ (False ∧ p5)) ∧ (p5 ∨ (p4 ∨ p5))) ∧ True) ∨ p1)))) → (p3 ∧ p5)) ∨ (False → p2)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_739569687482282905141677451052 : ((((p5 ∧ p3) ∨ (((p1 → (((p5 ∨ p1) ∧ ((((((p1 ∧ p4) → p2) → False) ∨ p5) → (p4 ∧ p5)) ∨ p2)) → p2)) ∨ True) → p1)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_152659250821939778943424946448 : (((p2 → False) ∧ ((((p3 → True) → ((p5 ∨ p2) ∧ (p1 ∧ ((p2 → p4) ∧ p3)))) → (p4 → p3)) → p2)) → ((p1 ∧ (p5 ∨ p1)) → p4)) := by
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
    -- Conjunctions on the left can always be decomposed.
    let h6 := h1.left
    let h7 := h1.right
    -- We want to use the implication h7 based on <expert-advice>. So we show its premise.
    have h8 : (((p3 → True) → ((p5 ∨ p2) ∧ (p1 ∧ ((p2 → p4) ∧ p3)))) → (p4 → p3)) := by
      -- Implications on the right can always be decomposed.
      intro h9
      -- Implications on the right can always be decomposed.
      intro h10
      -- We want to use the implication h9 based on <expert-advice>. So we show its premise.
      have h11 : (p3 → True) := by
        -- Implications on the right can always be decomposed.
        intro h12
        -- True on the right can always be proven directly.
        apply True.intro
      -- We have shown the premise of h9, we can now drive its conclusion.
      let h13 := h9 h11
      -- We need to get the right conjuct of h13 based on <expert-advice>.
      let h14 := h13.right
      -- We need to get the right conjuct of h14 based on <expert-advice>.
      let h15 := h14.right
      -- We need to get the right conjuct of h15 based on <expert-advice>.
      let h16 := h15.right
      -- One of the premise coincides with the conclusion.
      exact h16
    -- We have shown the premise of h7, we can now drive its conclusion.
    let h17 := h7 h8
    -- We want to use the implication h6 based on <expert-advice>. So we show its premise.
    have h18 : p2 := by
      -- One of the premise coincides with the conclusion.
      exact h17
    -- We have shown the premise of h6, we can now drive its conclusion.
    let h19 := h6 h18
    -- False on the left can always be used.
    apply False.elim h19
  case inr h20 =>
    -- Conjunctions on the left can always be decomposed.
    let h21 := h1.left
    let h22 := h1.right
    -- We want to use the implication h22 based on <expert-advice>. So we show its premise.
    have h23 : (((p3 → True) → ((p5 ∨ p2) ∧ (p1 ∧ ((p2 → p4) ∧ p3)))) → (p4 → p3)) := by
      -- Implications on the right can always be decomposed.
      intro h24
      -- Implications on the right can always be decomposed.
      intro h25
      -- We want to use the implication h24 based on <expert-advice>. So we show its premise.
      have h26 : (p3 → True) := by
        -- Implications on the right can always be decomposed.
        intro h27
        -- True on the right can always be proven directly.
        apply True.intro
      -- We have shown the premise of h24, we can now drive its conclusion.
      let h28 := h24 h26
      -- We need to get the right conjuct of h28 based on <expert-advice>.
      let h29 := h28.right
      -- We need to get the right conjuct of h29 based on <expert-advice>.
      let h30 := h29.right
      -- We need to get the right conjuct of h30 based on <expert-advice>.
      let h31 := h30.right
      -- One of the premise coincides with the conclusion.
      exact h31
    -- We have shown the premise of h22, we can now drive its conclusion.
    let h32 := h22 h23
    -- We want to use the implication h21 based on <expert-advice>. So we show its premise.
    have h33 : p2 := by
      -- One of the premise coincides with the conclusion.
      exact h32
    -- We have shown the premise of h21, we can now drive its conclusion.
    let h34 := h21 h33
    -- False on the left can always be used.
    apply False.elim h34



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_49282022385493762836947369485 : (((p4 ∧ ((((p1 ∧ (False → p2)) → p2) → ((p2 ∧ p3) → p1)) ∨ (True ∧ ((False ∨ (p2 ∨ p4)) ∧ p4)))) ∨ (True → (p5 ∨ p4))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_713186303718183385073609833942 : ((((p1 ∨ ((p1 ∨ False) ∨ (p2 ∧ p1))) ∨ (p3 ∨ ((((p1 ∨ (False ∨ (p5 ∧ (p1 → ((p4 ∧ p4) → p5))))) → p1) ∧ p5) → p2))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_48598905710612311533709294269 : ((((((((p4 → False) ∨ (p5 ∧ (p5 → (((p4 ∨ p4) → p2) → p5)))) ∧ False) → False) → p3) ∨ (p4 ∨ True)) ∧ ((p2 ∧ p2) ∨ True)) ∨ p1) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
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
theorem thm_5_vars_87984034096822736681337688062 : (((p4 → (((p1 ∨ p2) ∧ p1) → p4)) → (((p5 ∧ p4) → ((((p1 ∧ (p2 → p3)) ∨ p2) ∨ (False ∧ p5)) → (p3 ∧ p4))) ∧ False)) → False) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h2 : (p4 → (((p1 ∨ p2) ∧ p1) → p4)) := by
    -- Implications on the right can always be decomposed.
    intro h3
    -- Implications on the right can always be decomposed.
    intro h4
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
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h9 := h1 h2
  -- We need to get the right conjuct of h9 based on <expert-advice>.
  let h10 := h9.right
  -- False on the left can always be used.
  apply False.elim h10



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_175071236352032563406556515536 : ((p3 ∧ (((((p4 ∧ p3) ∧ True) ∧ p2) ∨ (((False ∧ p3) ∨ True) → False)) ∨ False)) → ((p1 ∧ (p5 ∧ p2)) ∨ ((True ∨ (False → p2)) ∧ True))) := by
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
      -- Conjunctions on the left can always be decomposed.
      let h6 := h5.left
      let h7 := h5.right
      -- Conjunctions on the left can always be decomposed.
      let h8 := h6.left
      let h9 := h6.right
      -- Conjunctions on the left can always be decomposed.
      let h10 := h8.left
      let h11 := h8.right
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Conjunctions on the right can always be decomposed.
      apply And.intro
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- True on the right can always be proven directly.
      apply True.intro
      -- True on the right can always be proven directly.
      apply True.intro
    case inr h12 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Conjunctions on the right can always be decomposed.
      apply And.intro
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- True on the right can always be proven directly.
      apply True.intro
      -- True on the right can always be proven directly.
      apply True.intro
  case inr h13 =>
    -- False on the left can always be used.
    apply False.elim h13



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_219422954527444094171833647027 : ((p4 ∨ ((p5 ∨ p1) ∧ p5)) → ((((((False ∨ (False ∨ (False ∧ p1))) ∧ p5) ∧ (p5 ∨ (p3 ∨ p4))) → p3) ∧ (p1 ∧ p2)) ∨ (False ∨ True))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h2 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro
  case inr h3 =>
    -- Conjunctions on the left can always be decomposed.
    let h4 := h3.left
    let h5 := h3.right
    -- Disjunctions on the left can always be decomposed.
    cases h4
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
theorem thm_5_vars_112659954275973752167018628409 : ((((((((p1 ∨ (((False → (p3 → p4)) ∧ p5) ∧ False)) ∧ True) ∨ p2) ∨ (p4 → p2)) ∨ True) ∨ ((p4 ∨ p3) ∨ p1)) → p5) ∨ (p5 → True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_160159201064666233131148369723 : ((((((False → p2) → (p5 ∧ True)) ∧ (p2 → p5)) → ((True ∧ True) ∧ (False ∨ p3))) ∧ (p3 → False)) → (True ∧ ((p2 ∨ (True → p3)) → p2))) := by
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
    -- One of the premise coincides with the conclusion.
    exact h3
  case inr h6 =>
    -- Conjunctions on the left can always be decomposed.
    let h7 := h1.left
    let h8 := h1.right
    -- We want to use the implication h6 based on <expert-advice>. So we show its premise.
    have h9 : True := by
      -- True on the right can always be proven directly.
      apply True.intro
    -- We have shown the premise of h6, we can now drive its conclusion.
    let h10 := h6 h9
    -- We want to use the implication h8 based on <expert-advice>. So we show its premise.
    have h11 : p3 := by
      -- One of the premise coincides with the conclusion.
      exact h10
    -- We have shown the premise of h8, we can now drive its conclusion.
    let h12 := h8 h11
    -- False on the left can always be used.
    apply False.elim h12



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_48589249617306485178803544280 : (((((True → ((p5 ∨ ((p3 ∧ p2) → p2)) ∨ (True → True))) ∧ ((p1 → (p5 → p5)) ∨ p4)) ∧ (False ∨ p3)) ∧ ((p3 ∧ False) ∨ p3)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_731683938626580847148104968573 : ((((p2 → (True ∨ p2)) → (p3 ∧ ((p2 ∧ (p1 → ((p1 ∧ (p5 ∨ (p5 ∨ p5))) → p2))) ∨ (p4 ∨ ((False ∨ (p2 → True)) ∨ p5))))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_739230101254707476231296653503 : ((((p4 ∧ p1) ∨ (((p2 ∨ (p5 ∨ False)) ∨ p1) ∨ ((False ∧ (((p4 → p1) ∨ p1) ∧ (p3 → p1))) ∧ ((p5 ∨ True) ∧ (p5 ∨ p5))))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_115497676372254809409962315022 : (((((False ∨ ((p3 → p1) ∨ True)) ∧ True) → p3) → ((p3 ∧ True) ∨ ((((p1 ∨ p3) ∨ p5) → ((p4 ∨ p4) ∧ False)) → p2))) ∨ (p4 → p3)) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h2 : ((False ∨ ((p3 → p1) ∨ True)) ∧ True) := by
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
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h3 := h1 h2
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- One of the premise coincides with the conclusion.
  exact h3
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_599706718980134211001674916910 : (((((p2 → p4) ∨ (((p2 → p1) ∧ False) ∨ ((p3 ∧ (p3 ∧ p4)) → (((p2 → (p2 ∧ ((p2 ∨ False) ∧ p5))) ∨ p1) ∨ p1)))) ∧ False) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_50238355157460981123078488946 : (((((((p3 ∧ p5) ∨ (p4 ∧ (p2 ∧ (p4 ∨ p3)))) ∧ ((p2 ∧ (True ∨ p1)) ∨ True)) → p2) → p4) ∨ ((p4 → (p1 ∧ False)) → p1)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_117292166240540700390465215746 : ((False ∧ ((p4 ∧ (((p1 ∨ ((p2 ∧ (p1 ∨ p2)) → p3)) ∧ p2) → (((p2 → p1) → (True → (p3 ∧ p2))) ∨ p3))) → p5)) ∨ (p4 ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_341736186002035942819127504361 : (p2 → (((p2 ∧ p4) ∨ ((((p1 ∨ p5) ∨ (((p1 ∨ (p3 → (p1 ∨ ((True → p5) ∨ p5)))) ∧ False) ∧ p2)) ∨ p3) ∨ p5)) ∨ (p3 ∨ p2))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_300683569205891963552634870761 : (False ∨ (((p3 → (p3 ∧ p5)) ∧ (p1 ∨ (p3 ∧ ((((p4 → (False ∨ True)) → p2) → True) ∨ False)))) ∨ ((((p1 → p5) → p4) ∨ True) ∨ False))) := by
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
theorem thm_5_vars_748655004014306126444832445054 : ((((p3 → p3) → ((((p3 ∧ ((p4 ∨ (((p1 ∧ (p2 ∧ p4)) ∨ True) → True)) ∧ ((True ∨ p5) → (p1 ∨ False)))) ∨ p5) → p2) ∧ p4)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_341687189605551387717933099276 : (p2 → (((p1 ∧ ((p5 ∧ p2) → ((True ∨ ((True → (p4 ∧ (False ∨ ((p5 → p2) → (p1 ∧ p3))))) → p2)) ∧ p3))) → False) ∨ (True ∨ p3))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_52575190520237425235063546474 : ((((p4 → (p3 ∨ (p5 ∧ (p1 ∧ (p3 ∧ (True → p5)))))) ∨ (False → p5)) ∨ (((False → True) → p3) ∨ (p2 ∧ ((p3 → False) ∧ p2)))) ∨ p5) := by
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



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_53404872166325210528584745739 : ((((p1 → ((p3 ∧ p5) ∧ ((p1 → False) ∨ p2))) ∨ (p3 → p3)) → (p5 ∨ (p4 ∨ (p1 → (((p3 ∧ p5) → (True ∨ p1)) ∧ p4))))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_207118611644042400825625186174 : (((p3 ∨ (p5 ∨ (p2 ∨ p3))) ∧ p5) → (((((p4 → False) → True) ∧ p3) ∧ ((p3 ∧ False) ∨ (True ∨ (p2 ∨ (p5 → (p1 ∨ p2)))))) ∨ p5)) := by
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
    -- One of the premise coincides with the conclusion.
    exact h3
  case inr h5 =>
    -- Disjunctions on the left can always be decomposed.
    cases h5
    case inl h6 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- One of the premise coincides with the conclusion.
      exact h3
    case inr h7 =>
      -- Disjunctions on the left can always be decomposed.
      cases h7
      case inl h8 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- One of the premise coincides with the conclusion.
        exact h3
      case inr h9 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- One of the premise coincides with the conclusion.
        exact h3



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_114545471103321762407954003875 : ((((((p1 → ((p2 ∨ ((p1 ∧ p1) ∨ p3)) → True)) ∧ p4) → (p1 ∧ True)) ∧ p3) ∧ ((p1 ∨ (p4 ∨ True)) ∧ (True → p5))) ∨ (p4 → p4)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_63400760231376158581368260099 : ((p5 ∧ (p3 ∨ (((p2 → (((False → p4) ∧ (p3 ∨ (p1 ∨ (((p3 ∨ p3) ∧ True) → p5)))) → p2)) ∧ ((p3 ∨ p2) ∨ p2)) → p1))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_138981357938936059291359057198 : ((((((p3 ∨ (((p4 ∨ ((p5 ∨ False) ∧ (p1 ∧ p3))) → (p4 → p1)) ∨ (False ∨ p1))) → p3) ∨ True) ∨ True) ∨ p1) → ((p5 ∨ p3) ∨ True)) := by
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
        -- True on the right can always be proven directly.
        apply True.intro
      case inr h5 =>
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
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_59550825794991794897280581802 : (((p3 → p1) ∨ (p2 ∧ (((p3 ∧ ((((p5 → ((False ∨ p3) ∨ (p1 → p3))) → ((p5 ∨ p3) → p2)) → p4) ∧ p4)) ∨ p4) ∧ True))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_677802262555031740589848620907 : (((((((p1 ∧ (p3 ∧ p3)) → (p1 ∨ (p5 → (((True ∧ False) ∨ p1) → p1)))) ∧ False) ∧ (p4 ∨ p4)) ∨ ((p1 ∨ p2) ∨ (False → True))) ∨ p2) ∧ True) := by
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
theorem thm_5_vars_53152955630584605355254074963 : ((((((p4 ∨ (False ∨ p1)) ∨ (p5 ∨ p5)) ∨ (True → p2)) ∨ p5) ∨ (p3 → (p5 → (((p4 ∧ (p2 ∧ False)) ∧ True) → (p4 ∨ p4))))) ∨ p1) := by
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
  -- Conjunctions on the left can always be decomposed.
  let h4 := h3.left
  let h5 := h3.right
  -- Conjunctions on the left can always be decomposed.
  let h6 := h4.left
  let h7 := h4.right
  -- Conjunctions on the left can always be decomposed.
  let h8 := h7.left
  let h9 := h7.right
  -- False on the left can always be used.
  apply False.elim h9



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_166471230456849645612891135420 : ((p3 ∨ ((((p5 → p4) ∨ (False ∨ (False ∨ (p3 ∨ (False ∧ (True ∧ False)))))) ∨ p4) ∧ p3)) ∨ (((p4 ∧ ((p4 ∧ p2) ∨ False)) → p2) ∨ p1)) := by
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
    -- Conjunctions on the left can always be decomposed.
    let h5 := h4.left
    let h6 := h4.right
    -- One of the premise coincides with the conclusion.
    exact h6
  case inr h7 =>
    -- False on the left can always be used.
    apply False.elim h7



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_228456177354758068971611776314 : ((False ∨ (p2 ∨ p4)) ∨ (p5 → ((((p1 ∧ p3) ∧ p1) ∨ ((p1 ∨ True) → ((p5 ∨ ((((True ∧ p4) ∧ p3) ∨ True) ∧ p1)) → p5))) ∨ p5))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_354017662642633929839579639642 : (p4 → (p4 → (((p2 ∧ (((False ∨ (p5 ∨ p2)) ∨ ((False ∧ p4) ∧ (p4 ∧ ((p4 ∧ p3) ∧ p3)))) → (p3 ∨ (p3 → False)))) ∨ p4) ∨ p3))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_597055151592733019495117028927 : ((((((p3 ∨ True) ∧ ((p2 → True) → p5)) → (((p3 ∧ p3) → ((True ∨ ((True → p4) ∨ p5)) → (p1 ∧ False))) ∨ (p1 ∨ p5))) ∧ p1) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_52277042057228583063898955185 : (((p2 → ((((p4 ∧ (p2 ∧ ((p3 ∨ p4) → p2))) ∧ p1) ∨ (p2 → p1)) ∨ p1)) → ((p1 → (p1 → p2)) ∨ (p1 → (p3 ∨ p1)))) ∨ p1) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h2
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_207599396343975905108346338979 : (((((p5 ∧ True) ∨ True) → p5) → p5) → ((p5 ∧ (((((p2 ∨ (p3 ∨ p3)) ∧ p1) ∧ (p3 → False)) ∧ p2) ∨ p5)) ∨ (p2 ∨ (True → True)))) := by
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
theorem thm_5_vars_69254586367331963219593275114 : ((p5 → ((p2 ∨ (p1 → False)) → (p4 ∨ (p5 ∧ ((p1 ∨ (((p5 ∨ p1) ∨ p5) ∧ p4)) ∨ ((p5 ∧ False) → ((p5 → True) → p2))))))) ∨ p5) := by
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
    -- Conjunctions on the right can always be decomposed.
    apply And.intro
    -- One of the premise coincides with the conclusion.
    exact h1
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h4
    -- Implications on the right can always be decomposed.
    intro h5
    -- Conjunctions on the left can always be decomposed.
    let h6 := h4.left
    let h7 := h4.right
    -- False on the left can always be used.
    apply False.elim h7
  case inr h8 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Conjunctions on the right can always be decomposed.
    apply And.intro
    -- One of the premise coincides with the conclusion.
    exact h1
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h9
    -- Implications on the right can always be decomposed.
    intro h10
    -- Conjunctions on the left can always be decomposed.
    let h11 := h9.left
    let h12 := h9.right
    -- False on the left can always be used.
    apply False.elim h12



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_184036929366177199283152376409 : (((((p4 ∨ p1) → ((p5 ∧ p1) → (p4 ∧ True))) → p5) ∨ True) ∨ (p4 ∧ (((False ∨ ((p5 ∨ ((p3 → True) ∧ True)) ∧ p4)) ∨ p4) ∨ p3))) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_604894391220608167930738196934 : ((((p1 → (((p5 ∨ p3) → (p4 ∧ p3)) ∧ (((True ∨ ((p2 ∧ p5) ∨ (p5 ∧ (p5 → p5)))) → ((p3 ∨ False) → False)) ∧ p3))) ∧ p5) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_341714583685213934192547144154 : (p2 → ((((p4 ∨ (p5 ∧ (((False ∨ p1) → p3) ∨ p4))) ∧ p2) ∧ ((False → (True → (True → False))) → (p5 ∧ (False ∨ True)))) ∨ (p3 → True))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h2
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_85946237752415778090496430488 : (((((False ∧ ((False → p4) ∨ (p3 ∨ p2))) → p5) → False) ∧ ((p3 ∨ ((p3 ∨ (False ∧ ((True ∨ p3) ∧ p4))) ∨ p5)) → (p4 → p5))) → p4) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
  have h4 : ((False ∧ ((False → p4) ∨ (p3 ∨ p2))) → p5) := by
    -- Implications on the right can always be decomposed.
    intro h5
    -- Conjunctions on the left can always be decomposed.
    let h6 := h5.left
    let h7 := h5.right
    -- False on the left can always be used.
    apply False.elim h6
  -- We have shown the premise of h2, we can now drive its conclusion.
  let h8 := h2 h4
  -- False on the left can always be used.
  apply False.elim h8



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_149186154147103535260674517012 : (((p1 → p5) ∧ (((((p5 ∧ True) → p1) ∨ p4) → (p3 ∨ (p3 ∨ (True ∧ ((p3 ∧ False) ∨ False))))) ∧ p2)) ∨ (((p5 → p2) → False) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_37334106554130547567124425511 : (((((((False → (p3 ∨ (p1 ∧ ((False ∧ False) ∨ p3)))) ∧ p4) → (False ∧ ((False ∨ p4) ∨ (p4 ∨ (p4 ∨ p3))))) ∧ False) ∨ p1) ∧ True) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_233689400697170643583950902314 : ((p2 ∨ (p2 → p2)) → ((p5 ∨ (False ∧ p2)) ∨ ((((False ∨ False) ∧ p2) ∧ p1) ∨ (((p5 ∧ (p3 ∧ True)) → p3) → ((False → p1) ∨ p3))))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h2 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h3
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Implications on the right can always be decomposed.
    intro h4
    -- False on the left can always be used.
    apply False.elim h4
  case inr h5 =>
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
    -- False on the left can always be used.
    apply False.elim h7



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_42827021419904095567507692414 : (((p1 → ((p1 ∧ p4) ∨ (((((p5 ∧ p2) ∨ p5) ∨ (p5 → ((p5 ∧ True) ∧ (p5 ∧ ((p3 → p3) → p4))))) → p5) → False))) ∨ True) ∨ False) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_110236016755495660834116193156 : ((p2 → (((((p1 ∧ (False ∨ p5)) ∧ ((p5 ∧ ((p3 ∨ True) → p2)) ∧ False)) ∨ (p5 ∧ ((False → p2) → p2))) ∨ p5) ∨ p2)) ∧ (True ∨ p1)) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h1
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_615606399674622238146960105914 : (((((True → (p5 ∨ (((p5 → True) ∨ (p4 ∧ p5)) ∧ (p5 → (p4 ∧ (p4 ∨ True)))))) → ((p1 ∨ p3) ∨ ((False ∧ p4) ∨ p5))) ∨ True) ∨ p3) ∧ True) := by
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
theorem thm_5_vars_352006545946063960043040973757 : (p4 → (((False ∧ p1) ∨ ((p3 ∧ p2) ∧ (p5 ∨ p5))) ∨ (((p5 ∧ ((p5 ∧ ((p3 → True) → p5)) ∨ p1)) ∨ (p3 ∧ True)) ∨ (p3 ∨ p4)))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_649749179030414957912849329073 : (((((((((p5 ∧ p1) ∧ (p2 ∧ p1)) ∧ ((p2 → False) ∨ (True ∧ (p2 ∨ p3)))) ∧ p2) ∨ (p4 → p4)) → (p2 → p3)) ∧ (True ∨ p2)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_798120910852182935258006907162 : (((p1 → ((False → ((((True ∧ (p3 ∨ True)) ∨ (p2 → (False ∧ (p4 → (True ∨ (True ∧ True)))))) → p5) → True)) → ((True ∧ p2) ∨ p4))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



