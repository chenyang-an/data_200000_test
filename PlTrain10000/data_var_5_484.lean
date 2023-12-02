variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_113443836602877799740352589004 : (((((p4 → p5) ∨ (p5 → (((p2 ∨ (p1 ∧ p5)) ∨ (((False ∧ p5) ∨ (True → p3)) ∨ True)) ∧ False))) ∨ p1) ∨ (True ∨ p4)) ∨ (True ∨ p3)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_179140259643665310824057468710 : ((p1 ∧ (False ∨ (((((p4 ∧ True) ∨ (p1 ∨ False)) ∨ p2) ∨ False) ∨ p2))) ∨ (True → (((((p4 → (p2 ∨ p3)) ∨ p4) ∧ p5) ∧ p3) → p3))) := by
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
  -- Disjunctions on the left can always be decomposed.
  cases h5
  case inl h7 =>
    -- One of the premise coincides with the conclusion.
    exact h4
  case inr h8 =>
    -- One of the premise coincides with the conclusion.
    exact h4



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_650625885643089793794054869094 : ((((((p4 → (p4 ∨ p3)) ∨ ((p2 → p5) ∧ (p4 ∧ p1))) ∧ ((True ∧ (((p4 ∨ True) ∧ (p4 → p1)) ∧ p4)) → p3)) ∧ (p5 ∧ p1)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_190563310642899914672871280140 : (((((True ∨ p5) ∧ True) ∧ ((p1 ∧ p5) → p4)) → p1) ∨ ((((p1 ∨ p4) ∧ p1) → (False → (p2 → p3))) → ((False → p3) ∨ (p2 ∧ p1)))) := by
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
theorem thm_5_vars_115019659445783519412032209176 : (((p5 ∧ ((((p3 → p4) ∧ p5) ∧ ((p1 ∨ p2) ∨ p5)) ∧ p3)) ∧ (((p4 ∨ p4) → False) ∨ (p5 ∧ (p2 → (p2 → p5))))) ∨ (p5 → True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_801278464084714708017410583896 : (((p2 → ((((((p1 → True) ∨ (True ∨ True)) → p3) ∧ False) ∨ ((p5 ∨ p1) → p2)) ∧ ((p3 → p4) ∨ ((False ∨ (p2 ∨ p1)) ∨ p1)))) ∨ p4) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h2
  -- Disjunctions on the left can always be decomposed.
  cases h2
  case inl h3 =>
    -- One of the premise coincides with the conclusion.
    exact h1
  case inr h4 =>
    -- One of the premise coincides with the conclusion.
    exact h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- One of the premise coincides with the conclusion.
  exact h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_345570706692496361501205374727 : (p3 → (((p3 ∧ (p5 → True)) ∧ ((p5 ∨ (p4 → p4)) ∧ (p4 ∧ (((False ∨ ((p4 ∧ (p5 ∨ (p3 → p5))) ∧ p5)) → p5) → p1)))) ∨ True)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_328113756616640711578421235399 : (True → (((p2 ∨ (((True → ((p2 ∧ (True ∨ p1)) ∧ (p3 ∨ (p3 → p4)))) ∨ (p3 → p1)) ∧ True)) → (p2 → p3)) ∨ (p2 ∨ (p2 → p2)))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h2
  -- One of the premise coincides with the conclusion.
  exact h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_87293365804418292582842808720 : ((((p1 ∨ ((p3 ∨ False) → p3)) → p4) ∧ ((p1 ∨ ((True → ((p1 → p4) ∨ p4)) → False)) ∧ ((p4 → p5) ∨ ((p5 ∨ p4) ∨ p2)))) → p4) := by
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
    -- Disjunctions on the left can always be decomposed.
    cases h5
    case inl h7 =>
      -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
      have h8 : (p1 ∨ ((p3 ∨ False) → p3)) := by
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- One of the premise coincides with the conclusion.
        exact h6
      -- We have shown the premise of h2, we can now drive its conclusion.
      let h9 := h2 h8
      -- One of the premise coincides with the conclusion.
      exact h9
    case inr h10 =>
      -- Disjunctions on the left can always be decomposed.
      cases h10
      case inl h11 =>
        -- Disjunctions on the left can always be decomposed.
        cases h11
        case inl h12 =>
          -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
          have h13 : (p1 ∨ ((p3 ∨ False) → p3)) := by
            -- Show the left disjunct based on <expert-advice>.
            apply Or.inl
            -- One of the premise coincides with the conclusion.
            exact h6
          -- We have shown the premise of h2, we can now drive its conclusion.
          let h14 := h2 h13
          -- One of the premise coincides with the conclusion.
          exact h14
        case inr h15 =>
          -- One of the premise coincides with the conclusion.
          exact h15
      case inr h16 =>
        -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
        have h17 : (p1 ∨ ((p3 ∨ False) → p3)) := by
          -- Show the left disjunct based on <expert-advice>.
          apply Or.inl
          -- One of the premise coincides with the conclusion.
          exact h6
        -- We have shown the premise of h2, we can now drive its conclusion.
        let h18 := h2 h17
        -- One of the premise coincides with the conclusion.
        exact h18
  case inr h19 =>
    -- Disjunctions on the left can always be decomposed.
    cases h5
    case inl h20 =>
      -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
      have h21 : (p1 ∨ ((p3 ∨ False) → p3)) := by
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- Implications on the right can always be decomposed.
        intro h22
        -- Disjunctions on the left can always be decomposed.
        cases h22
        case inl h23 =>
          -- One of the premise coincides with the conclusion.
          exact h23
        case inr h24 =>
          -- False on the left can always be used.
          apply False.elim h24
      -- We have shown the premise of h2, we can now drive its conclusion.
      let h25 := h2 h21
      -- One of the premise coincides with the conclusion.
      exact h25
    case inr h26 =>
      -- Disjunctions on the left can always be decomposed.
      cases h26
      case inl h27 =>
        -- Disjunctions on the left can always be decomposed.
        cases h27
        case inl h28 =>
          -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
          have h29 : (p1 ∨ ((p3 ∨ False) → p3)) := by
            -- Show the right disjunct based on <expert-advice>.
            apply Or.inr
            -- Implications on the right can always be decomposed.
            intro h30
            -- Disjunctions on the left can always be decomposed.
            cases h30
            case inl h31 =>
              -- One of the premise coincides with the conclusion.
              exact h31
            case inr h32 =>
              -- False on the left can always be used.
              apply False.elim h32
          -- We have shown the premise of h2, we can now drive its conclusion.
          let h33 := h2 h29
          -- One of the premise coincides with the conclusion.
          exact h33
        case inr h34 =>
          -- One of the premise coincides with the conclusion.
          exact h34
      case inr h35 =>
        -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
        have h36 : (p1 ∨ ((p3 ∨ False) → p3)) := by
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- Implications on the right can always be decomposed.
          intro h37
          -- Disjunctions on the left can always be decomposed.
          cases h37
          case inl h38 =>
            -- One of the premise coincides with the conclusion.
            exact h38
          case inr h39 =>
            -- False on the left can always be used.
            apply False.elim h39
        -- We have shown the premise of h2, we can now drive its conclusion.
        let h40 := h2 h36
        -- One of the premise coincides with the conclusion.
        exact h40



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_41469137524616509143983720406 : (((((p2 ∧ (False ∧ (p2 ∧ ((p5 ∧ False) → (p2 ∨ p4))))) ∧ p4) ∨ (False ∧ ((((p2 ∨ (False → p3)) ∨ False) ∨ p3) → True))) ∨ True) ∨ p1) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_136169281006105351513612029075 : (((((True ∧ (p5 ∨ p2)) ∨ False) ∧ p3) ∧ ((False ∨ p2) ∨ (False → ((False ∨ (True ∧ (p1 → (p2 → p2)))) → p2)))) ∨ ((False ∧ p1) → p1)) := by
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
theorem thm_5_vars_44408801992145785237153052299 : ((((((False ∨ (p3 → ((False ∨ p4) ∨ p4))) ∧ p4) ∧ ((p1 → False) ∧ p4)) → (p4 ∨ ((False ∧ (p3 ∨ p3)) ∧ (p2 ∧ p2)))) → p2) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_47014912233867754163688123409 : ((((p4 ∧ ((p3 → (((p2 ∨ (p5 ∧ True)) ∨ ((p2 → p4) ∨ (((p4 → False) ∨ p1) ∨ False))) ∧ p2)) → p4)) → p1) ∨ (False ∨ p3)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_53246348653247964459713887272 : ((((False ∧ p1) ∧ ((p2 → ((p2 ∧ p5) → p4)) → (p3 ∨ True))) ∨ (True → ((False ∧ ((p5 ∨ p1) ∧ (p5 ∨ p4))) ∧ (p5 → True)))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_731280388310067302584736683587 : ((((p4 ∨ (p1 ∧ p3)) → (p2 ∨ ((p1 → ((p5 ∧ (p4 → ((False ∨ p3) ∧ ((((p4 ∧ p4) ∧ p1) → False) → False)))) → p4)) ∧ False))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_682616326217898877385672611366 : (((((p2 → (False ∧ (((p1 → p1) ∧ p5) → False))) ∨ (((p1 ∨ (p3 ∧ False)) ∨ p4) ∨ False)) ∧ (((p1 ∨ p3) ∧ (p5 ∨ p3)) → p3)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_678518048306451541407801407224 : ((((((p5 ∧ p3) ∧ p1) ∨ ((((p3 → False) → p1) → (p2 → ((p4 → p1) ∨ (p1 ∨ True)))) ∨ p3)) ∨ (((False ∧ p5) ∨ True) → p1)) ∨ p2) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
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
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_159998642956265593688750788414 : ((((p2 → (((True ∨ p5) ∨ p4) ∧ p2)) ∨ ((False ∧ (p3 → p4)) → ((False → p4) ∨ False))) → True) → ((((True → p4) ∨ True) ∧ p4) ∨ True)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_42494329028033782606606492141 : (((False ∨ ((((p1 → (((p3 → (p2 → (p2 → p3))) ∨ True) ∧ ((False ∧ (p5 ∨ p1)) ∧ p4))) ∨ True) → (True ∨ p4)) → p5)) ∨ True) ∨ p2) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_119299547795601610611772855374 : ((p3 → ((p4 ∧ ((((p5 → (p2 → ((p4 → (p5 ∧ ((p4 ∧ True) → (p2 ∧ p4)))) ∧ p4))) → p5) → p5) ∧ p1)) → p2)) ∨ (False → p4)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_57669409485180554306144280500 : ((((True → p5) ∨ p4) → ((p3 ∧ (p1 ∧ ((p5 ∧ p4) ∨ (False ∨ (((False ∨ False) ∧ ((p5 ∧ p1) → (p1 → p1))) ∨ p1))))) ∧ p4)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_351310780616393089862740608938 : (p4 → ((((False ∨ True) → p5) ∧ ((p4 ∨ (p2 → p5)) ∨ (((p3 ∨ p1) ∨ p3) ∨ ((p4 ∧ p1) ∨ (p4 ∨ False))))) → (p3 ∨ (p5 ∨ True)))) := by
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
  case inr h8 =>
    -- Disjunctions on the left can always be decomposed.
    cases h8
    case inl h9 =>
      -- Disjunctions on the left can always be decomposed.
      cases h9
      case inl h10 =>
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
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- True on the right can always be proven directly.
          apply True.intro
      case inr h13 =>
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- One of the premise coincides with the conclusion.
        exact h13
    case inr h14 =>
      -- Disjunctions on the left can always be decomposed.
      cases h14
      case inl h15 =>
        -- Conjunctions on the left can always be decomposed.
        let h16 := h15.left
        let h17 := h15.right
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- True on the right can always be proven directly.
        apply True.intro
      case inr h18 =>
        -- Disjunctions on the left can always be decomposed.
        cases h18
        case inl h19 =>
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- True on the right can always be proven directly.
          apply True.intro
        case inr h20 =>
          -- False on the left can always be used.
          apply False.elim h20



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_9258539605415530718937604942 : ((((((p3 → (True → (False → p5))) ∧ p5) ∨ True) → (((((p1 → ((p1 → (p2 → p5)) ∨ p3)) → False) ∨ p5) ∧ p3) ∨ p3)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_148372158206287228090578710164 : ((((p2 → (p3 ∧ ((((p5 ∧ (p4 ∧ p4)) ∨ p3) ∨ p3) ∧ p2))) ∨ False) ∨ (((False ∧ p3) ∧ False) ∧ p3)) ∨ (p2 → ((p5 → p2) ∨ False))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h2
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_633119913662541735540514725545 : (((((True ∧ ((((True ∧ True) ∨ (((p1 ∨ p4) ∨ (p2 ∧ ((p5 → p5) ∨ p3))) ∨ (True ∧ False))) ∨ True) ∨ False)) ∧ (p2 → p2)) → p4) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_205946397281775210976115348430 : ((False ∧ (p3 ∧ (False ∧ (p4 ∨ p2)))) ∨ ((((p2 → ((((p2 ∧ (False ∨ p3)) → False) → p5) → (p2 ∧ p3))) ∨ (p5 ∨ p4)) ∨ True) ∨ p1)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_55491950019494912525245536163 : (((((True ∨ True) → p4) → (p3 ∧ p5)) → (((False → (False ∨ (p2 ∧ (p4 → p1)))) → ((False → (p3 ∧ (False ∨ p5))) ∧ p3)) → p3)) ∨ p4) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
  have h3 : (False → (False ∨ (p2 ∧ (p4 → p1)))) := by
    -- Implications on the right can always be decomposed.
    intro h4
    -- False on the left can always be used.
    apply False.elim h4
  -- We have shown the premise of h2, we can now drive its conclusion.
  let h5 := h2 h3
  -- We need to get the right conjuct of h5 based on <expert-advice>.
  let h6 := h5.right
  -- One of the premise coincides with the conclusion.
  exact h6



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_767252402764307622454414492566 : (((p5 ∧ (((p5 ∨ ((p1 ∧ ((((p1 ∧ True) ∨ (p5 → ((p5 ∨ True) → ((True ∧ p2) ∧ False)))) ∧ p2) → p1)) → True)) → False) ∧ False)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_251586925688842595779187254600 : ((p3 → False) ∨ (p1 → ((((p2 ∨ p5) ∨ False) → (p3 ∨ p4)) ∨ (((p4 ∨ p2) → ((p4 ∧ (p1 → (p3 ∨ True))) → (p3 ∨ True))) ∨ p3)))) := by
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
  -- Implications on the right can always be decomposed.
  intro h3
  -- Conjunctions on the left can always be decomposed.
  let h4 := h3.left
  let h5 := h3.right
  -- Disjunctions on the left can always be decomposed.
  cases h2
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
theorem thm_5_vars_199926527853018767694121859932 : ((((p1 → p3) ∨ (p1 ∧ p1)) ∨ (p5 → p1)) → (p2 → (((p3 ∧ (((False ∧ p3) ∧ ((p2 → p4) ∨ p1)) ∨ False)) ∨ True) ∧ (False → True)))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h3 =>
    -- Disjunctions on the left can always be decomposed.
    cases h3
    case inl h4 =>
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
      -- True on the right can always be proven directly.
      apply True.intro
  case inr h8 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro
  -- Implications on the right can always be decomposed.
  intro h9
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_712840992615035187488973899217 : (((((p1 ∨ True) → ((p4 → p4) → p1)) ∨ ((p5 → (p2 → ((p3 ∧ p4) ∨ (((p4 ∨ p3) ∨ ((p5 ∨ p4) ∧ p2)) ∧ True)))) ∨ p4)) ∨ p5) ∧ True) := by
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
  -- Implications on the right can always be decomposed.
  intro h2
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- One of the premise coincides with the conclusion.
  exact h1
  -- One of the premise coincides with the conclusion.
  exact h2
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_188892862768056110854131525402 : ((((p1 ∨ (p1 ∨ p2)) ∨ True) → ((p5 ∨ p1) ∨ True)) ∧ ((((p1 ∧ (p2 ∨ p2)) → p4) ∨ p4) → (((False → p4) ∧ (False → p1)) → True))) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
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
      -- Disjunctions on the left can always be decomposed.
      cases h4
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
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro
  -- Implications on the right can always be decomposed.
  intro h8
  -- Implications on the right can always be decomposed.
  intro h9
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_166128320611664316812775965077 : ((True ∧ ((((p3 ∨ (False ∨ False)) ∨ (p5 ∧ p5)) ∧ False) ∨ (((p5 ∧ p3) ∨ False) ∨ True))) ∨ ((p4 ∨ ((True ∨ (p4 ∨ p4)) ∧ p4)) ∧ p1)) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
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
theorem thm_5_vars_208430117823749472427414319527 : (((p4 ∨ p1) ∨ ((p4 → p1) → p2)) → ((p4 ∨ False) ∨ (False ∨ (p1 → (((p4 ∨ p2) ∨ p1) ∨ (p3 → (p2 ∧ ((p4 ∨ p2) ∧ p5)))))))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h2 =>
    -- Disjunctions on the left can always be decomposed.
    cases h2
    case inl h3 =>
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- One of the premise coincides with the conclusion.
      exact h3
    case inr h4 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Implications on the right can always be decomposed.
      intro h5
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- One of the premise coincides with the conclusion.
      exact h5
  case inr h6 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h7
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h7



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_200938391547236178174732601250 : ((p1 ∨ (p5 ∨ ((True → (p2 → True)) → p4))) → (((True → (((False ∧ p5) → True) ∧ p1)) ∨ (p2 → p2)) ∧ (p2 ∨ (p4 ∨ (p2 ∨ True))))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
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
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Implications on the right can always be decomposed.
      intro h6
      -- One of the premise coincides with the conclusion.
      exact h6
    case inr h7 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Implications on the right can always be decomposed.
      intro h8
      -- One of the premise coincides with the conclusion.
      exact h8
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h9 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
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
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- True on the right can always be proven directly.
      apply True.intro
    case inr h12 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- True on the right can always be proven directly.
      apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_228864409666940641974410028229 : ((p3 ∨ (p5 → p2)) ∨ ((p1 → (((p3 ∨ False) ∧ (False ∨ (p1 → True))) ∨ (False ∧ (False ∨ ((p3 ∨ (False → p2)) → (p4 ∨ p2)))))) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_158560811025686072171768468862 : ((True ∧ ((p3 → (((p4 ∨ ((p3 ∧ ((False ∨ p3) ∧ p2)) ∨ p1)) ∨ (p4 ∧ False)) ∨ p2)) ∨ True)) ∨ (p2 → ((p5 → (True ∨ p3)) ∧ True))) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_157474732104558996816686835395 : ((((((p3 ∧ ((p5 → p3) ∧ p1)) → ((p3 → p5) ∧ True)) ∨ p3) ∧ (p1 ∨ p2)) ∨ (p5 → p1)) ∨ ((p5 ∨ (p1 ∨ (False ∨ True))) ∨ p4)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
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
theorem thm_5_vars_937379957735503919938164067092 : (((((p4 ∨ p4) ∧ (p5 ∧ (p5 → False))) ∧ ((p4 ∨ ((p2 ∧ (((p4 ∧ True) ∨ False) ∨ (True ∨ True))) ∨ (p3 ∨ p1))) ∧ (p5 ∧ p1))) → p2) ∧ True) := by
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
  cases h4
  case inl h6 =>
    -- Conjunctions on the left can always be decomposed.
    let h7 := h5.left
    let h8 := h5.right
    -- Conjunctions on the left can always be decomposed.
    let h9 := h3.left
    let h10 := h3.right
    -- Disjunctions on the left can always be decomposed.
    cases h9
    case inl h11 =>
      -- Conjunctions on the left can always be decomposed.
      let h12 := h10.left
      let h13 := h10.right
      -- We want to use the implication h8 based on <expert-advice>. So we show its premise.
      have h14 : p5 := by
        -- One of the premise coincides with the conclusion.
        exact h12
      -- We have shown the premise of h8, we can now drive its conclusion.
      let h15 := h8 h14
      -- False on the left can always be used.
      apply False.elim h15
    case inr h16 =>
      -- Disjunctions on the left can always be decomposed.
      cases h16
      case inl h17 =>
        -- Conjunctions on the left can always be decomposed.
        let h18 := h17.left
        let h19 := h17.right
        -- Disjunctions on the left can always be decomposed.
        cases h19
        case inl h20 =>
          -- Disjunctions on the left can always be decomposed.
          cases h20
          case inl h21 =>
            -- Conjunctions on the left can always be decomposed.
            let h22 := h21.left
            let h23 := h21.right
            -- Conjunctions on the left can always be decomposed.
            let h24 := h10.left
            let h25 := h10.right
            -- One of the premise coincides with the conclusion.
            exact h18
          case inr h26 =>
            -- False on the left can always be used.
            apply False.elim h26
        case inr h27 =>
          -- Disjunctions on the left can always be decomposed.
          cases h27
          case inl h28 =>
            -- Conjunctions on the left can always be decomposed.
            let h29 := h10.left
            let h30 := h10.right
            -- One of the premise coincides with the conclusion.
            exact h18
          case inr h31 =>
            -- Conjunctions on the left can always be decomposed.
            let h32 := h10.left
            let h33 := h10.right
            -- One of the premise coincides with the conclusion.
            exact h18
      case inr h34 =>
        -- Disjunctions on the left can always be decomposed.
        cases h34
        case inl h35 =>
          -- Conjunctions on the left can always be decomposed.
          let h36 := h10.left
          let h37 := h10.right
          -- We want to use the implication h8 based on <expert-advice>. So we show its premise.
          have h38 : p5 := by
            -- One of the premise coincides with the conclusion.
            exact h36
          -- We have shown the premise of h8, we can now drive its conclusion.
          let h39 := h8 h38
          -- False on the left can always be used.
          apply False.elim h39
        case inr h40 =>
          -- Conjunctions on the left can always be decomposed.
          let h41 := h10.left
          let h42 := h10.right
          -- We want to use the implication h8 based on <expert-advice>. So we show its premise.
          have h43 : p5 := by
            -- One of the premise coincides with the conclusion.
            exact h41
          -- We have shown the premise of h8, we can now drive its conclusion.
          let h44 := h8 h43
          -- False on the left can always be used.
          apply False.elim h44
  case inr h45 =>
    -- Conjunctions on the left can always be decomposed.
    let h46 := h5.left
    let h47 := h5.right
    -- Conjunctions on the left can always be decomposed.
    let h48 := h3.left
    let h49 := h3.right
    -- Disjunctions on the left can always be decomposed.
    cases h48
    case inl h50 =>
      -- Conjunctions on the left can always be decomposed.
      let h51 := h49.left
      let h52 := h49.right
      -- We want to use the implication h47 based on <expert-advice>. So we show its premise.
      have h53 : p5 := by
        -- One of the premise coincides with the conclusion.
        exact h51
      -- We have shown the premise of h47, we can now drive its conclusion.
      let h54 := h47 h53
      -- False on the left can always be used.
      apply False.elim h54
    case inr h55 =>
      -- Disjunctions on the left can always be decomposed.
      cases h55
      case inl h56 =>
        -- Conjunctions on the left can always be decomposed.
        let h57 := h56.left
        let h58 := h56.right
        -- Disjunctions on the left can always be decomposed.
        cases h58
        case inl h59 =>
          -- Disjunctions on the left can always be decomposed.
          cases h59
          case inl h60 =>
            -- Conjunctions on the left can always be decomposed.
            let h61 := h60.left
            let h62 := h60.right
            -- Conjunctions on the left can always be decomposed.
            let h63 := h49.left
            let h64 := h49.right
            -- One of the premise coincides with the conclusion.
            exact h57
          case inr h65 =>
            -- False on the left can always be used.
            apply False.elim h65
        case inr h66 =>
          -- Disjunctions on the left can always be decomposed.
          cases h66
          case inl h67 =>
            -- Conjunctions on the left can always be decomposed.
            let h68 := h49.left
            let h69 := h49.right
            -- One of the premise coincides with the conclusion.
            exact h57
          case inr h70 =>
            -- Conjunctions on the left can always be decomposed.
            let h71 := h49.left
            let h72 := h49.right
            -- One of the premise coincides with the conclusion.
            exact h57
      case inr h73 =>
        -- Disjunctions on the left can always be decomposed.
        cases h73
        case inl h74 =>
          -- Conjunctions on the left can always be decomposed.
          let h75 := h49.left
          let h76 := h49.right
          -- We want to use the implication h47 based on <expert-advice>. So we show its premise.
          have h77 : p5 := by
            -- One of the premise coincides with the conclusion.
            exact h75
          -- We have shown the premise of h47, we can now drive its conclusion.
          let h78 := h47 h77
          -- False on the left can always be used.
          apply False.elim h78
        case inr h79 =>
          -- Conjunctions on the left can always be decomposed.
          let h80 := h49.left
          let h81 := h49.right
          -- We want to use the implication h47 based on <expert-advice>. So we show its premise.
          have h82 : p5 := by
            -- One of the premise coincides with the conclusion.
            exact h80
          -- We have shown the premise of h47, we can now drive its conclusion.
          let h83 := h47 h82
          -- False on the left can always be used.
          apply False.elim h83
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_177901719308380758782890405996 : (((((p1 ∧ (p1 ∧ (False ∨ False))) ∨ (p1 ∧ p1)) ∨ (p3 ∨ p5)) ∨ p2) ∨ ((False ∨ (p5 → (((p2 ∨ p4) ∧ p4) → p4))) ∨ (p4 ∧ p3))) := by
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
  -- Conjunctions on the left can always be decomposed.
  let h3 := h2.left
  let h4 := h2.right
  -- Disjunctions on the left can always be decomposed.
  cases h3
  case inl h5 =>
    -- One of the premise coincides with the conclusion.
    exact h4
  case inr h6 =>
    -- One of the premise coincides with the conclusion.
    exact h4



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_112261225979003622048007145848 : (((p5 ∨ (((p3 → (((p2 → (True ∧ (p3 → ((False → True) → False)))) ∧ p4) ∧ (p1 ∧ False))) ∨ (True ∨ p3)) ∧ p3)) ∨ False) ∨ (False → True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_564017269359238519558334785 : (((p3 → (((((((p2 → (p5 ∧ (p1 ∨ False))) → p3) ∨ p2) ∨ True) ∧ p3) → p1) ∧ ((p2 → True) ∧ (True ∨ True)))) ∨ True) ∨ p1) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_68032372326875725121040501247 : ((p2 → (p2 ∧ (((((p3 ∨ True) ∨ p3) ∨ p1) → (p5 ∧ (p5 ∨ (p4 → (False ∧ (((p4 ∧ True) → True) ∧ False)))))) ∧ (p4 → p4)))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_813084783703483113372668527178 : ((((((True → False) ∧ (((p3 ∧ False) ∧ False) ∨ ((((p5 → p1) ∨ p1) ∧ ((p5 ∨ (p4 → (p1 ∧ p5))) ∨ p4)) → True))) ∧ p1) ∧ p1) → p4) ∧ True) := by
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
  -- Conjunctions on the left can always be decomposed.
  let h6 := h4.left
  let h7 := h4.right
  -- Disjunctions on the left can always be decomposed.
  cases h7
  case inl h8 =>
    -- Conjunctions on the left can always be decomposed.
    let h9 := h8.left
    let h10 := h8.right
    -- Conjunctions on the left can always be decomposed.
    let h11 := h9.left
    let h12 := h9.right
    -- False on the left can always be used.
    apply False.elim h12
  case inr h13 =>
    -- We want to use the implication h6 based on <expert-advice>. So we show its premise.
    have h14 : True := by
      -- True on the right can always be proven directly.
      apply True.intro
    -- We have shown the premise of h6, we can now drive its conclusion.
    let h15 := h6 h14
    -- False on the left can always be used.
    apply False.elim h15
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_178837872638956276233236119304 : ((((True ∨ False) ∨ p1) → (p1 ∧ (((True ∧ p4) ∧ p3) ∨ (p1 ∨ p1)))) ∨ ((((p2 → p1) ∧ p2) → (((p3 ∨ p1) ∨ p5) ∧ p2)) ∨ p2)) := by
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
  -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
  have h4 : p2 := by
    -- One of the premise coincides with the conclusion.
    exact h3
  -- We have shown the premise of h2, we can now drive its conclusion.
  let h5 := h2 h4
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h5
  -- Conjunctions on the left can always be decomposed.
  let h6 := h1.left
  let h7 := h1.right
  -- One of the premise coincides with the conclusion.
  exact h7



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_186847691690907309271590598084 : (((p4 ∧ (p1 ∧ (False ∨ p3))) ∨ ((p4 ∨ (p2 ∨ p1)) ∨ True)) → ((p4 → (True ∨ False)) → (((p2 ∨ True) ∧ (p3 ∧ (False ∨ False))) ∨ True))) := by
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
    -- Conjunctions on the left can always be decomposed.
    let h6 := h5.left
    let h7 := h5.right
    -- Disjunctions on the left can always be decomposed.
    cases h7
    case inl h8 =>
      -- False on the left can always be used.
      apply False.elim h8
    case inr h9 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- True on the right can always be proven directly.
      apply True.intro
  case inr h10 =>
    -- Disjunctions on the left can always be decomposed.
    cases h10
    case inl h11 =>
      -- Disjunctions on the left can always be decomposed.
      cases h11
      case inl h12 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- True on the right can always be proven directly.
        apply True.intro
      case inr h13 =>
        -- Disjunctions on the left can always be decomposed.
        cases h13
        case inl h14 =>
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- True on the right can always be proven directly.
          apply True.intro
        case inr h15 =>
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- True on the right can always be proven directly.
          apply True.intro
    case inr h16 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- True on the right can always be proven directly.
      apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_613071951430279983712993535984 : ((((((p3 ∧ ((p2 ∧ p2) → (((((p1 → p4) ∧ (False ∨ True)) → p1) ∨ (p1 ∨ p4)) ∧ (p2 ∧ p4)))) ∨ p1) → (p4 → p1)) ∨ False) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_138328297669339682653797736554 : ((p3 → (p2 ∨ (p4 ∨ (((((False ∨ (True ∨ p5)) ∧ p4) → p3) → False) ∨ (p5 → ((p2 ∨ False) ∨ (False ∧ p2))))))) ∨ ((p3 ∨ True) ∨ p5)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_137628688035615230038234071355 : ((False ∨ ((((False ∧ False) ∧ ((p2 ∨ (((p5 ∧ p2) ∧ p2) → ((p3 ∨ False) → True))) → True)) ∧ p5) ∧ (True → True))) ∨ ((p1 ∨ True) ∨ p2)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_317769652368078294195094853983 : (p4 ∨ (((p1 ∧ (((p4 ∧ p5) → p2) ∧ (((False → (False → p1)) → p5) ∧ True))) ∧ (p3 → (p4 → (True ∨ (p1 → (p1 ∨ True)))))) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_174799198703893826932532163291 : (((p5 ∨ p4) ∧ (p3 ∧ ((p1 → (False ∧ False)) ∧ ((p5 → p4) ∨ (True ∧ p2))))) → ((False → (True ∨ (p1 ∧ False))) → ((p1 ∨ p4) ∨ True))) := by
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
    let h6 := h4.left
    let h7 := h4.right
    -- Conjunctions on the left can always be decomposed.
    let h8 := h7.left
    let h9 := h7.right
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
  case inr h14 =>
    -- Conjunctions on the left can always be decomposed.
    let h15 := h4.left
    let h16 := h4.right
    -- Conjunctions on the left can always be decomposed.
    let h17 := h16.left
    let h18 := h16.right
    -- Disjunctions on the left can always be decomposed.
    cases h18
    case inl h19 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- True on the right can always be proven directly.
      apply True.intro
    case inr h20 =>
      -- Conjunctions on the left can always be decomposed.
      let h21 := h20.left
      let h22 := h20.right
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- True on the right can always be proven directly.
      apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_147869140616245859968262987726 : (((p3 → ((((((p2 → p4) → p4) ∨ p1) ∧ (p5 → ((p4 ∧ p5) → (p3 ∨ p1)))) ∨ p5) ∨ p3)) → p1) ∨ ((False → p2) ∨ (True → p4))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_134437008490232509152026182842 : (((((((((p4 ∨ (True → (False → p4))) ∧ p1) ∨ p1) → (True ∧ (p5 ∧ p3))) ∧ (p3 ∨ True)) ∧ p3) ∧ p5) → p2) ∨ ((p4 ∨ p4) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_729610367149478012176939965571 : (((((p5 ∨ p2) ∨ True) → (p4 ∧ (p3 ∨ ((((((p3 → (p5 ∧ p1)) ∧ (False → p4)) → p1) ∧ p5) ∧ (p4 ∧ p1)) ∨ (p3 ∨ False))))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_350358141234715949092488745437 : (p4 → ((p5 → ((p2 → p1) → (((((((p1 ∨ p5) → (False → ((p1 ∨ False) ∧ p1))) → p1) ∨ p4) → (p3 ∨ p4)) → False) ∨ p5))) ∨ p2)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h2
  -- Implications on the right can always be decomposed.
  intro h3
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_44760499239877747374985683103 : (((((p3 ∨ (False ∧ p4)) ∨ False) → (((((p1 ∧ (p2 ∧ ((p3 ∧ p4) ∧ ((p3 ∨ p3) ∧ p1)))) ∧ p4) ∧ p3) ∨ p3) → p1)) → p3) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_177781514580795594251856929609 : (((p4 ∧ ((((p4 ∨ p1) ∨ p5) ∨ ((False ∧ True) → False)) ∧ True)) ∧ p4) ∨ (((((True → False) ∧ False) ∨ p4) → True) ∨ (p2 ∨ (False ∨ p4)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_117632870545594326307540613570 : ((p3 ∧ ((((p4 ∧ p5) → (p4 ∨ p2)) ∧ ((False ∧ ((False ∨ ((p5 ∧ (p3 → p4)) → p2)) ∧ True)) ∨ (p2 → True))) ∨ p4)) ∨ (p4 → True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_337552556003978023113368163097 : (p1 → ((p5 ∧ ((p5 ∧ ((((p5 ∧ True) ∧ p5) → p3) → p2)) ∧ ((((p1 ∨ p5) → False) ∧ p5) ∧ p3))) ∨ ((p1 → p4) ∨ (p5 ∨ p1)))) := by
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
theorem thm_5_vars_218129360514231435935157763484 : (((p3 → False) ∧ (p3 → False)) → (((False → p1) ∧ (((False ∧ p3) ∨ p1) ∨ (p1 ∨ True))) ∨ ((((p4 ∨ False) ∨ True) ∨ (False ∧ p2)) ∧ p2))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h4
  -- False on the left can always be used.
  apply False.elim h4
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_56166729134643148763762362270 : (((p1 ∧ ((p4 ∨ p3) ∧ p3)) ∨ (((True ∧ (((p1 ∨ p2) ∨ p4) ∧ True)) ∧ True) ∨ (((p1 ∧ (p1 ∨ True)) ∨ False) → (False ∨ p1)))) ∨ p4) := by
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
    -- Conjunctions on the left can always be decomposed.
    let h3 := h2.left
    let h4 := h2.right
    -- Disjunctions on the left can always be decomposed.
    cases h4
    case inl h5 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- One of the premise coincides with the conclusion.
      exact h5
    case inr h6 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- One of the premise coincides with the conclusion.
      exact h3
  case inr h7 =>
    -- False on the left can always be used.
    apply False.elim h7



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_147941230994087791873891553805 : ((((p5 ∧ p1) ∧ ((p1 ∨ (p5 ∧ ((p4 ∧ ((p1 → p3) → p5)) → (True ∧ p5)))) ∨ p1)) ∧ (p3 → True)) ∨ (False → ((p5 ∨ p1) ∨ p4))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_625627625516367568655310482649 : ((((p1 → (((((p4 ∧ p3) ∧ p2) ∧ (((True → p5) ∨ (p5 → ((False ∧ p1) ∨ (p1 ∧ False)))) ∧ True)) ∨ (p1 → p5)) → False)) ∨ p5) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_69242079479309238685235682973 : ((p5 → ((p2 ∨ (p1 ∨ p2)) ∧ (((p2 → True) ∧ ((p4 ∧ (p1 ∧ (p3 ∨ (((p2 ∨ p2) → p1) ∨ p4)))) → p4)) ∧ (False ∧ p1)))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_162052989620060692185482856737 : ((p5 → ((((True ∨ p1) ∧ ((p4 → p4) → ((p1 ∧ (p5 ∧ (False → False))) ∨ p4))) → False) ∨ False)) → (p3 → (p5 → ((p4 ∨ p4) → p1)))) := by
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
    -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
    have h6 : p5 := by
      -- One of the premise coincides with the conclusion.
      exact h3
    -- We have shown the premise of h1, we can now drive its conclusion.
    let h7 := h1 h6
    -- Disjunctions on the left can always be decomposed.
    cases h7
    case inl h8 =>
      -- We want to use the implication h8 based on <expert-advice>. So we show its premise.
      have h9 : ((True ∨ p1) ∧ ((p4 → p4) → ((p1 ∧ (p5 ∧ (False → False))) ∨ p4))) := by
        -- Conjunctions on the right can always be decomposed.
        apply And.intro
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- True on the right can always be proven directly.
        apply True.intro
        -- Implications on the right can always be decomposed.
        intro h10
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- One of the premise coincides with the conclusion.
        exact h5
      -- We have shown the premise of h8, we can now drive its conclusion.
      let h11 := h8 h9
      -- False on the left can always be used.
      apply False.elim h11
    case inr h12 =>
      -- False on the left can always be used.
      apply False.elim h12
  case inr h13 =>
    -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
    have h14 : p5 := by
      -- One of the premise coincides with the conclusion.
      exact h3
    -- We have shown the premise of h1, we can now drive its conclusion.
    let h15 := h1 h14
    -- Disjunctions on the left can always be decomposed.
    cases h15
    case inl h16 =>
      -- We want to use the implication h16 based on <expert-advice>. So we show its premise.
      have h17 : ((True ∨ p1) ∧ ((p4 → p4) → ((p1 ∧ (p5 ∧ (False → False))) ∨ p4))) := by
        -- Conjunctions on the right can always be decomposed.
        apply And.intro
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- True on the right can always be proven directly.
        apply True.intro
        -- Implications on the right can always be decomposed.
        intro h18
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- One of the premise coincides with the conclusion.
        exact h13
      -- We have shown the premise of h16, we can now drive its conclusion.
      let h19 := h16 h17
      -- False on the left can always be used.
      apply False.elim h19
    case inr h20 =>
      -- False on the left can always be used.
      apply False.elim h20



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_57215009489001257574223878077 : ((((p2 → False) ∨ p5) ∨ ((((p2 → p1) → ((p2 ∨ (((p5 ∧ p2) → p5) → p1)) ∨ (True ∧ True))) ∧ p2) ∨ ((True ∨ False) ∨ p3))) ∨ False) := by
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
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_137158885328063069066269058613 : ((False ∧ ((True → (((p1 ∨ p5) ∧ ((((p4 ∨ (p4 ∧ (p3 ∨ (False → p1)))) ∨ p2) ∧ p3) ∨ True)) → p2)) ∨ False)) ∨ ((p3 → p3) ∨ p3)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_135095573427243015091962921096 : (((((((True ∧ False) ∧ (p2 → p3)) → False) ∧ p1) → (((p5 ∨ p5) → (False → (p5 → p1))) → False)) ∨ (p4 → p5)) ∨ (p3 ∨ (p2 → p2))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_177639386922475325448996972826 : ((((False ∧ ((p5 ∧ (p3 ∨ p4)) ∨ (p3 ∨ (p5 → p5)))) ∧ True) ∧ p4) ∨ (p5 → ((False ∨ p2) → ((p4 ∨ (p4 ∨ p2)) ∨ (p5 → p3))))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Disjunctions on the left can always be decomposed.
  cases h2
  case inl h3 =>
    -- False on the left can always be used.
    apply False.elim h3
  case inr h4 =>
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h4



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_314550573047695588978216447519 : (p3 ∨ (((p2 ∨ (p3 → ((p4 → False) ∧ p1))) → (True → (((True ∨ (p2 → p5)) ∧ False) ∧ False))) ∨ (p2 → (p4 ∨ (p4 → (p1 → p4)))))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
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
  -- One of the premise coincides with the conclusion.
  exact h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_344288399588998100611771416681 : (p2 → (p3 ∨ (((p1 → (True ∨ p2)) → ((False ∨ ((p3 ∨ ((p2 ∨ ((False ∧ p5) → (p5 ∨ p4))) ∨ p1)) ∨ p4)) ∧ (p4 ∧ p2))) ∨ p2))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_192921022518867838752256788342 : ((((True ∨ (p2 ∧ (p1 → False))) ∨ True) ∨ (p4 ∧ p3)) → (p1 → ((((p5 ∨ (p2 ∨ (((p1 ∧ p4) ∧ True) → p2))) ∧ True) ∧ p1) ∨ p1))) := by
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
        -- One of the premise coincides with the conclusion.
        exact h2
      case inr h6 =>
        -- Conjunctions on the left can always be decomposed.
        let h7 := h6.left
        let h8 := h6.right
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- One of the premise coincides with the conclusion.
        exact h2
    case inr h9 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- One of the premise coincides with the conclusion.
      exact h2
  case inr h10 =>
    -- Conjunctions on the left can always be decomposed.
    let h11 := h10.left
    let h12 := h10.right
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_607807206987118670321757917250 : (((((p3 ∨ (p4 ∧ ((False → p4) → (p5 → (((p1 ∧ False) ∨ False) ∨ ((p2 ∨ p4) → (p4 → ((p5 ∧ False) → p2)))))))) ∧ p3) ∨ True) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_159393440682948505731074651237 : (((((p1 ∧ ((p5 ∨ (p1 → p5)) ∧ (p4 ∨ ((False ∨ (p1 ∧ False)) ∧ p5)))) ∨ False) → p5) ∧ p5) → (((p2 → p4) ∨ p5) ∨ (p5 → p4))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h3



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_687891020639234393773963269854 : (((((((p5 ∨ p4) ∧ (True ∨ (p4 ∨ (p5 → False)))) → p2) → ((p4 → p4) → False)) ∧ ((p4 → (p4 ∧ ((p2 → p4) → p1))) ∨ False)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_175024516584713508409876065235 : ((p1 ∧ (((p2 ∧ p2) ∨ False) → ((p5 ∨ ((p3 → (p3 → p3)) ∧ True)) ∧ p4))) → (((p2 → (False → (p1 ∨ True))) → p2) → (p4 ∨ p5))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Conjunctions on the left can always be decomposed.
  let h3 := h1.left
  let h4 := h1.right
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
  have h5 : (p2 → (False → (p1 ∨ True))) := by
    -- Implications on the right can always be decomposed.
    intro h6
    -- Implications on the right can always be decomposed.
    intro h7
    -- False on the left can always be used.
    apply False.elim h7
  -- We have shown the premise of h2, we can now drive its conclusion.
  let h8 := h2 h5
  -- We want to use the implication h4 based on <expert-advice>. So we show its premise.
  have h9 : ((p2 ∧ p2) ∨ False) := by
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Conjunctions on the right can always be decomposed.
    apply And.intro
    -- One of the premise coincides with the conclusion.
    exact h8
    -- One of the premise coincides with the conclusion.
    exact h8
  -- We have shown the premise of h4, we can now drive its conclusion.
  let h10 := h4 h9
  -- We need to get the right conjuct of h10 based on <expert-advice>.
  let h11 := h10.right
  -- One of the premise coincides with the conclusion.
  exact h11



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_345174449240814875846396665335 : (p3 → (((p4 ∧ p3) ∨ (p4 ∨ ((p5 ∨ p3) ∧ ((p2 ∨ ((((((p1 → (p2 → p1)) ∧ p4) ∨ p4) → False) ∨ p4) ∧ p2)) ∨ True)))) ∧ True)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_608093994655867784357979964180 : (((((((p2 → (((p2 ∨ p2) ∨ (((p4 ∧ False) ∨ (False → (p2 → True))) ∧ p4)) → ((p1 ∨ p4) ∨ p5))) → False) ∧ p5) ∨ p3) ∨ True) ∨ p1) ∧ True) := by
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
theorem thm_5_vars_587020602577530894711437477349 : (((((p5 ∨ ((((False ∨ p2) ∨ (p5 ∨ (False → (p3 ∨ p2)))) ∨ p3) → ((((True ∧ p4) → (True ∨ p2)) ∨ True) ∧ p2))) ∧ p3) ∧ p5) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_308308559391464234004509285542 : (p2 ∨ ((p2 → ((p4 ∨ p5) ∨ (((p2 ∨ p5) → ((p2 ∧ p3) ∧ (p3 ∧ ((p4 ∧ (p5 ∧ ((False ∨ True) ∧ True))) ∧ p3)))) ∨ True))) ∧ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
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
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_117479000096824860911573333175 : ((p1 ∧ (p1 ∨ (((False ∨ ((True ∨ (((p2 ∧ p5) ∨ ((False → (True → True)) → p5)) → (p4 ∨ p4))) ∨ p2)) ∨ True) → p3))) ∨ (False → p4)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_352800934241333785511593051612 : (p4 → ((p2 ∨ p5) → (p5 ∨ (((((p5 ∨ p3) ∧ (p5 ∧ ((p4 ∧ (((True → True) ∨ (True → p3)) ∨ p2)) → p3))) ∧ True) ∧ p4) ∨ p2)))) := by
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
    -- One of the premise coincides with the conclusion.
    exact h3
  case inr h4 =>
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- One of the premise coincides with the conclusion.
    exact h4



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_114642064943667970919027193805 : ((((((p4 ∨ False) ∨ p1) → (((p2 ∨ (False → p5)) ∧ False) ∧ True)) ∧ (p2 → p1)) ∨ (((p2 ∨ p4) → p4) ∨ (p2 ∧ p2))) ∨ (p1 → p1)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_308364412370786792465641325066 : (p2 ∨ (((p1 → (p4 ∨ ((p4 ∧ p2) ∧ ((p5 ∨ ((p3 ∧ True) ∨ (((p2 ∨ (p4 ∧ p5)) ∨ (p2 ∨ p2)) ∨ p5))) ∨ p5)))) ∧ p2) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_124940645927665572476331355401 : ((((False ∧ p3) → (p1 ∧ p1)) → ((False ∨ (((p2 → (p3 ∧ True)) → False) → (((False ∧ (p4 ∧ p5)) → True) ∨ p5))) ∧ False)) → (p5 → p2)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h3 : ((False ∧ p3) → (p1 ∧ p1)) := by
    -- Implications on the right can always be decomposed.
    intro h4
    -- Conjunctions on the right can always be decomposed.
    apply And.intro
    -- Conjunctions on the left can always be decomposed.
    let h5 := h4.left
    let h6 := h4.right
    -- False on the left can always be used.
    apply False.elim h5
    -- Conjunctions on the left can always be decomposed.
    let h7 := h4.left
    let h8 := h4.right
    -- False on the left can always be used.
    apply False.elim h7
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h9 := h1 h3
  -- We need to get the right conjuct of h9 based on <expert-advice>.
  let h10 := h9.right
  -- False on the left can always be used.
  apply False.elim h10



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_248259248915637910734959533456 : ((p2 ∨ p2) ∨ ((((p2 ∨ False) ∨ (p4 ∨ p5)) ∨ ((True ∧ ((p2 ∧ (p1 → (((p1 ∨ p1) → False) → False))) ∧ p2)) ∨ (True → False))) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_706511157061592849975801224418 : ((((p5 ∨ ((p3 ∨ (p2 ∨ p2)) → (p4 ∧ p3))) ∧ ((False → (True ∧ p5)) → ((((True ∨ (p2 → True)) → (False ∧ p2)) ∨ True) ∧ p5))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_86636629958159435477578458145 : (((((p3 ∧ p3) ∨ p4) ∨ ((p2 ∧ p3) ∨ p3)) ∧ ((p3 → p4) ∧ ((p3 ∧ (True ∧ ((p1 → (False ∨ (p4 ∧ True))) ∨ p1))) → p5))) → p4) := by
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
      -- Conjunctions on the left can always be decomposed.
      let h8 := h3.left
      let h9 := h3.right
      -- We want to use the implication h8 based on <expert-advice>. So we show its premise.
      have h10 : p3 := by
        -- One of the premise coincides with the conclusion.
        exact h7
      -- We have shown the premise of h8, we can now drive its conclusion.
      let h11 := h8 h10
      -- One of the premise coincides with the conclusion.
      exact h11
    case inr h12 =>
      -- Conjunctions on the left can always be decomposed.
      let h13 := h3.left
      let h14 := h3.right
      -- One of the premise coincides with the conclusion.
      exact h12
  case inr h15 =>
    -- Disjunctions on the left can always be decomposed.
    cases h15
    case inl h16 =>
      -- Conjunctions on the left can always be decomposed.
      let h17 := h16.left
      let h18 := h16.right
      -- Conjunctions on the left can always be decomposed.
      let h19 := h3.left
      let h20 := h3.right
      -- We want to use the implication h19 based on <expert-advice>. So we show its premise.
      have h21 : p3 := by
        -- One of the premise coincides with the conclusion.
        exact h18
      -- We have shown the premise of h19, we can now drive its conclusion.
      let h22 := h19 h21
      -- One of the premise coincides with the conclusion.
      exact h22
    case inr h23 =>
      -- Conjunctions on the left can always be decomposed.
      let h24 := h3.left
      let h25 := h3.right
      -- We want to use the implication h24 based on <expert-advice>. So we show its premise.
      have h26 : p3 := by
        -- One of the premise coincides with the conclusion.
        exact h23
      -- We have shown the premise of h24, we can now drive its conclusion.
      let h27 := h24 h26
      -- One of the premise coincides with the conclusion.
      exact h27



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_173384444320937171273792864867 : ((p4 → ((p3 → (p1 ∨ ((((p2 → p4) ∧ p3) ∨ False) ∨ False))) ∧ (p5 ∨ p5))) ∨ ((p1 ∧ (((p3 ∧ p4) ∨ (p1 ∨ p1)) → p3)) → p3)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- We want to use the implication h3 based on <expert-advice>. So we show its premise.
  have h4 : ((p3 ∧ p4) ∨ (p1 ∨ p1)) := by
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- One of the premise coincides with the conclusion.
    exact h2
  -- We have shown the premise of h3, we can now drive its conclusion.
  let h5 := h3 h4
  -- One of the premise coincides with the conclusion.
  exact h5



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_264572603703443898555353736087 : (True ∧ ((p3 ∧ (p4 ∧ p1)) ∨ ((p2 ∨ ((p1 ∧ (False ∨ ((p1 → p2) ∧ False))) ∨ True)) ∨ (((p1 ∧ ((p3 ∧ p4) → False)) ∨ p4) ∨ p4)))) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- True on the right can always be proven directly.
  apply True.intro
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
theorem thm_5_vars_755826766034071854062891420071 : (((p1 ∧ ((((((p1 ∨ (((((p1 ∨ p2) ∧ p2) ∨ p4) ∨ p1) ∧ True)) ∨ ((False → p1) ∨ p1)) ∨ (p1 ∨ p1)) ∧ p1) ∧ p4) → p2)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_137817212458148483765176104158 : ((p3 ∨ ((((p4 ∨ ((p3 ∧ (p3 ∧ p5)) ∧ p3)) ∧ (p3 → (True ∨ p4))) ∨ (False → (p1 ∧ (p3 ∨ p1)))) ∨ p3)) ∨ ((p1 → p3) ∨ p4)) := by
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
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- False on the left can always be used.
  apply False.elim h1
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_44147262508105336466341867621 : (((((((((True → (True ∧ p4)) ∨ p2) ∧ ((True ∨ p3) ∧ (p4 ∨ (p4 → p2)))) ∧ p5) ∨ True) ∨ p5) → ((False ∨ False) ∧ True)) → p5) ∨ p5) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h2 : ((((((True → (True ∧ p4)) ∨ p2) ∧ ((True ∨ p3) ∧ (p4 ∨ (p4 → p2)))) ∧ p5) ∨ True) ∨ p5) := by
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h3 := h1 h2
  -- We need to get the left conjuct of h3 based on <expert-advice>.
  let h4 := h3.left
  -- Disjunctions on the left can always be decomposed.
  cases h4
  case inl h5 =>
    -- False on the left can always be used.
    apply False.elim h5
  case inr h6 =>
    -- False on the left can always be used.
    apply False.elim h6



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_164602050521293371209823863870 : (((True ∧ ((((p4 → p2) → p3) ∨ (p4 ∨ ((True ∨ True) → p3))) ∨ (p3 → p4))) ∧ p3) ∨ (True ∨ ((False ∨ ((p3 ∧ p3) ∨ p2)) → p4))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_111898119220139786471633723589 : ((((p1 → ((p3 ∨ p1) → (p5 → (((False → p2) → False) ∨ (False ∧ p5))))) ∨ ((p4 ∧ ((p5 ∧ p4) → p1)) → p4)) ∨ p1) ∨ (p3 → p1)) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
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
theorem thm_5_vars_731789125547388278515457821859 : ((((p3 → (False → False)) → ((((((p5 ∨ p2) ∧ p5) → (False → ((((True → p3) → p3) ∧ p3) → p3))) → (p4 → False)) ∨ p5) → p4)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_674128541031844309413001251413 : ((((p3 ∧ ((p3 ∨ ((((p2 ∧ p1) → (((False ∧ (True → True)) ∨ p4) ∧ p4)) → p5) ∨ False)) ∨ (True ∧ p5))) → (p2 ∧ (p2 ∨ p2))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_354644709232379332549124026789 : (p5 → (((((p2 ∧ ((p1 ∨ False) → ((True ∧ (True → (((False → p4) ∧ (p4 ∧ p3)) → (p4 ∧ True)))) ∨ p2))) → p3) → p2) → p2) ∨ p5)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_48755126508382318178808063802 : ((((p4 ∨ p2) ∧ (p1 ∨ (p2 ∨ ((p3 → ((((p1 ∧ False) → p3) ∨ p3) ∧ (p3 ∧ (False ∧ False)))) ∨ p2)))) ∧ (p2 ∨ (p3 ∧ p4))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_782441847811443372300718306154 : (((p3 ∨ (((((p5 → (True ∧ p1)) → False) → (True → (p4 → (((False → True) ∧ p3) → (p4 ∧ True))))) → (p5 ∨ (p5 ∧ p3))) ∨ p2)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



