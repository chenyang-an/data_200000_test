variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_327872604234292646346011171460 : (True → (((p5 → False) → ((p4 ∨ ((p4 ∨ (True ∨ p3)) → (p3 ∧ p4))) → (((((True ∨ p1) ∧ p1) ∧ p3) ∧ p3) ∨ False))) ∨ (p3 ∨ True))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_478450714575265664708016701783 : ((((False → ((((p5 ∧ p5) ∨ p5) ∧ (False ∨ p2)) ∨ True)) → (((False → p5) → (((p3 ∨ (p1 ∨ p2)) ∧ p2) ∧ p2)) ∨ (p1 → True))) ∧ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h2
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_619109495506794655075171812815 : (((((p2 ∧ (p3 → p2)) ∨ (((p1 ∨ ((p1 ∨ p1) ∨ ((((p4 ∨ p5) ∧ p2) ∧ p1) ∨ p5))) ∧ (p3 ∧ (p2 ∧ False))) ∧ p5)) ∨ True) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_350302301487940555189266452837 : (p4 → ((p2 ∨ (p3 ∧ (p3 ∨ ((((p1 ∨ (p4 → False)) ∨ p1) ∨ p2) → (p3 → ((p2 ∧ (((p3 ∧ True) ∧ False) ∨ p2)) ∧ True)))))) ∨ p4)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_629287202550593144982722665325 : (((((((((((p4 ∨ p4) ∨ (p1 ∨ (p4 → p5))) ∨ False) ∨ False) ∧ (p2 ∨ ((p3 ∧ p1) ∨ p4))) ∧ (False → False)) → p4) ∨ p3) → p2) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_56502439369312304316974430116 : (((p2 ∧ ((p4 → p5) → p2)) → (((((((p1 ∧ ((p2 ∨ p4) ∨ p2)) ∨ p4) → p1) → p5) ∧ p2) ∨ ((p2 → p1) ∨ False)) ∨ p2)) ∨ p4) := by
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
theorem thm_5_vars_57679291425750615092645148342 : ((((p2 → p3) ∨ p2) → (p3 ∨ (False ∨ (p1 ∨ ((True → (p1 ∨ True)) ∨ (((True → p5) ∧ True) → (((p5 ∨ p4) ∧ p1) → p2))))))) ∨ p2) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h2 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Implications on the right can always be decomposed.
    intro h3
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
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Implications on the right can always be decomposed.
    intro h5
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_141736992691321240992709214677 : (((True → False) ∧ (p5 → ((p4 ∨ ((p1 ∧ p5) → (True ∧ p1))) ∧ ((True → p4) ∧ (True → (p2 ∧ (p4 → p2))))))) → ((p4 ∨ p1) → False)) := by
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
    -- We want to use the implication h4 based on <expert-advice>. So we show its premise.
    have h6 : True := by
      -- True on the right can always be proven directly.
      apply True.intro
    -- We have shown the premise of h4, we can now drive its conclusion.
    let h7 := h4 h6
    -- False on the left can always be used.
    apply False.elim h7
  case inr h8 =>
    -- Conjunctions on the left can always be decomposed.
    let h9 := h1.left
    let h10 := h1.right
    -- We want to use the implication h9 based on <expert-advice>. So we show its premise.
    have h11 : True := by
      -- True on the right can always be proven directly.
      apply True.intro
    -- We have shown the premise of h9, we can now drive its conclusion.
    let h12 := h9 h11
    -- False on the left can always be used.
    apply False.elim h12



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_787072190010615918876112709000 : (((p4 ∨ ((p4 ∨ False) ∨ (((((True → p2) ∨ p1) ∧ (p4 ∧ p4)) ∨ True) ∧ ((((False ∧ p4) → (p2 → (p3 ∧ p4))) ∧ False) → True)))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_149807077197673718159486135016 : ((False ∨ (p5 ∨ ((p5 → ((((p3 → (p3 → (p5 → (p5 ∧ p5)))) ∧ p5) ∨ p2) ∨ p4)) → (p3 ∧ p1)))) ∨ (((p2 → True) → False) → p1)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h2 : (p2 → True) := by
    -- Implications on the right can always be decomposed.
    intro h3
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h4 := h1 h2
  -- False on the left can always be used.
  apply False.elim h4



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_685655404456473628807589258005 : ((((((((p5 ∧ False) ∨ False) → p1) ∧ (p1 → (p3 ∧ ((p5 ∨ (True ∨ p3)) ∧ False)))) ∨ p4) → ((p2 → p4) ∧ (False ∨ (p3 → p2)))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_177984198497677219502907858624 : (((p3 ∧ ((((p3 ∧ (p1 → p2)) → False) ∧ p3) ∨ (p4 → p2))) ∨ p5) ∨ (((p3 ∧ True) ∨ (p5 ∨ ((True ∨ (p2 ∨ p2)) → p3))) → True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_354972925570105258364110960770 : (p5 → ((p4 → (((False → (True → p5)) → ((True → p5) ∧ ((((((p3 ∧ p1) ∧ p1) ∨ False) → (p1 ∨ False)) ∧ p1) ∨ True))) → p1)) ∨ True)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_110326726902366849049307756004 : ((p2 → (p3 ∨ (((p5 ∨ (True ∧ False)) → p2) ∧ ((((p1 ∨ p3) ∧ (p5 ∧ p4)) ∧ (True ∧ (False ∧ (p1 ∨ p1)))) ∨ p2)))) ∧ (p2 → p2)) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h2
  -- Disjunctions on the left can always be decomposed.
  cases h2
  case inl h3 =>
    -- One of the premise coincides with the conclusion.
    exact h1
  case inr h4 =>
    -- Conjunctions on the left can always be decomposed.
    let h5 := h4.left
    let h6 := h4.right
    -- False on the left can always be used.
    apply False.elim h6
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h1
  -- Implications on the right can always be decomposed.
  intro h7
  -- One of the premise coincides with the conclusion.
  exact h7



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_54372968497236309717614370735 : (((False → (p5 → ((p3 ∧ (p4 ∧ True)) → p5))) ∧ (p5 ∧ (((p4 ∨ p3) ∧ ((False ∧ False) ∨ (p1 → p2))) ∧ (False ∨ (p2 ∨ p3))))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_58997280918029408246244801982 : (((p3 ∧ p1) ∨ ((((p3 → (p4 ∨ p2)) → (True ∧ (False → p3))) ∧ ((False ∨ ((p5 ∨ p5) → (p2 → p3))) ∨ True)) ∨ (p3 → p2))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_192277851382643918434480597233 : ((((p4 ∨ p4) ∧ (p4 ∧ ((p4 → p2) → p1))) ∧ p1) → ((((p5 ∧ p1) → p1) → (p5 ∨ ((p5 → False) → (False ∨ p5)))) ∨ (p1 ∧ True))) := by
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
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Conjunctions on the right can always be decomposed.
    apply And.intro
    -- One of the premise coincides with the conclusion.
    exact h3
    -- True on the right can always be proven directly.
    apply True.intro
  case inr h9 =>
    -- Conjunctions on the left can always be decomposed.
    let h10 := h5.left
    let h11 := h5.right
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Conjunctions on the right can always be decomposed.
    apply And.intro
    -- One of the premise coincides with the conclusion.
    exact h3
    -- True on the right can always be proven directly.
    apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_234632870011788916823855507564 : ((p3 → (p2 → p1)) → (((p5 → (((False ∨ ((p5 ∧ p4) → p5)) → p3) ∨ ((((p2 → False) ∨ p4) ∧ p2) → (p3 ∨ True)))) ∨ False) ∨ False)) := by
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
    -- True on the right can always be proven directly.
    apply True.intro
  case inr h7 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_230324135888351429674725373939 : (((p2 ∨ True) ∧ True) → ((((p1 ∧ p1) ∨ ((p4 ∨ (p5 ∧ ((((True ∧ True) ∧ False) ∨ (False ∨ p5)) ∨ p4))) ∧ p1)) ∨ p1) → (p5 ∨ p1))) := by
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
      -- Conjunctions on the left can always be decomposed.
      let h7 := h1.left
      let h8 := h1.right
      -- Disjunctions on the left can always be decomposed.
      cases h7
      case inl h9 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- One of the premise coincides with the conclusion.
        exact h6
      case inr h10 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- One of the premise coincides with the conclusion.
        exact h6
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
        -- Disjunctions on the left can always be decomposed.
        cases h15
        case inl h17 =>
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- One of the premise coincides with the conclusion.
          exact h13
        case inr h18 =>
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- One of the premise coincides with the conclusion.
          exact h13
      case inr h19 =>
        -- Conjunctions on the left can always be decomposed.
        let h20 := h19.left
        let h21 := h19.right
        -- Disjunctions on the left can always be decomposed.
        cases h21
        case inl h22 =>
          -- Disjunctions on the left can always be decomposed.
          cases h22
          case inl h23 =>
            -- Conjunctions on the left can always be decomposed.
            let h24 := h23.left
            let h25 := h23.right
            -- Conjunctions on the left can always be decomposed.
            let h26 := h24.left
            let h27 := h24.right
            -- False on the left can always be used.
            apply False.elim h25
          case inr h28 =>
            -- Disjunctions on the left can always be decomposed.
            cases h28
            case inl h29 =>
              -- False on the left can always be used.
              apply False.elim h29
            case inr h30 =>
              -- Conjunctions on the left can always be decomposed.
              let h31 := h1.left
              let h32 := h1.right
              -- Disjunctions on the left can always be decomposed.
              cases h31
              case inl h33 =>
                -- Show the left disjunct based on <expert-advice>.
                apply Or.inl
                -- One of the premise coincides with the conclusion.
                exact h30
              case inr h34 =>
                -- Show the left disjunct based on <expert-advice>.
                apply Or.inl
                -- One of the premise coincides with the conclusion.
                exact h30
        case inr h35 =>
          -- Conjunctions on the left can always be decomposed.
          let h36 := h1.left
          let h37 := h1.right
          -- Disjunctions on the left can always be decomposed.
          cases h36
          case inl h38 =>
            -- Show the left disjunct based on <expert-advice>.
            apply Or.inl
            -- One of the premise coincides with the conclusion.
            exact h20
          case inr h39 =>
            -- Show the left disjunct based on <expert-advice>.
            apply Or.inl
            -- One of the premise coincides with the conclusion.
            exact h20
  case inr h40 =>
    -- Conjunctions on the left can always be decomposed.
    let h41 := h1.left
    let h42 := h1.right
    -- Disjunctions on the left can always be decomposed.
    cases h41
    case inl h43 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- One of the premise coincides with the conclusion.
      exact h40
    case inr h44 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- One of the premise coincides with the conclusion.
      exact h40



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_328412342307204239991871122127 : (True → ((((p1 → True) ∧ (((p4 ∧ (p4 ∧ True)) ∨ ((p2 → True) ∧ p2)) ∧ p2)) ∨ (p1 ∧ p3)) ∨ ((True ∨ p5) ∧ ((True ∨ p3) ∨ p3)))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_178588254073377486790245535966 : ((((p2 ∧ ((True → p3) ∨ p5)) ∨ p5) ∨ (((p5 → True) → p2) ∨ p3)) ∨ (((False → ((((p5 ∧ p5) ∨ p3) → p3) ∧ p3)) ∨ True) ∧ True)) := by
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
theorem thm_5_vars_316995649862557305552989421594 : (p3 ∨ (p3 → (((((p2 ∨ (p1 ∧ False)) → (False ∨ p2)) → p1) ∧ (p2 → p3)) ∨ (((p1 ∧ (False → p5)) → (p4 ∧ p1)) ∨ (p1 → p3))))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h2
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_37502266140454918971481493817 : (((((p4 ∨ False) ∧ (((p4 ∨ False) → (p2 ∧ True)) → (((p1 → (p3 ∧ p1)) ∧ ((p5 → p4) → (False ∨ p4))) ∧ p1))) ∨ p4) ∧ True) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_78138228104755660910111183867 : (((p1 → (((((p4 → ((p4 → (p3 → p2)) ∧ p1)) ∧ p5) → (((((True → False) → p2) ∨ p5) ∧ p4) ∧ p4)) ∨ True) ∧ p1)) → False) → p5) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h2 : (p1 → (((((p4 → ((p4 → (p3 → p2)) ∧ p1)) ∧ p5) → (((((True → False) → p2) ∨ p5) ∧ p4) ∧ p4)) ∨ True) ∧ p1)) := by
    -- Implications on the right can always be decomposed.
    intro h3
    -- Conjunctions on the right can always be decomposed.
    apply And.intro
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro
    -- One of the premise coincides with the conclusion.
    exact h3
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h4 := h1 h2
  -- False on the left can always be used.
  apply False.elim h4



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_147786740942113396966109225416 : ((((p1 → p4) → (((False → ((p5 ∧ (True ∧ True)) ∨ (p3 ∧ True))) ∧ True) → (True → (p2 ∨ p4)))) → False) ∨ (p1 ∨ (p1 → (p1 ∨ p2)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_603188310933838445667541407172 : ((((p2 ∨ ((((((False ∧ ((((False → (p1 → p1)) ∨ p5) ∧ True) ∨ True)) → p5) → p3) ∨ p2) → p5) ∨ (True ∧ (p5 ∨ True)))) ∧ p1) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_112468371457707324260465868542 : ((((((p4 ∧ (p3 ∨ (p5 ∧ p1))) ∧ p3) → ((p3 ∨ (True ∧ p5)) ∨ (((False ∨ p3) ∨ p4) ∧ (p3 → p4)))) ∨ p5) → p1) ∨ (False → False)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_52097702217952686466664829644 : ((((((p5 ∨ p4) → p3) → ((((True ∨ (p4 ∧ p5)) ∨ p3) ∨ p3) ∧ p2)) ∨ True) → ((p3 ∨ p2) ∧ (p1 ∧ ((p4 ∧ p1) ∨ True)))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_160244431346975000847220346210 : ((((p4 ∨ (p4 ∨ p2)) ∨ ((True ∨ p3) ∧ ((False ∧ (p1 ∨ (p1 ∧ p2))) → p2))) ∨ (p1 → True)) → (p1 ∨ (False ∨ (p3 ∨ (False → p3))))) := by
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
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- Implications on the right can always be decomposed.
        intro h5
        -- False on the left can always be used.
        apply False.elim h5
      case inr h6 =>
        -- Disjunctions on the left can always be decomposed.
        cases h6
        case inl h7 =>
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- Implications on the right can always be decomposed.
          intro h8
          -- False on the left can always be used.
          apply False.elim h8
        case inr h9 =>
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- Implications on the right can always be decomposed.
          intro h10
          -- False on the left can always be used.
          apply False.elim h10
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
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- Implications on the right can always be decomposed.
        intro h15
        -- False on the left can always be used.
        apply False.elim h15
      case inr h16 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- One of the premise coincides with the conclusion.
        exact h16
  case inr h17 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h18
    -- False on the left can always be used.
    apply False.elim h18



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_116046417371728345427464681849 : (((False → ((p4 → p5) ∨ p4)) → (p4 ∨ ((True ∧ ((p5 ∨ (((p3 ∨ p4) ∨ p2) ∧ ((p2 ∨ p5) ∨ False))) ∨ p1)) → p3))) ∨ (p1 ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_305682577381151478603553251955 : (p1 ∨ (((p1 → p3) ∧ ((p5 → (p1 ∧ p1)) → (p1 → p4))) ∨ ((p4 → True) → ((((p4 ∨ False) ∧ True) ∧ False) ∨ (p5 ∨ (True ∧ True)))))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_245537027858233235168623787677 : ((p3 ∧ True) ∨ (((p2 ∧ p1) ∨ ((((p5 ∧ p3) ∧ (False ∧ p3)) ∨ ((False ∧ p1) ∨ ((p4 ∧ (True → True)) ∨ False))) ∧ p2)) ∨ (False → True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_54432522580507246643961825104 : ((((True ∧ (((True → p1) ∧ True) ∧ p2)) ∨ False) ∨ (True ∧ ((((p1 → (p4 ∨ p3)) ∨ True) ∨ ((p4 ∨ p5) ∧ p2)) ∨ (p2 ∧ False)))) ∨ p2) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_205616715152261144782411495141 : (((False ∧ p4) ∨ ((p1 ∨ p2) ∧ False)) ∨ (p2 ∨ (True → (p4 → (((p5 ∧ (False ∧ ((p2 ∧ p3) ∨ (p5 → p2)))) ∨ p3) → (False → True)))))) := by
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
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_787026084173094067904062750744 : (((p4 ∨ ((p5 → p3) ∧ ((p3 ∨ p2) ∧ (((p3 ∧ (False → ((p1 ∧ True) ∨ ((p5 ∧ (p3 ∨ True)) ∨ (p3 → p2))))) ∨ False) → p1)))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_134224278071171315725668776881 : ((((p3 ∧ (((p3 ∨ p5) ∧ p5) ∨ p2)) ∨ ((((p4 ∧ (True → (True ∧ False))) → p3) → True) ∨ (p2 → p4))) ∨ False) ∨ (p5 ∧ (False ∧ p4))) := by
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
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_620439077537467818022152263301 : (((((p5 ∨ p5) ∨ (p2 → ((p1 ∧ (p5 ∧ (p5 → (p5 → (False ∧ p1))))) ∨ ((((p4 ∨ (p5 → p3)) ∧ p1) ∨ p4) ∨ True)))) ∨ p1) ∨ p4) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
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
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_234424226413049063795425368216 : ((p2 → (False ∧ False)) → (((((p4 → True) ∧ ((p1 → (p2 ∧ p3)) ∧ (True ∨ (p3 ∧ p2)))) ∨ p1) ∧ (True → False)) ∨ (p2 → (p3 → p1)))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h2
  -- Implications on the right can always be decomposed.
  intro h3
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h4 : p2 := by
    -- One of the premise coincides with the conclusion.
    exact h2
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h5 := h1 h4
  -- We need to get the left conjuct of h5 based on <expert-advice>.
  let h6 := h5.left
  -- False on the left can always be used.
  apply False.elim h6



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_336402859557858137242862050359 : (p1 → ((p4 ∧ (((((p2 ∨ ((p3 → False) ∨ p2)) ∧ p2) ∧ p3) ∨ (((p1 → p5) → (p4 ∧ p3)) ∧ p1)) → (p3 ∨ (p2 ∨ False)))) ∨ True)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_146923510117519921367393534933 : ((((False ∧ (((((p1 ∨ p3) → ((p5 ∨ (p4 ∨ (True ∨ p5))) → False)) → p1) ∨ True) → p1)) ∧ True) ∧ p1) ∨ (((p3 ∧ p2) → p2) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_213514108887900279827752609179 : (((p4 → (p2 ∨ p3)) ∧ p5) ∨ (((p1 → (True ∧ p5)) → p3) ∨ (False → ((((False ∧ p5) → ((False → (p3 ∧ p1)) ∧ True)) ∧ p1) ∨ p2)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_147488058789024210976850617662 : (((p4 ∧ (p3 → ((p5 ∨ (p5 ∨ p4)) ∧ (True ∧ (p3 → (p5 → ((p4 → (p4 → p2)) ∨ False))))))) ∨ p3) ∨ ((p3 ∧ p4) → (True ∨ False))) := by
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



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_118726141171979502689394822385 : ((p5 ∨ ((p4 → ((p3 ∨ p1) ∨ ((False → p4) → ((False ∧ True) ∧ ((p1 → p5) ∧ (p5 ∨ p3)))))) → ((False ∧ p5) ∧ p5))) ∨ (False → p2)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_777215300339203953148137525890 : (((p1 ∨ ((((((((False ∨ (p5 ∨ p2)) ∨ p2) → p2) → (False ∧ (True ∧ p1))) → (p4 → p4)) ∧ True) → p4) ∨ (True ∧ (p1 → p5)))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_201119294383775854088895784490 : ((True → (p2 ∧ (p4 → (False ∧ (p4 → p2))))) → ((p1 ∧ (p2 → p5)) ∨ (((p1 → p4) → p2) ∧ ((p2 ∨ False) ∨ (p3 ∧ (False → p3)))))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h2
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h3 : True := by
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h4 := h1 h3
  -- We need to get the left conjuct of h4 based on <expert-advice>.
  let h5 := h4.left
  -- One of the premise coincides with the conclusion.
  exact h5
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h6 : True := by
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h7 := h1 h6
  -- We need to get the left conjuct of h7 based on <expert-advice>.
  let h8 := h7.left
  -- One of the premise coincides with the conclusion.
  exact h8



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_204553588477464007646332888495 : ((((False → (True ∨ p5)) → p4) ∨ p3) ∨ (p4 → ((True ∨ p5) ∧ (p2 → (True ∧ ((p2 → p2) ∧ (((p1 ∨ (p5 ∧ p3)) ∧ True) ∨ p4))))))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro
  -- Implications on the right can always be decomposed.
  intro h2
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h3
  -- One of the premise coincides with the conclusion.
  exact h2
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_884274887141058873956965283 : ((p1 → (((((p4 → (p1 ∧ (False → False))) ∨ ((((p2 ∧ (p3 → True)) ∧ p4) → False) → (p2 → True))) ∨ p4) → p5) ∨ True)) ∨ p2) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_740326837054428085723157934625 : ((((p1 ∨ p1) ∨ (((((p2 ∧ (p2 ∨ True)) ∨ p1) ∨ (p2 ∨ ((p2 → p5) ∨ p1))) → p3) ∧ (((p5 ∧ (True ∧ p3)) ∧ p2) → p1))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_208278252986602102706305295009 : (((False ∨ p5) ∧ (True → (p2 ∧ False))) → ((((True ∧ p3) → (p1 → ((((False → True) ∨ p3) ∧ (p2 ∧ p1)) → p5))) ∧ False) ∧ (p3 ∨ p1))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
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
  cases h5
  case inl h7 =>
    -- Conjunctions on the left can always be decomposed.
    let h8 := h6.left
    let h9 := h6.right
    -- Conjunctions on the left can always be decomposed.
    let h10 := h2.left
    let h11 := h2.right
    -- Conjunctions on the left can always be decomposed.
    let h12 := h1.left
    let h13 := h1.right
    -- Disjunctions on the left can always be decomposed.
    cases h12
    case inl h14 =>
      -- False on the left can always be used.
      apply False.elim h14
    case inr h15 =>
      -- One of the premise coincides with the conclusion.
      exact h15
  case inr h16 =>
    -- Conjunctions on the left can always be decomposed.
    let h17 := h6.left
    let h18 := h6.right
    -- Conjunctions on the left can always be decomposed.
    let h19 := h2.left
    let h20 := h2.right
    -- Conjunctions on the left can always be decomposed.
    let h21 := h1.left
    let h22 := h1.right
    -- Disjunctions on the left can always be decomposed.
    cases h21
    case inl h23 =>
      -- False on the left can always be used.
      apply False.elim h23
    case inr h24 =>
      -- One of the premise coincides with the conclusion.
      exact h24
  -- Conjunctions on the left can always be decomposed.
  let h25 := h1.left
  let h26 := h1.right
  -- Disjunctions on the left can always be decomposed.
  cases h25
  case inl h27 =>
    -- False on the left can always be used.
    apply False.elim h27
  case inr h28 =>
    -- We want to use the implication h26 based on <expert-advice>. So we show its premise.
    have h29 : True := by
      -- True on the right can always be proven directly.
      apply True.intro
    -- We have shown the premise of h26, we can now drive its conclusion.
    let h30 := h26 h29
    -- We need to get the right conjuct of h30 based on <expert-advice>.
    let h31 := h30.right
    -- False on the left can always be used.
    apply False.elim h31
  -- Conjunctions on the left can always be decomposed.
  let h32 := h1.left
  let h33 := h1.right
  -- Disjunctions on the left can always be decomposed.
  cases h32
  case inl h34 =>
    -- False on the left can always be used.
    apply False.elim h34
  case inr h35 =>
    -- We want to use the implication h33 based on <expert-advice>. So we show its premise.
    have h36 : True := by
      -- True on the right can always be proven directly.
      apply True.intro
    -- We have shown the premise of h33, we can now drive its conclusion.
    let h37 := h33 h36
    -- We need to get the right conjuct of h37 based on <expert-advice>.
    let h38 := h37.right
    -- False on the left can always be used.
    apply False.elim h38



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_301415350050788573665328842492 : (False ∨ (((p3 ∨ (True ∧ p3)) ∨ p4) → ((((p1 → (p1 ∨ p1)) → ((p5 → p4) ∧ p2)) → (p4 ∨ (p3 ∧ (False ∧ p1)))) ∨ (False ∨ p3)))) := by
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
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- One of the premise coincides with the conclusion.
      exact h3
    case inr h4 =>
      -- Conjunctions on the left can always be decomposed.
      let h5 := h4.left
      let h6 := h4.right
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- One of the premise coincides with the conclusion.
      exact h6
  case inr h7 =>
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Implications on the right can always be decomposed.
    intro h8
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- One of the premise coincides with the conclusion.
    exact h7



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_135661757942931155097343789639 : (((True ∧ (((((p4 ∨ (False ∨ p2)) ∨ True) ∧ (p2 → (False ∨ False))) ∨ False) ∧ p4)) → ((False ∧ (p1 → p5)) ∨ False)) ∨ (p2 → (p4 ∨ p2))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_136495532867066568176079934623 : ((((p2 ∨ p5) → False) ∧ ((((p3 ∨ p4) ∧ p1) ∨ ((p2 ∧ p5) ∨ p5)) ∧ (p5 ∨ (((p4 → p5) ∧ p1) ∨ p5)))) ∨ ((p3 ∧ p2) → p3)) := by
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
theorem thm_5_vars_246091014795504658357905065087 : ((p4 ∧ p1) ∨ (((p2 ∧ (((p1 ∨ (p3 ∨ True)) → p2) ∨ p3)) ∧ (((True ∧ p5) → p2) → p1)) ∨ (((p5 ∧ p3) ∨ True) → (True ∨ p5)))) := by
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
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- True on the right can always be proven directly.
    apply True.intro
  case inr h5 =>
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- True on the right can always be proven directly.
    apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_663927455642980272728772666515 : ((((p4 ∧ ((p1 ∧ ((False ∨ (((p5 ∧ p1) ∧ p2) ∨ ((p5 → p4) ∨ (True ∨ (p1 ∧ p2))))) ∨ p3)) → (p3 ∧ p5))) → (p3 ∨ p1)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_167070664073793073244279526819 : ((((((p2 → p5) ∧ ((p4 ∨ (((p4 → p2) ∨ p4) ∨ p3)) ∨ True)) ∨ p4) → p4) ∨ True) → ((p5 ∨ (True ∨ ((p5 ∨ p5) → p1))) ∨ p4)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h2 =>
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- True on the right can always be proven directly.
    apply True.intro
  case inr h3 =>
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- True on the right can always be proven directly.
    apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_610435967507013690035978395208 : ((((((((True → p3) → (True ∨ p5)) ∨ (p1 ∨ (True ∧ (((p2 ∨ False) ∧ (p5 → (False ∧ p1))) ∨ (False ∨ p1))))) → p1) → p3) ∨ True) ∨ p5) ∧ True) := by
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
theorem thm_5_vars_45467203412714201377639368961 : (((False ∨ (((((True → p5) ∨ p1) ∨ p4) ∧ ((p3 → (p4 ∨ ((p1 → False) ∧ (True → (True ∨ p3))))) ∨ (p1 → p4))) ∨ True)) → p5) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_115343900261042420565045205005 : (((p1 → (((False ∨ True) → (p2 ∨ (p4 → p5))) ∨ p4)) → (((p4 ∨ (False ∧ (p5 ∨ p1))) ∧ p5) ∨ (p2 ∨ (p3 → p3)))) ∨ (p3 ∨ p2)) := by
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
  -- One of the premise coincides with the conclusion.
  exact h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_111643910480709065037843092114 : (((((p1 ∧ (p2 ∧ (p5 ∧ p2))) ∨ ((p2 ∧ (False ∨ (False ∨ p1))) ∧ (((p1 → (p2 → p3)) → p5) ∨ p5))) ∨ False) ∨ True) ∨ (False ∧ p5)) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_64813832634376345786817497170 : ((p2 ∨ ((((((p4 → p2) ∨ (((p1 ∧ False) → True) → (p3 ∨ ((p2 → ((p4 → True) ∨ p3)) ∧ p2)))) ∧ p2) ∨ p4) ∨ p2) → False)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_641553976315423334792976836846 : (((((p3 ∧ True) → (((True ∨ (((p1 ∧ p3) ∧ p3) ∨ ((p3 ∨ p4) ∨ True))) ∨ (p3 ∨ p4)) ∨ ((p1 ∧ (p1 ∧ p1)) ∧ p5))) → p5) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_644841269653199961329600114026 : ((((p2 ∨ (((True ∨ p5) ∧ (((p4 ∧ (p1 ∨ p2)) ∧ ((p2 ∧ p2) → (p5 ∨ ((p1 ∨ p3) → p4)))) → p3)) → (p4 ∧ p4))) → p4) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_321065519754405614894351998154 : (p4 ∨ (p1 ∨ ((((p2 ∧ p4) ∨ p2) → ((((p4 ∨ (True ∧ p3)) → ((p1 ∧ p3) ∧ False)) ∨ (p5 ∨ p4)) ∨ True)) ∨ ((p3 → p1) → p4)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
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
theorem thm_5_vars_623881198212239980373684210587 : ((((p1 ∨ (p3 ∨ (p5 ∨ ((p3 → (p3 ∧ (((((p2 → p5) ∧ (p4 ∨ False)) → p2) ∧ p2) ∨ True))) ∨ (p3 ∨ (p5 ∨ True)))))) ∨ p5) ∨ p1) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
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
theorem thm_5_vars_59257000437762148266935636037 : (((p2 ∨ p5) ∨ ((((p5 ∧ p5) → (p3 ∧ (p3 ∧ p4))) → (False ∨ p1)) → ((False → ((False → (p4 → False)) → (p5 ∧ p5))) → p4))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_314493019173143187141361305061 : (p3 ∨ ((p5 → (((p5 ∨ p1) → False) ∨ (p5 → (p2 → (True ∧ (p5 ∨ (False ∧ ((p4 → True) → p5)))))))) → ((True → (p5 ∧ p2)) → p2))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
  have h3 : True := by
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h2, we can now drive its conclusion.
  let h4 := h2 h3
  -- We need to get the right conjuct of h4 based on <expert-advice>.
  let h5 := h4.right
  -- One of the premise coincides with the conclusion.
  exact h5



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_111055852216880672083195773980 : ((((p2 ∨ (p5 ∨ ((p3 → (p5 → (((p5 ∨ p1) ∨ p5) → (p1 → p4)))) → p4))) → (((p4 ∨ p2) ∨ p5) → p5)) ∧ p3) ∨ (p4 → True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_147592963983210759872541258034 : ((((((True → ((((p3 → (p2 ∧ p1)) → (False ∧ p1)) ∧ (p4 ∨ p1)) ∧ p1)) → p3) → True) ∨ p3) → p2) ∨ ((False → (p3 ∧ p3)) ∨ p3)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- False on the left can always be used.
  apply False.elim h1
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_610454401739941436563364667804 : (((((((p1 ∨ p4) ∨ (((((((p4 ∨ p3) ∨ p1) → p5) ∨ True) ∧ (p5 ∨ (p1 ∧ (p5 → p1)))) ∧ p3) ∨ False)) → p4) → p3) ∨ True) ∨ p4) ∧ True) := by
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
theorem thm_5_vars_246621748840640358939632921140 : ((p5 ∧ p3) ∨ ((p3 → (p5 ∧ (False ∧ ((p4 ∨ (((p1 ∨ p5) ∧ p5) ∨ p4)) ∨ (p2 → (((p1 ∨ False) ∧ (p2 → True)) ∧ False)))))) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_662340546603167897691868671288 : (((((True ∧ ((p5 ∨ ((False ∨ p5) ∧ True)) → False)) ∧ (((False → p4) ∨ (p5 ∧ (False ∨ False))) → ((p4 ∨ p4) ∧ p5))) → (p5 ∨ False)) ∨ p2) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
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
  -- We want to use the implication h3 based on <expert-advice>. So we show its premise.
  have h6 : ((False → p4) ∨ (p5 ∧ (False ∨ False))) := by
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Implications on the right can always be decomposed.
    intro h7
    -- False on the left can always be used.
    apply False.elim h7
  -- We have shown the premise of h3, we can now drive its conclusion.
  let h8 := h3 h6
  -- We need to get the right conjuct of h8 based on <expert-advice>.
  let h9 := h8.right
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- One of the premise coincides with the conclusion.
  exact h9
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_3011282911020071781524291609 : (((True ∧ p3) → p4) → (((p4 ∧ p1) ∧ (p4 ∨ (p1 → ((((p1 → ((False → True) ∨ p1)) ∧ p4) ∧ False) ∧ p2)))) ∨ (p1 → True))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h2
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_117215313140219617007342247802 : ((True ∧ ((p3 → (p2 ∧ p4)) ∧ ((p2 ∨ (True → (p4 ∨ p4))) → (p2 ∧ (p2 → ((False → ((p5 → p5) ∧ p4)) → False)))))) ∨ (True ∨ p1)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_158079621951143911686180933539 : ((((True ∧ True) ∨ (p3 ∧ (p1 → p1))) → ((p2 ∧ ((p4 ∨ False) → True)) ∧ ((True ∧ p1) ∨ p4))) ∨ ((((True → p3) ∨ p4) ∨ p4) → True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_114391912293472356651838247577 : (((((p3 ∨ p4) ∨ ((p3 → (p3 → p1)) ∧ (p4 ∨ (p1 ∧ p2)))) ∧ ((p5 ∧ p1) → p5)) ∨ (p2 ∨ ((p2 ∨ p1) ∨ False))) ∨ (p2 → p2)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_137417899925565225196210314820 : ((p4 ∧ ((((True ∨ ((((p3 ∨ ((False ∧ p2) → True)) ∧ (p4 → True)) → p5) ∧ (p1 ∨ p4))) → False) ∧ p2) ∨ p3)) ∨ (True ∨ (p2 ∧ p2))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_691969529971227064816647045903 : ((((p5 → (((((p1 ∧ True) ∨ (False → (True ∧ p5))) ∧ p1) ∧ (p5 ∨ p3)) ∨ False)) → (False ∨ ((p4 ∧ (p4 ∨ False)) ∨ (False ∧ p3)))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_303769877423926362330335695542 : (p1 ∨ ((((False ∧ p4) ∨ (False ∧ (((p1 → (p3 ∨ (((False ∨ p2) ∨ p3) → (True ∧ (True ∧ p1))))) → (False → p2)) ∧ p2))) ∨ p4) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_603269066075006985394657096138 : ((((p2 ∨ ((p1 ∧ p2) ∨ ((((False ∨ ((p2 ∧ (p2 ∧ p1)) ∨ p2)) ∧ (True ∧ p2)) ∧ p5) ∨ (((False ∧ p4) ∧ p3) ∨ p5)))) ∧ p4) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_130137647954270668282185648346 : ((((((p5 ∨ False) ∧ (True ∨ p4)) → True) ∧ ((p1 ∨ (p2 → p5)) → ((p5 ∨ (p4 ∧ p5)) ∨ True))) ∨ (True ∨ p3)) ∧ (p4 → (p5 ∨ p4))) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_233212281014801613203041244263 : ((p5 ∧ (p1 → p3)) → ((p5 ∧ p2) ∨ (((p4 ∨ (p2 ∧ p1)) ∨ (p1 ∨ ((((p3 → False) ∧ p1) ∧ p4) → p2))) ∨ (p3 ∧ (True → p3))))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h4
  -- Conjunctions on the left can always be decomposed.
  let h5 := h4.left
  let h6 := h4.right
  -- Conjunctions on the left can always be decomposed.
  let h7 := h5.left
  let h8 := h5.right
  -- We want to use the implication h7 based on <expert-advice>. So we show its premise.
  have h9 : p3 := by
    -- We want to use the implication h3 based on <expert-advice>. So we show its premise.
    have h10 : p1 := by
      -- One of the premise coincides with the conclusion.
      exact h8
    -- We have shown the premise of h3, we can now drive its conclusion.
    let h11 := h3 h10
    -- One of the premise coincides with the conclusion.
    exact h11
  -- We have shown the premise of h7, we can now drive its conclusion.
  let h12 := h7 h9
  -- False on the left can always be used.
  apply False.elim h12



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_738572443392124310906423233761 : ((((p1 ∧ p5) ∨ (p3 ∨ (((p2 ∧ (p3 ∧ ((p5 ∨ p5) → (p3 → (((p4 → p3) ∨ (True ∧ p5)) ∨ True))))) → (False ∧ p2)) ∨ False))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_208594368670480124519529644570 : (((p2 → p4) → ((p5 ∧ p5) ∧ p3)) → (((p3 ∧ (False ∨ (False ∧ p4))) → p3) → ((((((p4 → p3) → False) ∧ p1) ∨ True) ∧ True) ∨ p1))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_343493158384168488665182352190 : (p2 → ((True ∧ True) → (((p4 ∨ ((((((True ∧ p2) ∨ (False ∨ p3)) ∨ ((False → (p5 → True)) ∨ True)) ∨ p2) → True) → p3)) ∨ p2) ∨ p1))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Conjunctions on the left can always be decomposed.
  let h3 := h2.left
  let h4 := h2.right
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_668682013317435555565610753746 : (((((((p3 ∧ (((p3 ∧ (False → True)) ∨ (p3 → True)) ∨ (False ∧ (p2 → (p1 → p5))))) ∧ False) ∧ p3) ∨ p4) ∨ (p5 → (p2 ∨ True))) ∨ p4) ∧ True) := by
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
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_626622944566653908822115217603 : ((((p4 → (False ∨ ((((p3 → ((((((p4 → p5) ∨ p2) → (p1 ∨ True)) ∨ p2) ∨ p1) → True)) → (p2 ∨ p3)) ∨ p5) → p1))) ∨ True) ∨ p1) ∧ True) := by
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
theorem thm_5_vars_53480018108163725472004943150 : (((p2 ∧ ((p4 ∨ (((p5 ∧ (p1 ∧ p1)) ∧ p1) → p1)) ∧ p1)) → (((p3 ∨ p4) ∨ False) → ((p3 → (p1 ∨ (False → p5))) ∧ False))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_53750308521201113971613829995 : ((((((p4 → False) → ((False → p4) ∨ False)) → p4) ∧ p1) ∨ (((((((p4 ∧ True) → True) → (p3 ∨ p1)) → p1) → p1) → p5) ∨ p1)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_116682256417489222950795892945 : (((True ∧ False) ∨ ((p2 ∧ (p1 → (((p1 ∨ (((p5 ∧ (p3 ∧ p1)) → p3) ∧ False)) → False) ∨ (True ∧ (p3 ∧ False))))) ∨ True)) ∨ (p3 ∨ False)) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_249442426838985324847863118842 : ((p5 ∨ False) ∨ ((p3 → (p2 ∨ p5)) ∨ ((p5 ∨ ((True ∧ (((p2 → (False ∧ p3)) ∧ ((False → False) ∨ (p3 → p5))) ∨ p5)) ∨ True)) ∨ p4))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
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
theorem thm_5_vars_114737881512517706533910291471 : ((((False ∨ (p4 → p5)) ∧ ((((p2 ∧ (p1 → p4)) → p4) ∧ (True ∨ p4)) ∨ p1)) → ((False ∧ (False ∨ (p1 ∧ p3))) ∧ True)) ∨ (True ∨ p5)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_872457398596928414641635720337 : ((((True → (((p4 ∨ (((False ∨ p2) ∨ p5) ∨ False)) ∨ (p5 ∨ (False → (((p5 ∧ p2) ∧ True) → (True → p1))))) ∧ (p3 ∨ True))) → p1) → p1) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h1
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h2 : (True → (((p4 ∨ (((False ∨ p2) ∨ p5) ∨ False)) ∨ (p5 ∨ (False → (((p5 ∧ p2) ∧ True) → (True → p1))))) ∧ (p3 ∨ True))) := by
    -- Implications on the right can always be decomposed.
    intro h3
    -- Conjunctions on the right can always be decomposed.
    apply And.intro
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h4
    -- Implications on the right can always be decomposed.
    intro h5
    -- Implications on the right can always be decomposed.
    intro h6
    -- Conjunctions on the left can always be decomposed.
    let h7 := h5.left
    let h8 := h5.right
    -- Conjunctions on the left can always be decomposed.
    let h9 := h7.left
    let h10 := h7.right
    -- False on the left can always be used.
    apply False.elim h4
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h11 := h1 h2
  -- One of the premise coincides with the conclusion.
  exact h11
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_179478615216426071503670142752 : ((True → ((((((True ∨ p5) → p5) ∨ p3) → True) ∨ p2) → (p2 ∨ p5))) ∨ ((p5 → p5) ∨ (((p5 ∧ (p5 ∧ p3)) → p3) ∧ (True ∨ True)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_147833867486780167473594124031 : (((p2 ∨ ((p5 ∨ (p2 → ((((False ∨ (p5 → True)) → p2) → (p4 → (p4 ∨ p1))) → False))) ∨ p4)) → p5) ∨ (p3 ∨ ((p1 ∧ p4) ∨ True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_323185408575069780282713382324 : (p5 ∨ (((p4 ∨ (((p4 ∧ p1) ∨ ((False ∧ (False → (((True ∨ True) → p4) ∧ p2))) ∨ (p4 ∨ p2))) ∨ (p3 → p5))) ∨ p4) ∨ (p2 → True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_156636890170373108725006123654 : ((((p5 ∧ ((p5 ∨ p5) ∨ ((p1 ∧ ((True ∨ ((p2 ∧ p3) ∧ p3)) → p5)) → False))) ∨ False) ∧ True) ∨ (False ∨ (True ∧ (p3 ∨ (p3 → True))))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_590536497657606451550980670429 : (((((True ∧ ((((((p2 → (p4 → (p3 → p1))) → False) → p5) ∨ ((p3 ∧ ((p4 ∧ p1) → p1)) ∨ p3)) → p4) → p2)) → p1) ∧ p1) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_64252942261832682275547935207 : ((False ∨ (p3 ∨ ((p2 ∨ (p1 ∧ (False ∧ True))) ∧ ((((p4 ∨ ((p5 ∧ True) ∨ p4)) ∧ (((p1 ∨ p5) → True) ∧ p1)) → True) ∨ p1)))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_326296061179879900736702155584 : (p5 ∨ (p4 → ((p1 ∨ ((True ∧ (p5 ∨ (True ∨ (True ∨ ((((p3 ∨ p4) ∧ (p2 ∨ p1)) ∧ p4) → p2))))) → False)) ∨ (False → (False ∨ True))))) := by
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
theorem thm_5_vars_53460175642262536530380520385 : ((((False ∨ p4) ∨ ((True ∧ p2) ∧ ((True ∨ p5) ∧ (False ∨ True)))) → (((p2 ∨ (p5 → p1)) → ((False ∨ (p3 ∨ p2)) → p4)) ∨ True)) ∨ p1) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h2 =>
    -- Disjunctions on the left can always be decomposed.
    cases h2
    case inl h3 =>
      -- False on the left can always be used.
      apply False.elim h3
    case inr h4 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- True on the right can always be proven directly.
      apply True.intro
  case inr h5 =>
    -- Conjunctions on the left can always be decomposed.
    let h6 := h5.left
    let h7 := h5.right
    -- Conjunctions on the left can always be decomposed.
    let h8 := h6.left
    let h9 := h6.right
    -- Conjunctions on the left can always be decomposed.
    let h10 := h7.left
    let h11 := h7.right
    -- Disjunctions on the left can always be decomposed.
    cases h10
    case inl h12 =>
      -- Disjunctions on the left can always be decomposed.
      cases h11
      case inl h13 =>
        -- False on the left can always be used.
        apply False.elim h13
      case inr h14 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- True on the right can always be proven directly.
        apply True.intro
    case inr h15 =>
      -- Disjunctions on the left can always be decomposed.
      cases h11
      case inl h16 =>
        -- False on the left can always be used.
        apply False.elim h16
      case inr h17 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- True on the right can always be proven directly.
        apply True.intro



