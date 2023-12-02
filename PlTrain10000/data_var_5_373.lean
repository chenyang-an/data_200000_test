variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_68669844059570773987118969363 : ((p4 → ((p2 ∨ (p1 → (p1 ∧ (((True ∨ p5) ∧ (p4 → False)) → (False ∧ ((p5 ∧ p5) → (((True ∧ p1) ∨ p5) → p4))))))) → p2)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_140111800669538239376846437363 : (((p1 → ((p4 ∧ (True ∨ ((p4 → (p3 ∧ True)) ∧ (p1 ∧ p3)))) → (((p3 → p5) → p1) ∨ p5))) ∨ (p5 ∨ p5)) → ((p2 ∧ p2) ∨ True)) := by
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



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_164840605894583316042588207721 : (((p2 ∧ (True → (p3 ∨ (p4 ∨ (p1 ∧ ((p1 → p1) ∧ (p3 ∧ (p1 ∨ True)))))))) ∨ True) ∨ (p2 → ((p2 ∨ (p5 → False)) ∨ (p4 ∧ False)))) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_95718365567451327819613624399 : ((p5 ∧ (p2 ∧ ((p5 → ((((p3 → True) → (p4 ∨ (p4 → p3))) ∨ True) ∧ (True → False))) ∧ ((True → (p3 ∧ p3)) ∨ (p4 ∧ p5))))) → p3) := by
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
  cases h7
  case inl h8 =>
    -- We want to use the implication h8 based on <expert-advice>. So we show its premise.
    have h9 : True := by
      -- True on the right can always be proven directly.
      apply True.intro
    -- We have shown the premise of h8, we can now drive its conclusion.
    let h10 := h8 h9
    -- We need to get the left conjuct of h10 based on <expert-advice>.
    let h11 := h10.left
    -- One of the premise coincides with the conclusion.
    exact h11
  case inr h12 =>
    -- Conjunctions on the left can always be decomposed.
    let h13 := h12.left
    let h14 := h12.right
    -- We want to use the implication h6 based on <expert-advice>. So we show its premise.
    have h15 : p5 := by
      -- One of the premise coincides with the conclusion.
      exact h14
    -- We have shown the premise of h6, we can now drive its conclusion.
    let h16 := h6 h15
    -- We need to get the right conjuct of h16 based on <expert-advice>.
    let h17 := h16.right
    -- We want to use the implication h17 based on <expert-advice>. So we show its premise.
    have h18 : True := by
      -- True on the right can always be proven directly.
      apply True.intro
    -- We have shown the premise of h17, we can now drive its conclusion.
    let h19 := h17 h18
    -- False on the left can always be used.
    apply False.elim h19



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_115967343828590052330497497305 : (((((False ∧ False) → True) ∧ p5) → ((p2 ∧ (False → (p5 ∧ (((True ∧ p1) → p5) → False)))) ∧ (p2 ∧ ((p2 ∨ True) ∧ False)))) ∨ (True ∨ p3)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_200091824849837332272086301355 : ((((p2 ∧ p1) → p5) ∧ ((False ∨ p2) ∧ p4)) → (((False ∨ True) → (p1 ∧ (p3 ∧ (True → (((True ∨ p4) → True) → (True ∧ p5)))))) ∨ True)) := by
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
    apply False.elim h6
  case inr h7 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_76750297352672331058864094666 : ((((((p5 ∧ (p3 ∧ p2)) ∨ p1) ∧ ((p1 ∧ (True ∧ False)) ∨ (p4 → p3))) ∨ (True ∧ ((p5 ∧ (p5 ∧ (False ∧ p2))) → p4))) → p1) → p1) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h2 : ((((p5 ∧ (p3 ∧ p2)) ∨ p1) ∧ ((p1 ∧ (True ∧ False)) ∨ (p4 → p3))) ∨ (True ∧ ((p5 ∧ (p5 ∧ (False ∧ p2))) → p4))) := by
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Conjunctions on the right can always be decomposed.
    apply And.intro
    -- True on the right can always be proven directly.
    apply True.intro
    -- Implications on the right can always be decomposed.
    intro h3
    -- Conjunctions on the left can always be decomposed.
    let h4 := h3.left
    let h5 := h3.right
    -- Conjunctions on the left can always be decomposed.
    let h6 := h5.left
    let h7 := h5.right
    -- Conjunctions on the left can always be decomposed.
    let h8 := h7.left
    let h9 := h7.right
    -- False on the left can always be used.
    apply False.elim h8
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h10 := h1 h2
  -- One of the premise coincides with the conclusion.
  exact h10



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_342866873584775125806949774860 : (p2 → (((p4 ∨ True) → (p1 ∨ (True ∧ False))) ∨ ((((p1 → p2) ∨ (((True → True) → p2) ∧ p2)) → p1) → ((p2 ∨ p3) → (p1 ∧ p2))))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h2
  -- Implications on the right can always be decomposed.
  intro h3
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Disjunctions on the left can always be decomposed.
  cases h3
  case inl h4 =>
    -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
    have h5 : ((p1 → p2) ∨ (((True → True) → p2) ∧ p2)) := by
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- Implications on the right can always be decomposed.
      intro h6
      -- One of the premise coincides with the conclusion.
      exact h4
    -- We have shown the premise of h2, we can now drive its conclusion.
    let h7 := h2 h5
    -- One of the premise coincides with the conclusion.
    exact h7
  case inr h8 =>
    -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
    have h9 : ((p1 → p2) ∨ (((True → True) → p2) ∧ p2)) := by
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- Implications on the right can always be decomposed.
      intro h10
      -- One of the premise coincides with the conclusion.
      exact h1
    -- We have shown the premise of h2, we can now drive its conclusion.
    let h11 := h2 h9
    -- One of the premise coincides with the conclusion.
    exact h11
  -- Disjunctions on the left can always be decomposed.
  cases h3
  case inl h12 =>
    -- One of the premise coincides with the conclusion.
    exact h12
  case inr h13 =>
    -- One of the premise coincides with the conclusion.
    exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_14830481085817419362266871490 : ((((((p4 → True) ∧ (p2 → ((False ∧ (p1 → p4)) ∧ p2))) → p1) ∨ (((True ∨ ((p4 ∧ False) → p4)) ∨ p3) ∨ p3)) ∨ (p4 ∧ p2)) ∧ True) := by
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
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_160712752508304940778804580898 : (((((p2 ∨ p3) ∧ p1) → ((p1 → True) ∨ p4)) ∨ (p3 → ((p2 ∨ p3) ∨ (p4 ∧ (p4 ∧ p1))))) → (((True → p1) ∨ (False ∨ p3)) ∨ True)) := by
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
theorem thm_5_vars_641896476770133670164074252768 : (((((p2 → p1) → ((p5 ∨ p3) ∧ (False → (((True → False) → (p2 → (((((p3 ∧ True) ∨ p1) → p4) ∨ p3) ∨ p2))) ∨ p5)))) → False) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_259022779371958780981812159115 : ((True → p4) → ((p3 ∨ ((((p5 ∨ p5) → p1) ∧ ((p1 ∨ (False ∨ False)) ∨ p2)) ∧ (p5 → ((p2 ∨ False) ∨ p2)))) ∨ ((p1 ∨ p2) ∨ True))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_48955618008896834434591375403 : ((((True → ((p5 ∨ (p4 ∧ (True ∧ (True ∨ (True ∧ p2))))) ∨ (p1 ∧ (False → (p5 → (p1 ∨ False)))))) ∧ p3) ∨ ((p2 ∨ p1) → False)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_113106458787441648440583755954 : (((True → (True ∧ ((True → ((((True ∨ (p4 ∨ (p2 ∨ (p2 → p2)))) ∧ p2) ∨ p4) → p2)) ∨ ((p5 ∧ p4) ∨ p2)))) → p4) ∨ (True ∨ p2)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_199046147813495958558649905291 : (((((False ∨ False) ∨ (True → p1)) ∨ p5) ∧ True) → ((p2 ∨ (p2 → (p4 → p4))) → (((((p5 → False) ∨ p2) ∨ True) → False) → (p4 ∨ p4)))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Implications on the right can always be decomposed.
  intro h3
  -- Disjunctions on the left can always be decomposed.
  cases h2
  case inl h4 =>
    -- Conjunctions on the left can always be decomposed.
    let h5 := h1.left
    let h6 := h1.right
    -- Disjunctions on the left can always be decomposed.
    cases h5
    case inl h7 =>
      -- Disjunctions on the left can always be decomposed.
      cases h7
      case inl h8 =>
        -- Disjunctions on the left can always be decomposed.
        cases h8
        case inl h9 =>
          -- False on the left can always be used.
          apply False.elim h9
        case inr h10 =>
          -- False on the left can always be used.
          apply False.elim h10
      case inr h11 =>
        -- We want to use the implication h3 based on <expert-advice>. So we show its premise.
        have h12 : (((p5 → False) ∨ p2) ∨ True) := by
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- True on the right can always be proven directly.
          apply True.intro
        -- We have shown the premise of h3, we can now drive its conclusion.
        let h13 := h3 h12
        -- False on the left can always be used.
        apply False.elim h13
    case inr h14 =>
      -- We want to use the implication h3 based on <expert-advice>. So we show its premise.
      have h15 : (((p5 → False) ∨ p2) ∨ True) := by
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- True on the right can always be proven directly.
        apply True.intro
      -- We have shown the premise of h3, we can now drive its conclusion.
      let h16 := h3 h15
      -- False on the left can always be used.
      apply False.elim h16
  case inr h17 =>
    -- Conjunctions on the left can always be decomposed.
    let h18 := h1.left
    let h19 := h1.right
    -- Disjunctions on the left can always be decomposed.
    cases h18
    case inl h20 =>
      -- Disjunctions on the left can always be decomposed.
      cases h20
      case inl h21 =>
        -- Disjunctions on the left can always be decomposed.
        cases h21
        case inl h22 =>
          -- False on the left can always be used.
          apply False.elim h22
        case inr h23 =>
          -- False on the left can always be used.
          apply False.elim h23
      case inr h24 =>
        -- We want to use the implication h3 based on <expert-advice>. So we show its premise.
        have h25 : (((p5 → False) ∨ p2) ∨ True) := by
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- True on the right can always be proven directly.
          apply True.intro
        -- We have shown the premise of h3, we can now drive its conclusion.
        let h26 := h3 h25
        -- False on the left can always be used.
        apply False.elim h26
    case inr h27 =>
      -- We want to use the implication h3 based on <expert-advice>. So we show its premise.
      have h28 : (((p5 → False) ∨ p2) ∨ True) := by
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- True on the right can always be proven directly.
        apply True.intro
      -- We have shown the premise of h3, we can now drive its conclusion.
      let h29 := h3 h28
      -- False on the left can always be used.
      apply False.elim h29



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_139853777726468835529129373681 : (((p5 → ((p4 → ((((True ∨ ((True → p3) ∨ (p1 ∨ p3))) → (p5 → p1)) ∨ p1) ∧ (p2 → False))) → False)) → p2) → ((p5 ∧ p3) ∨ True)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_313309697595921383053267808741 : (p3 ∨ ((p1 ∨ (((p3 ∨ (p5 ∧ p1)) ∧ ((((p2 → p1) ∨ True) → ((p1 → p2) → p4)) → ((p3 ∨ p4) ∨ p1))) ∨ (p2 ∧ False))) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_87208902873961661830915243764 : (((((True ∧ (True ∨ True)) ∧ p4) ∧ p2) ∧ (((p5 ∨ ((p5 ∨ p5) ∨ p3)) ∧ (True ∧ ((p5 ∨ p2) → p5))) ∧ ((p1 ∨ p3) ∨ p3))) → p5) := by
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
  -- Conjunctions on the left can always be decomposed.
  let h8 := h6.left
  let h9 := h6.right
  -- Disjunctions on the left can always be decomposed.
  cases h9
  case inl h10 =>
    -- Conjunctions on the left can always be decomposed.
    let h11 := h3.left
    let h12 := h3.right
    -- Conjunctions on the left can always be decomposed.
    let h13 := h11.left
    let h14 := h11.right
    -- Disjunctions on the left can always be decomposed.
    cases h13
    case inl h15 =>
      -- Conjunctions on the left can always be decomposed.
      let h16 := h14.left
      let h17 := h14.right
      -- Disjunctions on the left can always be decomposed.
      cases h12
      case inl h18 =>
        -- Disjunctions on the left can always be decomposed.
        cases h18
        case inl h19 =>
          -- One of the premise coincides with the conclusion.
          exact h15
        case inr h20 =>
          -- One of the premise coincides with the conclusion.
          exact h15
      case inr h21 =>
        -- One of the premise coincides with the conclusion.
        exact h15
    case inr h22 =>
      -- Disjunctions on the left can always be decomposed.
      cases h22
      case inl h23 =>
        -- Disjunctions on the left can always be decomposed.
        cases h23
        case inl h24 =>
          -- Conjunctions on the left can always be decomposed.
          let h25 := h14.left
          let h26 := h14.right
          -- Disjunctions on the left can always be decomposed.
          cases h12
          case inl h27 =>
            -- Disjunctions on the left can always be decomposed.
            cases h27
            case inl h28 =>
              -- One of the premise coincides with the conclusion.
              exact h24
            case inr h29 =>
              -- One of the premise coincides with the conclusion.
              exact h24
          case inr h30 =>
            -- One of the premise coincides with the conclusion.
            exact h24
        case inr h31 =>
          -- Conjunctions on the left can always be decomposed.
          let h32 := h14.left
          let h33 := h14.right
          -- Disjunctions on the left can always be decomposed.
          cases h12
          case inl h34 =>
            -- Disjunctions on the left can always be decomposed.
            cases h34
            case inl h35 =>
              -- One of the premise coincides with the conclusion.
              exact h31
            case inr h36 =>
              -- One of the premise coincides with the conclusion.
              exact h31
          case inr h37 =>
            -- One of the premise coincides with the conclusion.
            exact h31
      case inr h38 =>
        -- Conjunctions on the left can always be decomposed.
        let h39 := h14.left
        let h40 := h14.right
        -- Disjunctions on the left can always be decomposed.
        cases h12
        case inl h41 =>
          -- Disjunctions on the left can always be decomposed.
          cases h41
          case inl h42 =>
            -- We want to use the implication h40 based on <expert-advice>. So we show its premise.
            have h43 : (p5 ∨ p2) := by
              -- Show the right disjunct based on <expert-advice>.
              apply Or.inr
              -- One of the premise coincides with the conclusion.
              exact h5
            -- We have shown the premise of h40, we can now drive its conclusion.
            let h44 := h40 h43
            -- One of the premise coincides with the conclusion.
            exact h44
          case inr h45 =>
            -- We want to use the implication h40 based on <expert-advice>. So we show its premise.
            have h46 : (p5 ∨ p2) := by
              -- Show the right disjunct based on <expert-advice>.
              apply Or.inr
              -- One of the premise coincides with the conclusion.
              exact h5
            -- We have shown the premise of h40, we can now drive its conclusion.
            let h47 := h40 h46
            -- One of the premise coincides with the conclusion.
            exact h47
        case inr h48 =>
          -- We want to use the implication h40 based on <expert-advice>. So we show its premise.
          have h49 : (p5 ∨ p2) := by
            -- Show the right disjunct based on <expert-advice>.
            apply Or.inr
            -- One of the premise coincides with the conclusion.
            exact h5
          -- We have shown the premise of h40, we can now drive its conclusion.
          let h50 := h40 h49
          -- One of the premise coincides with the conclusion.
          exact h50
  case inr h51 =>
    -- Conjunctions on the left can always be decomposed.
    let h52 := h3.left
    let h53 := h3.right
    -- Conjunctions on the left can always be decomposed.
    let h54 := h52.left
    let h55 := h52.right
    -- Disjunctions on the left can always be decomposed.
    cases h54
    case inl h56 =>
      -- Conjunctions on the left can always be decomposed.
      let h57 := h55.left
      let h58 := h55.right
      -- Disjunctions on the left can always be decomposed.
      cases h53
      case inl h59 =>
        -- Disjunctions on the left can always be decomposed.
        cases h59
        case inl h60 =>
          -- One of the premise coincides with the conclusion.
          exact h56
        case inr h61 =>
          -- One of the premise coincides with the conclusion.
          exact h56
      case inr h62 =>
        -- One of the premise coincides with the conclusion.
        exact h56
    case inr h63 =>
      -- Disjunctions on the left can always be decomposed.
      cases h63
      case inl h64 =>
        -- Disjunctions on the left can always be decomposed.
        cases h64
        case inl h65 =>
          -- Conjunctions on the left can always be decomposed.
          let h66 := h55.left
          let h67 := h55.right
          -- Disjunctions on the left can always be decomposed.
          cases h53
          case inl h68 =>
            -- Disjunctions on the left can always be decomposed.
            cases h68
            case inl h69 =>
              -- One of the premise coincides with the conclusion.
              exact h65
            case inr h70 =>
              -- One of the premise coincides with the conclusion.
              exact h65
          case inr h71 =>
            -- One of the premise coincides with the conclusion.
            exact h65
        case inr h72 =>
          -- Conjunctions on the left can always be decomposed.
          let h73 := h55.left
          let h74 := h55.right
          -- Disjunctions on the left can always be decomposed.
          cases h53
          case inl h75 =>
            -- Disjunctions on the left can always be decomposed.
            cases h75
            case inl h76 =>
              -- One of the premise coincides with the conclusion.
              exact h72
            case inr h77 =>
              -- One of the premise coincides with the conclusion.
              exact h72
          case inr h78 =>
            -- One of the premise coincides with the conclusion.
            exact h72
      case inr h79 =>
        -- Conjunctions on the left can always be decomposed.
        let h80 := h55.left
        let h81 := h55.right
        -- Disjunctions on the left can always be decomposed.
        cases h53
        case inl h82 =>
          -- Disjunctions on the left can always be decomposed.
          cases h82
          case inl h83 =>
            -- We want to use the implication h81 based on <expert-advice>. So we show its premise.
            have h84 : (p5 ∨ p2) := by
              -- Show the right disjunct based on <expert-advice>.
              apply Or.inr
              -- One of the premise coincides with the conclusion.
              exact h5
            -- We have shown the premise of h81, we can now drive its conclusion.
            let h85 := h81 h84
            -- One of the premise coincides with the conclusion.
            exact h85
          case inr h86 =>
            -- We want to use the implication h81 based on <expert-advice>. So we show its premise.
            have h87 : (p5 ∨ p2) := by
              -- Show the right disjunct based on <expert-advice>.
              apply Or.inr
              -- One of the premise coincides with the conclusion.
              exact h5
            -- We have shown the premise of h81, we can now drive its conclusion.
            let h88 := h81 h87
            -- One of the premise coincides with the conclusion.
            exact h88
        case inr h89 =>
          -- We want to use the implication h81 based on <expert-advice>. So we show its premise.
          have h90 : (p5 ∨ p2) := by
            -- Show the right disjunct based on <expert-advice>.
            apply Or.inr
            -- One of the premise coincides with the conclusion.
            exact h5
          -- We have shown the premise of h81, we can now drive its conclusion.
          let h91 := h81 h90
          -- One of the premise coincides with the conclusion.
          exact h91



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_613611241448624412080230286948 : (((((((((True ∧ p5) ∧ (p4 ∧ (((p3 ∧ True) ∧ p4) ∨ p4))) ∧ p2) ∧ (p1 → False)) ∧ (True ∨ True)) ∧ ((p3 → p5) ∨ p5)) ∨ False) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_707417177810470686483828386021 : (((((p3 → ((p3 ∨ p4) → p2)) → (p2 ∧ False)) ∨ ((p4 → (p5 ∧ (((p2 ∨ (p3 → False)) → True) → (p2 ∨ p5)))) ∨ (True ∨ p1))) ∨ False) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
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
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_255635212211133432975823039640 : ((p5 ∧ p4) → (((p4 ∨ True) ∧ True) ∧ (((((p3 ∨ ((p1 → ((p1 ∨ (p5 ∨ p3)) ∧ p3)) → p3)) ∧ p4) → p1) → p1) ∨ (True ∨ True)))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- One of the premise coincides with the conclusion.
  exact h3
  -- True on the right can always be proven directly.
  apply True.intro
  -- Conjunctions on the left can always be decomposed.
  let h4 := h1.left
  let h5 := h1.right
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_227477846897913167097121684699 : ((True ∧ (p3 ∧ p5)) ∨ (((((p4 ∨ False) ∧ (((((False → p1) ∨ p5) ∧ p2) ∨ ((p4 ∧ (p5 ∨ p1)) ∨ p1)) ∨ True)) ∨ p3) ∨ p2) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_204439400994932984957720519253 : (((((p2 ∨ False) ∨ p1) ∧ p2) ∨ p1) ∨ (p2 → ((((p4 ∧ ((p5 ∧ p2) → p3)) → p2) → p2) → (p2 ∧ (True → ((p3 → p1) → True)))))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- One of the premise coincides with the conclusion.
  exact h1
  -- Implications on the right can always be decomposed.
  intro h3
  -- Implications on the right can always be decomposed.
  intro h4
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_341110918746612071951629198686 : (p2 → ((p5 → (((((p1 ∨ p3) ∨ p4) ∧ False) ∨ (p5 → p5)) ∧ ((p1 ∨ p1) ∨ ((p1 ∧ ((p1 ∨ p5) ∧ (True ∧ p4))) ∨ p5)))) ∨ p5)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h2
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h3
  -- One of the premise coincides with the conclusion.
  exact h3
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_173112453402115256316625107926 : ((p2 ∨ (((p3 ∨ p4) ∨ ((False → ((p1 ∨ p1) ∧ (False → False))) → p4)) → p1)) ∨ ((((p4 → (p5 ∧ p5)) → p4) ∨ (True → True)) ∨ p1)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_47373576195328306301736145748 : ((((True ∧ p1) → (p5 → (p1 ∧ (p3 ∨ ((True ∧ (p2 ∧ (((p3 ∨ p3) ∨ (p4 ∨ (False ∧ False))) ∧ p5))) ∨ p4))))) ∨ (p2 → True)) ∨ p1) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_233102103774887236309910619937 : ((p4 ∧ (p3 → True)) → (((((p1 ∨ False) ∧ (p4 → p5)) → p3) ∧ False) ∨ ((p2 → (p4 → ((p4 ∨ p3) ∧ (True → p3)))) ∨ (p4 ∨ p2)))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- One of the premise coincides with the conclusion.
  exact h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_180542323326860453562104183451 : ((((p3 → p1) → ((p4 ∧ (False → p5)) → p1)) ∨ ((p3 → p3) → False)) → ((((True ∨ (True ∨ p1)) → ((p1 ∧ p2) ∨ True)) ∨ p5) ∨ p5)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h2 =>
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Implications on the right can always be decomposed.
    intro h3
    -- Disjunctions on the left can always be decomposed.
    cases h3
    case inl h4 =>
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
        -- True on the right can always be proven directly.
        apply True.intro
      case inr h7 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- True on the right can always be proven directly.
        apply True.intro
  case inr h8 =>
    -- We want to use the implication h8 based on <expert-advice>. So we show its premise.
    have h9 : (p3 → p3) := by
      -- Implications on the right can always be decomposed.
      intro h10
      -- One of the premise coincides with the conclusion.
      exact h10
    -- We have shown the premise of h8, we can now drive its conclusion.
    let h11 := h8 h9
    -- False on the left can always be used.
    apply False.elim h11



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_345064199777708208971602331347 : (p3 → (((p3 ∧ ((p4 ∧ (p2 → ((p2 → ((False → p2) ∨ False)) ∧ False))) → ((False ∧ p2) ∧ p3))) ∨ ((False → True) ∨ (p1 → p3))) ∧ p3)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h2
  -- True on the right can always be proven directly.
  apply True.intro
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_66069424956012558978726138782 : ((p5 ∨ ((((p5 ∧ False) → p3) ∧ ((False ∨ (p1 → (((((True ∨ p4) ∨ False) → p5) ∨ (p1 ∨ True)) ∧ (p5 ∧ p5)))) ∨ False)) ∨ True)) ∨ p2) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_342016785228255240954430365671 : (p2 → ((p3 ∨ ((((True → p5) ∨ (p3 ∧ p4)) ∧ (p1 ∧ (p2 → p5))) ∨ (((p4 ∨ (p3 ∧ p5)) ∧ p3) ∧ p5))) ∨ ((True ∧ p2) ∨ p3))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_177863226166146072636972155335 : (((((True ∧ p3) ∨ (p5 ∨ (p5 ∨ ((p5 → p3) ∨ p4)))) ∨ p4) ∨ p2) ∨ ((p2 ∨ p3) → (True ∧ (((True → False) → (p1 ∧ True)) ∨ p3)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h2 =>
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Implications on the right can always be decomposed.
    intro h3
    -- Conjunctions on the right can always be decomposed.
    apply And.intro
    -- We want to use the implication h3 based on <expert-advice>. So we show its premise.
    have h4 : True := by
      -- True on the right can always be proven directly.
      apply True.intro
    -- We have shown the premise of h3, we can now drive its conclusion.
    let h5 := h3 h4
    -- False on the left can always be used.
    apply False.elim h5
    -- True on the right can always be proven directly.
    apply True.intro
  case inr h6 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h6



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_149417475729246517820028055919 : ((True ∧ ((False → ((True → False) → p3)) ∧ ((((p2 → ((p3 ∨ p5) ∧ True)) ∧ (p1 ∧ p4)) ∨ p3) → p5))) ∨ ((p1 ∧ p4) → (p3 → p3))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Conjunctions on the left can always be decomposed.
  let h3 := h1.left
  let h4 := h1.right
  -- One of the premise coincides with the conclusion.
  exact h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_135917980369015493873215708192 : ((((True ∧ p2) → ((((p2 → (False → p4)) ∧ p1) → p3) ∧ p2)) → ((p3 ∧ ((p1 → p1) ∧ (p1 ∨ p2))) ∨ p1)) ∨ ((True → p3) → True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_159038033908599137081378729465 : ((p4 ∨ (p2 → (p4 ∨ (p5 ∧ ((False ∧ p4) ∨ (p2 ∨ (((True ∨ False) → p4) ∨ (p1 ∨ p5)))))))) ∨ (True ∨ ((p5 ∧ (p5 ∨ p5)) ∧ p2))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_249860399046166110400556560069 : ((True → False) ∨ (((p3 ∧ p4) ∨ ((True → ((p1 ∨ p2) ∧ True)) ∧ True)) ∨ (((p5 ∧ False) → p1) ∧ (p1 ∨ ((p2 ∨ (p5 → p3)) → True))))) := by
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
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h4
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_172070165661019905024205554709 : ((((((False ∨ (p4 ∨ p1)) → (p1 → p3)) ∨ p4) ∨ (p5 ∧ p4)) → (p3 → p1)) ∨ ((p1 → (True ∨ p1)) ∧ (True ∨ (p1 → (p1 ∨ p5))))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_345369902647018622487703784993 : (p3 → ((((((p5 ∧ False) ∨ ((((p3 ∧ p1) → p4) → True) → p1)) ∨ p3) → ((p3 → False) ∧ ((p5 ∨ (True ∧ p2)) ∧ p3))) ∨ p5) ∨ True)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_180121084561682878386603294974 : ((((p4 ∨ (((((False → p5) ∨ False) ∨ p2) → True) ∨ p5)) ∨ p4) → True) → ((p1 ∧ (p3 ∧ p2)) → ((p4 → p2) → ((p3 → False) → p5)))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Implications on the right can always be decomposed.
  intro h3
  -- Implications on the right can always be decomposed.
  intro h4
  -- Conjunctions on the left can always be decomposed.
  let h5 := h2.left
  let h6 := h2.right
  -- Conjunctions on the left can always be decomposed.
  let h7 := h6.left
  let h8 := h6.right
  -- We want to use the implication h4 based on <expert-advice>. So we show its premise.
  have h9 : p3 := by
    -- One of the premise coincides with the conclusion.
    exact h7
  -- We have shown the premise of h4, we can now drive its conclusion.
  let h10 := h4 h9
  -- False on the left can always be used.
  apply False.elim h10



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_157110663721818586405239665194 : (((p4 → (p3 ∨ ((False ∨ p2) ∨ (p2 ∨ (p1 ∨ ((p4 → ((True ∨ p2) → True)) → True)))))) ∨ False) ∨ (p3 ∧ ((True ∧ False) ∨ (p5 ∧ p2)))) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
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
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h2
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_672816472811205055447674088291 : (((((((((True ∧ p4) ∧ p4) ∧ p1) ∧ p1) ∧ ((False ∨ (p5 ∧ p4)) → (False ∨ p1))) ∧ ((False → p5) ∨ p2)) → (p3 → (p5 ∧ p5))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_345408102151390780852908213688 : (p3 → (((((p1 → p1) ∨ ((False → (p3 → (((p5 ∨ p1) ∨ p3) ∨ p4))) ∨ True)) ∨ ((p1 → (p3 ∨ (True ∧ p4))) ∧ p2)) → p2) ∨ p3)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_85167498257736820069339111717 : (((((p5 → p4) ∨ (p1 → (True ∨ p4))) ∧ (True ∨ (p4 ∧ (True ∧ p1)))) → ((p2 → ((p3 ∨ p1) ∨ (p1 → p2))) ∧ (False ∧ p4))) → p2) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h2 : (((p5 → p4) ∨ (p1 → (True ∨ p4))) ∧ (True ∨ (p4 ∧ (True ∧ p1)))) := by
    -- Conjunctions on the right can always be decomposed.
    apply And.intro
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h3
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- True on the right can always be proven directly.
    apply True.intro
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h4 := h1 h2
  -- We need to get the right conjuct of h4 based on <expert-advice>.
  let h5 := h4.right
  -- We need to get the left conjuct of h5 based on <expert-advice>.
  let h6 := h5.left
  -- False on the left can always be used.
  apply False.elim h6



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_64198499060532855008781357959 : ((False ∨ (False ∧ (p4 ∨ (True ∧ (((True → p4) → (p5 ∨ (((p4 ∨ p1) → ((p3 ∧ False) ∨ p4)) ∧ True))) ∨ ((p4 ∨ p2) → False)))))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_318259774881287729097478165774 : (p4 ∨ (((p5 → (False ∧ p4)) ∧ ((p5 ∨ ((((False ∨ p3) → ((True → False) ∧ p4)) ∧ True) → True)) → (((True ∧ True) ∧ p1) ∧ False))) → p2)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- We want to use the implication h3 based on <expert-advice>. So we show its premise.
  have h4 : (p5 ∨ ((((False ∨ p3) → ((True → False) ∧ p4)) ∧ True) → True)) := by
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h5
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h3, we can now drive its conclusion.
  let h6 := h3 h4
  -- We need to get the right conjuct of h6 based on <expert-advice>.
  let h7 := h6.right
  -- False on the left can always be used.
  apply False.elim h7



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_59490814069172184896140225569 : (((p1 → p5) ∨ ((p1 → ((p5 ∧ True) ∨ (((p3 ∧ ((p4 → p1) → p5)) ∧ p4) ∧ ((p5 ∧ False) ∧ (p3 ∨ (p3 ∧ p3)))))) ∧ True)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_326240827964235436904297834301 : (p5 ∨ (p3 → ((((((p1 ∨ p2) ∨ True) ∧ ((True ∨ p5) → (p3 → p4))) → p5) → p2) → (p4 → (p4 → (p3 → ((p2 → p4) ∨ False))))))) := by
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
  -- Implications on the right can always be decomposed.
  intro h5
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h6
  -- One of the premise coincides with the conclusion.
  exact h3



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_329715656459927050397978340045 : (True → ((p1 → p1) → (((((((((False → p1) → p5) ∨ p3) ∨ p2) → ((p4 → (p2 → p3)) → p5)) → (p4 ∨ True)) → p3) ∧ p2) → p3))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Implications on the right can always be decomposed.
  intro h3
  -- Conjunctions on the left can always be decomposed.
  let h4 := h3.left
  let h5 := h3.right
  -- We want to use the implication h4 based on <expert-advice>. So we show its premise.
  have h6 : ((((((False → p1) → p5) ∨ p3) ∨ p2) → ((p4 → (p2 → p3)) → p5)) → (p4 ∨ True)) := by
    -- Implications on the right can always be decomposed.
    intro h7
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h4, we can now drive its conclusion.
  let h8 := h4 h6
  -- One of the premise coincides with the conclusion.
  exact h8



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_166147864191991394973311239457 : ((False ∧ ((((p1 ∧ p4) ∧ p5) ∧ (False ∨ (p4 ∧ (True ∧ (p3 ∧ (p4 ∧ False)))))) ∧ p4)) ∨ ((((p3 ∨ p3) ∨ True) → (p2 ∧ p3)) → p2)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h2 : ((p3 ∨ p3) ∨ True) := by
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h3 := h1 h2
  -- We need to get the left conjuct of h3 based on <expert-advice>.
  let h4 := h3.left
  -- One of the premise coincides with the conclusion.
  exact h4



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_809945159230690821775222760611 : (((p5 → (((((((p3 ∧ ((True ∨ p4) → False)) → p5) ∧ ((True → (p4 ∨ p1)) → p5)) ∨ p5) → p3) ∨ True) ∨ ((p4 ∨ p4) ∧ p3))) ∨ p2) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_53460269652821354043801008075 : ((((p1 ∨ True) ∨ ((False → p2) ∨ ((p4 ∧ (True ∧ p5)) ∨ p3))) → (p2 → ((p3 → p3) → ((p1 ∨ ((p5 → p4) → p1)) ∨ p3)))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_196674044751530302724789351367 : ((((p2 → (p2 ∧ (p5 ∨ True))) ∧ False) ∧ False) ∨ (p5 → ((((p2 ∧ (((True ∨ p1) ∧ p4) ∨ True)) ∧ p5) ∧ p1) ∨ (False → (True ∧ p1))))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h2
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- False on the left can always be used.
  apply False.elim h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_166698450695217070775104408408 : ((p3 → ((((p4 → p1) → (p3 → ((True ∨ (p5 ∨ p1)) → (p2 → p4)))) ∨ True) ∧ True)) ∨ ((p5 → ((p3 ∧ (p1 ∧ p1)) ∨ False)) → False)) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_180882577697943918452891508112 : ((((p3 → p3) ∧ False) → (((True → p1) → p5) ∧ ((False → p2) ∧ p5))) → (p2 ∨ (((False ∧ p4) ∨ (p3 → (p5 → p5))) ∨ (False → True)))) := by
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
theorem thm_5_vars_127850642473411933862043633246 : ((False → ((p4 ∧ (p5 ∨ (((True → (p3 ∧ False)) → p2) ∨ ((False ∧ ((p4 ∧ p1) ∧ p5)) ∧ ((p2 ∨ True) ∧ True))))) ∧ True)) → (p2 → p2)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- One of the premise coincides with the conclusion.
  exact h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_41363343977246053697221932309 : (((((p2 → (((p3 ∨ (False → (True → p1))) ∨ True) ∨ (p1 ∧ True))) ∨ (p2 → p5)) → ((False ∨ (p3 ∨ (p5 → p4))) ∧ p1)) ∨ p4) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_135068755569960273152709709615 : (((((p2 ∧ ((False ∧ False) → p4)) ∧ (p4 ∨ (((p5 ∨ p5) ∨ p4) ∧ (p1 ∨ p3)))) ∧ (True ∧ p3)) ∨ (p5 → p1)) ∨ ((True → False) → p5)) := by
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
theorem thm_5_vars_177562199769836457238041020579 : ((p3 → (p3 ∨ (p2 → ((((p4 ∨ True) ∨ p2) → p2) → (p2 ∨ p4))))) ∧ (((p3 ∧ p3) → p4) ∨ (False ∨ ((p2 ∨ False) ∨ (p5 ∨ True))))) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- One of the premise coincides with the conclusion.
  exact h1
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



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_112853259864636307122941927630 : ((((p3 → (p4 → p5)) ∧ (p3 ∧ ((((p3 ∨ (True ∨ p2)) ∨ p1) ∨ (True → ((p3 → p1) ∨ (p1 → p1)))) ∨ p5))) → p1) ∨ (True ∨ p5)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_202130890491006232308394709921 : ((((p4 ∨ (p4 → False)) → False) → True) ∧ (p4 ∨ ((True → (((False → ((p3 → (p2 ∨ p1)) ∨ p4)) ∧ p3) ∧ ((p3 ∨ False) → True))) → p3))) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h2
  -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
  have h3 : True := by
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h2, we can now drive its conclusion.
  let h4 := h2 h3
  -- We need to get the left conjuct of h4 based on <expert-advice>.
  let h5 := h4.left
  -- We need to get the right conjuct of h5 based on <expert-advice>.
  let h6 := h5.right
  -- One of the premise coincides with the conclusion.
  exact h6



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_185600781828071918409102026997 : ((p5 ∨ (p2 ∨ ((True → ((p3 ∨ False) ∧ p1)) ∨ (p2 ∨ p3)))) ∨ (True ∨ (((False ∨ p2) ∧ p2) ∨ (((p5 → p2) ∨ (p4 ∨ p1)) ∧ p5)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_328824453485240867289024669577 : (True → (((p2 ∧ (p5 ∧ (p1 → p5))) → (p4 → (p2 → p4))) → ((((p3 → p4) ∧ ((p3 ∧ (p4 ∨ p3)) ∧ (p3 ∧ p5))) ∨ p4) ∨ True))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_305719521601240855294574544035 : (p1 ∨ ((p2 ∨ ((((p1 → (p1 ∧ p2)) → True) ∧ p5) ∨ True)) → ((p4 ∧ p5) ∨ (p4 → (p1 → (True ∧ ((p5 → (p1 ∨ p1)) ∨ p4))))))) := by
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
    -- Implications on the right can always be decomposed.
    intro h4
    -- Conjunctions on the right can always be decomposed.
    apply And.intro
    -- True on the right can always be proven directly.
    apply True.intro
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h3
  case inr h5 =>
    -- Disjunctions on the left can always be decomposed.
    cases h5
    case inl h6 =>
      -- Conjunctions on the left can always be decomposed.
      let h7 := h6.left
      let h8 := h6.right
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Implications on the right can always be decomposed.
      intro h9
      -- Implications on the right can always be decomposed.
      intro h10
      -- Conjunctions on the right can always be decomposed.
      apply And.intro
      -- True on the right can always be proven directly.
      apply True.intro
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- One of the premise coincides with the conclusion.
      exact h9
    case inr h11 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Implications on the right can always be decomposed.
      intro h12
      -- Implications on the right can always be decomposed.
      intro h13
      -- Conjunctions on the right can always be decomposed.
      apply And.intro
      -- True on the right can always be proven directly.
      apply True.intro
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- One of the premise coincides with the conclusion.
      exact h12



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_337129365839329909770230061770 : (p1 → ((p5 ∧ ((False ∨ p1) → ((p4 ∨ True) ∧ ((p3 → p5) → ((((((p2 ∨ False) → False) ∧ True) ∨ p3) → False) ∨ p2))))) ∨ (p2 ∨ True))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_656911000938318842020105355541 : ((((((p2 → False) ∧ (p1 → False)) ∨ (p2 ∧ ((False ∨ False) ∨ (p3 ∨ ((False → ((False → True) ∨ (p5 → p2))) ∨ True))))) ∨ (True ∨ p2)) ∨ False) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_55534913435337698303604564146 : ((((p2 → p3) → ((p4 ∧ p1) ∨ True)) → (p4 ∨ (p3 → (False ∨ ((p5 ∧ (True → (((p4 ∧ (p3 ∨ p4)) ∧ p1) ∧ p4))) ∧ p4))))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_325821538280035032598513665999 : (p5 ∨ (p3 ∨ ((p4 → (((p1 ∨ False) ∧ p3) → False)) → (p2 ∨ (((p2 ∨ (True ∨ True)) ∧ ((p4 ∨ p4) → (False ∧ p1))) → (p4 → False)))))) := by
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
  -- Conjunctions on the left can always be decomposed.
  let h4 := h2.left
  let h5 := h2.right
  -- Disjunctions on the left can always be decomposed.
  cases h4
  case inl h6 =>
    -- We want to use the implication h5 based on <expert-advice>. So we show its premise.
    have h7 : (p4 ∨ p4) := by
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- One of the premise coincides with the conclusion.
      exact h3
    -- We have shown the premise of h5, we can now drive its conclusion.
    let h8 := h5 h7
    -- We need to get the left conjuct of h8 based on <expert-advice>.
    let h9 := h8.left
    -- False on the left can always be used.
    apply False.elim h9
  case inr h10 =>
    -- Disjunctions on the left can always be decomposed.
    cases h10
    case inl h11 =>
      -- We want to use the implication h5 based on <expert-advice>. So we show its premise.
      have h12 : (p4 ∨ p4) := by
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- One of the premise coincides with the conclusion.
        exact h3
      -- We have shown the premise of h5, we can now drive its conclusion.
      let h13 := h5 h12
      -- We need to get the left conjuct of h13 based on <expert-advice>.
      let h14 := h13.left
      -- False on the left can always be used.
      apply False.elim h14
    case inr h15 =>
      -- We want to use the implication h5 based on <expert-advice>. So we show its premise.
      have h16 : (p4 ∨ p4) := by
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- One of the premise coincides with the conclusion.
        exact h3
      -- We have shown the premise of h5, we can now drive its conclusion.
      let h17 := h5 h16
      -- We need to get the left conjuct of h17 based on <expert-advice>.
      let h18 := h17.left
      -- False on the left can always be used.
      apply False.elim h18



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_624266623929543849059422789333 : ((((p3 ∨ ((p3 → (p5 → ((p4 → ((False ∨ (p1 ∧ (p2 ∨ (p1 ∨ p3)))) ∧ (((p4 → False) ∧ p3) → True))) ∨ p4))) → p2)) ∨ True) ∨ p3) ∧ True) := by
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
theorem thm_5_vars_54079511327789316585775508423 : ((((p5 ∨ p2) ∧ (p1 ∧ (True ∨ (True → (p2 → p3))))) → (p5 ∨ (True → ((((True ∧ p3) → (p5 ∧ p5)) → False) ∨ (p2 ∨ False))))) ∨ p4) := by
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
    -- Disjunctions on the left can always be decomposed.
    cases h6
    case inl h7 =>
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- One of the premise coincides with the conclusion.
      exact h4
    case inr h8 =>
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- One of the premise coincides with the conclusion.
      exact h4
  case inr h9 =>
    -- Conjunctions on the left can always be decomposed.
    let h10 := h3.left
    let h11 := h3.right
    -- Disjunctions on the left can always be decomposed.
    cases h11
    case inl h12 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Implications on the right can always be decomposed.
      intro h13
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- One of the premise coincides with the conclusion.
      exact h9
    case inr h14 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Implications on the right can always be decomposed.
      intro h15
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- One of the premise coincides with the conclusion.
      exact h9



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_171516379874327389182728153600 : (((((p5 ∧ p2) → (((False ∨ p5) ∧ ((p1 ∨ True) → p1)) → p4)) ∧ p1) ∨ p5) ∨ (False ∨ (p4 → (((True → p2) → p2) ∨ (p5 → p4))))) := by
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
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_173882337946873355178818441510 : (((((((p5 ∧ (p1 ∧ p1)) ∨ p1) ∨ (False → p1)) ∧ (p4 ∧ p2)) ∨ True) → p5) → (((p2 ∧ p4) ∧ (p5 ∨ p3)) → ((p2 → False) → p3))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Implications on the right can always be decomposed.
  intro h3
  -- Conjunctions on the left can always be decomposed.
  let h4 := h2.left
  let h5 := h2.right
  -- Conjunctions on the left can always be decomposed.
  let h6 := h4.left
  let h7 := h4.right
  -- Disjunctions on the left can always be decomposed.
  cases h5
  case inl h8 =>
    -- We want to use the implication h3 based on <expert-advice>. So we show its premise.
    have h9 : p2 := by
      -- One of the premise coincides with the conclusion.
      exact h6
    -- We have shown the premise of h3, we can now drive its conclusion.
    let h10 := h3 h9
    -- False on the left can always be used.
    apply False.elim h10
  case inr h11 =>
    -- One of the premise coincides with the conclusion.
    exact h11



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_76501745834275675365420254471 : ((((p2 → ((p1 ∧ ((((((p2 ∨ p3) → p5) ∧ p1) ∨ (p1 ∧ (p1 ∨ False))) ∧ p3) ∧ False)) ∨ p1)) ∨ (True ∨ (p5 ∧ p5))) → False) → p2) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h2 : ((p2 → ((p1 ∧ ((((((p2 ∨ p3) → p5) ∧ p1) ∨ (p1 ∧ (p1 ∨ False))) ∧ p3) ∧ False)) ∨ p1)) ∨ (True ∨ (p5 ∧ p5))) := by
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h3 := h1 h2
  -- False on the left can always be used.
  apply False.elim h3



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_687332796165543283536065098590 : (((((p1 ∧ (p4 ∧ ((p2 ∧ p2) ∧ (((p2 → p1) ∧ (p5 ∧ False)) ∧ False)))) ∧ p5) ∧ (((((p5 ∧ True) → p4) ∨ p2) ∨ p2) → p5)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_328807591096897010100295122330 : (True → ((p1 → (((p5 → True) → (p4 ∨ p5)) ∧ (False ∨ p1))) ∨ ((((((p1 → p5) ∨ p4) ∨ p2) ∨ ((False ∧ p2) ∧ p5)) → True) ∨ p3))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h2
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_53815831177375326830147800922 : ((((p2 ∧ ((p3 → p4) → (p2 → p4))) ∧ (p2 → p2)) ∨ ((p3 ∨ ((p5 ∨ p1) ∨ True)) ∨ ((p3 ∧ (p3 ∧ p4)) ∨ (p2 ∧ p1)))) ∨ p1) := by
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
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_689302335425189353397447631385 : ((((((p5 ∨ (p4 ∨ p4)) ∨ ((((p1 ∧ p4) → p4) ∧ False) ∧ p5)) ∧ (p1 ∨ True)) ∨ (((p5 ∧ p4) → False) ∨ (p2 → (True ∧ p5)))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_327221219700983376268903380810 : (True → ((p1 → (p2 ∨ (((True → (p4 → False)) → (p2 ∧ ((p2 ∨ (False ∧ p1)) → (p1 ∨ p2)))) ∧ (((False ∧ p1) → p5) → p4)))) ∨ True)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_2838001125928357553407068835 : ((True ∧ ((False ∨ p4) ∧ p1)) → ((p3 → ((p4 ∨ p2) → ((((p2 ∨ (True ∨ p4)) ∧ (p5 → (p4 → p4))) → False) ∧ p2))) ∨ p1)) := by
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
    apply False.elim h6
  case inr h7 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h5



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_111872421142012080040746665566 : ((((p1 ∧ (p3 ∨ ((p1 → p2) ∧ (((True ∨ (p4 ∨ p2)) ∧ False) ∧ (p3 ∧ True))))) ∨ (((True ∨ True) → False) ∨ p4)) ∨ True) ∨ (p1 → p1)) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_351239613889816299960289497312 : (p4 → ((((((p2 ∧ (True ∧ p5)) → p3) ∨ p1) → p2) → (p5 ∨ (((True → p5) ∨ ((p3 ∨ p3) ∧ True)) → p3))) ∨ ((True → False) → p1))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h2
  -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
  have h3 : True := by
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h2, we can now drive its conclusion.
  let h4 := h2 h3
  -- False on the left can always be used.
  apply False.elim h4



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_338043592384469018003192185561 : (p1 → (((p2 ∨ p1) ∧ (p5 ∧ ((p2 → False) ∨ (p2 ∧ p5)))) ∨ (p1 ∨ ((False ∨ ((True ∨ p5) ∧ p4)) ∧ (((p2 → False) ∨ p2) → p2))))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_731430981658149373976140653405 : ((((True → (False ∧ p3)) → (p4 ∧ ((p1 ∧ p2) ∨ (((True ∧ p3) ∧ ((p1 → p1) ∧ (p4 ∧ (p5 ∨ (p2 ∨ False))))) → (p1 ∧ p2))))) ∨ p2) ∧ True) := by
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
  -- We need to get the left conjuct of h3 based on <expert-advice>.
  let h4 := h3.left
  -- False on the left can always be used.
  apply False.elim h4
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h5 : True := by
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h6 := h1 h5
  -- We need to get the left conjuct of h6 based on <expert-advice>.
  let h7 := h6.left
  -- False on the left can always be used.
  apply False.elim h7
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_148178609750800963766662828675 : ((((((p1 → (p1 ∨ (True ∨ (p1 ∨ (p5 ∨ p5))))) → p5) → p3) ∧ (p1 ∨ True)) ∧ ((p3 ∨ p1) ∨ p4)) ∨ ((p2 ∨ (False ∨ False)) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_314844169017566753966957095623 : (p3 ∨ ((p3 ∧ (((p3 → ((p4 → p2) ∧ p5)) → False) ∨ (p1 → p3))) ∨ (((p5 ∨ True) ∧ True) ∨ ((p2 ∨ ((False ∨ True) → True)) → p5)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
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
theorem thm_5_vars_208542058698005372021760968294 : (((p1 ∨ p1) → ((p5 ∨ p3) ∨ False)) → ((p1 → (((p4 → p3) → (((True ∨ p1) → (p2 → False)) ∧ p4)) ∨ p1)) ∨ ((p2 ∨ True) ∧ p5))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h2
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_135235318727918874495477159532 : (((((p1 ∨ (True ∨ p3)) ∨ p5) → (False → (((False ∨ (p4 → p5)) ∧ ((False ∧ p3) ∨ p3)) ∨ False))) → (p2 ∨ p5)) ∨ (False → (p4 ∧ False))) := by
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
theorem thm_5_vars_178676970926317340303477987595 : (((p5 ∨ ((True → p5) ∨ p4)) ∧ ((p4 ∧ (True ∨ p2)) ∧ (p5 ∧ p5))) ∨ ((True ∨ (False ∧ False)) → ((((False → p4) ∨ p2) ∧ True) ∧ True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h2 =>
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Implications on the right can always be decomposed.
    intro h3
    -- False on the left can always be used.
    apply False.elim h3
  case inr h4 =>
    -- Conjunctions on the left can always be decomposed.
    let h5 := h4.left
    let h6 := h4.right
    -- False on the left can always be used.
    apply False.elim h5
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_656623548657816837905931252822 : ((((((((p1 ∨ True) ∧ p2) ∧ (p3 → True)) ∨ p4) → (((p3 ∧ p3) ∨ p4) ∨ ((p2 ∧ True) ∨ ((p3 → p1) ∨ p2)))) ∨ (True ∧ False)) ∨ False) ∧ True) := by
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
    -- Conjunctions on the left can always be decomposed.
    let h3 := h2.left
    let h4 := h2.right
    -- Conjunctions on the left can always be decomposed.
    let h5 := h3.left
    let h6 := h3.right
    -- Disjunctions on the left can always be decomposed.
    cases h5
    case inl h7 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- One of the premise coincides with the conclusion.
      exact h6
    case inr h8 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- One of the premise coincides with the conclusion.
      exact h6
  case inr h9 =>
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h9
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_780013490310902609910833418363 : (((p2 ∨ ((((p2 ∨ p2) ∧ (((p2 → p2) ∧ (p2 ∨ ((False ∧ p1) ∨ (p3 ∧ p3)))) ∨ True)) ∧ ((p2 → p3) ∨ False)) ∨ (True ∧ True))) ∨ p4) ∧ True) := by
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
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_105264299180297493129905088649 : (((((True ∨ (p5 → (False ∧ p4))) ∧ ((p5 → p2) ∨ p5)) ∧ (True ∨ ((p4 → (p1 ∧ p4)) → p5))) → (True → (p2 → p2))) ∧ (True ∨ p4)) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Implications on the right can always be decomposed.
  intro h3
  -- Conjunctions on the left can always be decomposed.
  let h4 := h1.left
  let h5 := h1.right
  -- Conjunctions on the left can always be decomposed.
  let h6 := h4.left
  let h7 := h4.right
  -- Disjunctions on the left can always be decomposed.
  cases h6
  case inl h8 =>
    -- Disjunctions on the left can always be decomposed.
    cases h7
    case inl h9 =>
      -- Disjunctions on the left can always be decomposed.
      cases h5
      case inl h10 =>
        -- One of the premise coincides with the conclusion.
        exact h3
      case inr h11 =>
        -- One of the premise coincides with the conclusion.
        exact h3
    case inr h12 =>
      -- Disjunctions on the left can always be decomposed.
      cases h5
      case inl h13 =>
        -- One of the premise coincides with the conclusion.
        exact h3
      case inr h14 =>
        -- One of the premise coincides with the conclusion.
        exact h3
  case inr h15 =>
    -- Disjunctions on the left can always be decomposed.
    cases h7
    case inl h16 =>
      -- Disjunctions on the left can always be decomposed.
      cases h5
      case inl h17 =>
        -- One of the premise coincides with the conclusion.
        exact h3
      case inr h18 =>
        -- One of the premise coincides with the conclusion.
        exact h3
    case inr h19 =>
      -- Disjunctions on the left can always be decomposed.
      cases h5
      case inl h20 =>
        -- One of the premise coincides with the conclusion.
        exact h3
      case inr h21 =>
        -- One of the premise coincides with the conclusion.
        exact h3
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_168705692842563076481101118277 : ((True ∨ ((((p3 ∧ p1) ∨ p4) → ((p4 ∨ ((p3 ∨ p2) → p4)) → p4)) ∧ (p2 → True))) → (p2 ∨ ((p1 ∧ (p4 ∨ (p1 ∨ p4))) ∨ True))) := by
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
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_44019416451510463556476816289 : ((((((p1 ∨ p2) → ((p1 ∨ False) → p5)) ∧ (((p3 ∨ p4) → (p1 ∧ p3)) ∧ ((p3 → (p5 → True)) ∧ False))) → (True ∨ False)) → p1) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_735252921636628329954111236445 : ((((p3 ∨ p5) ∧ ((p4 ∨ ((((False ∧ p1) ∨ True) → p5) → p5)) → ((((p4 ∨ (p3 ∧ ((p3 ∨ p1) ∧ p4))) → p3) ∨ p2) ∧ False))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_646447867295999901954639148849 : ((((p1 → ((p1 → (((True → (p5 ∧ (p4 ∧ ((p4 ∨ (p2 ∧ False)) → p5)))) → (p3 ∨ (True ∧ (p2 → p1)))) ∨ p1)) ∨ p5)) → p2) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_330988962032648699444612834236 : (True → (p5 → (((True ∧ False) ∧ (((p4 → p3) ∧ p2) → p3)) ∨ ((((p1 ∨ True) → p5) → True) → ((p5 ∨ (p5 ∨ True)) → (p4 ∨ True)))))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h3
  -- Implications on the right can always be decomposed.
  intro h4
  -- Disjunctions on the left can always be decomposed.
  cases h4
  case inl h5 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro
  case inr h6 =>
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



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_206366103429527124658280794669 : ((p2 ∨ (p2 ∧ (p5 ∧ (False → p2)))) ∨ ((((p4 ∨ ((True ∨ (p3 → (p3 ∧ p4))) ∧ (p3 ∨ False))) → p2) ∨ True) → ((p5 ∧ p5) ∨ True))) := by
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
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_118390818939605803525470987057 : ((p2 ∨ ((((p1 ∧ p3) ∧ p1) ∨ p2) ∧ (p2 ∨ (p1 ∧ (p1 ∧ (p5 ∨ ((((False → False) ∨ p5) ∧ True) ∧ (p5 ∨ p2)))))))) ∨ (False → p4)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_199770182850900261406485065289 : (((p2 → (False ∨ (False → (p4 ∨ p4)))) → False) → ((((False ∨ ((p1 → (p1 → True)) ∨ p4)) ∧ p5) ∨ p1) ∨ (((p4 ∧ True) → p2) ∧ True))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h2 : (p2 → (False ∨ (False → (p4 ∨ p4)))) := by
    -- Implications on the right can always be decomposed.
    intro h3
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h4
    -- False on the left can always be used.
    apply False.elim h4
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h5 := h1 h2
  -- False on the left can always be used.
  apply False.elim h5



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_783874014887094402722954625430 : (((p3 ∨ ((False ∨ (p5 ∧ p1)) ∧ ((((p4 → (p3 ∨ p1)) ∨ (p4 ∨ (True ∧ (p3 → p4)))) ∧ (((p3 ∨ p5) ∨ p4) ∧ False)) ∧ False))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_198688595398052049842604508857 : ((p4 ∨ (p1 ∧ (((p2 ∨ p4) → False) ∧ p5))) ∨ (p2 ∨ (p5 ∨ (True ∨ ((((((p3 ∨ p5) ∨ p5) → p5) ∧ p5) ∧ (p3 → p2)) ∧ p1))))) := by
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



