variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_43741377494268022146732539161 : (((((p4 ∧ True) → ((p2 ∨ p3) → (p3 ∧ ((p2 ∧ ((p1 ∨ ((p5 → p2) → (p1 ∨ (p3 ∧ p2)))) ∨ p2)) ∧ False)))) → True) → p3) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_205246191818841809334898853723 : ((((p2 ∨ p2) ∨ p1) ∨ (p3 ∧ p1)) ∨ (((p5 ∨ ((p2 ∧ (p4 → (p4 ∨ True))) → p1)) ∧ (True → (False → False))) → (p5 ∨ (True ∨ p5)))) := by
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
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- One of the premise coincides with the conclusion.
    exact h4
  case inr h5 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- True on the right can always be proven directly.
    apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_81049208134412529648297818525 : ((((p2 ∨ (p3 ∨ ((p5 → p4) ∧ (False ∨ p5)))) ∧ (False ∨ ((p2 ∧ p5) ∧ (p2 → (True → (p5 → p3)))))) ∧ ((True ∨ p4) ∧ p5)) → p3) := by
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
    cases h5
    case inl h7 =>
      -- False on the left can always be used.
      apply False.elim h7
    case inr h8 =>
      -- Conjunctions on the left can always be decomposed.
      let h9 := h8.left
      let h10 := h8.right
      -- Conjunctions on the left can always be decomposed.
      let h11 := h9.left
      let h12 := h9.right
      -- Conjunctions on the left can always be decomposed.
      let h13 := h3.left
      let h14 := h3.right
      -- Disjunctions on the left can always be decomposed.
      cases h13
      case inl h15 =>
        -- We want to use the implication h10 based on <expert-advice>. So we show its premise.
        have h16 : p2 := by
          -- One of the premise coincides with the conclusion.
          exact h11
        -- We have shown the premise of h10, we can now drive its conclusion.
        let h17 := h10 h16
        -- We want to use the implication h17 based on <expert-advice>. So we show its premise.
        have h18 : True := by
          -- True on the right can always be proven directly.
          apply True.intro
        -- We have shown the premise of h17, we can now drive its conclusion.
        let h19 := h17 h18
        -- We want to use the implication h19 based on <expert-advice>. So we show its premise.
        have h20 : p5 := by
          -- One of the premise coincides with the conclusion.
          exact h14
        -- We have shown the premise of h19, we can now drive its conclusion.
        let h21 := h19 h20
        -- One of the premise coincides with the conclusion.
        exact h21
      case inr h22 =>
        -- We want to use the implication h10 based on <expert-advice>. So we show its premise.
        have h23 : p2 := by
          -- One of the premise coincides with the conclusion.
          exact h11
        -- We have shown the premise of h10, we can now drive its conclusion.
        let h24 := h10 h23
        -- We want to use the implication h24 based on <expert-advice>. So we show its premise.
        have h25 : True := by
          -- True on the right can always be proven directly.
          apply True.intro
        -- We have shown the premise of h24, we can now drive its conclusion.
        let h26 := h24 h25
        -- We want to use the implication h26 based on <expert-advice>. So we show its premise.
        have h27 : p5 := by
          -- One of the premise coincides with the conclusion.
          exact h14
        -- We have shown the premise of h26, we can now drive its conclusion.
        let h28 := h26 h27
        -- One of the premise coincides with the conclusion.
        exact h28
  case inr h29 =>
    -- Disjunctions on the left can always be decomposed.
    cases h29
    case inl h30 =>
      -- Disjunctions on the left can always be decomposed.
      cases h5
      case inl h31 =>
        -- False on the left can always be used.
        apply False.elim h31
      case inr h32 =>
        -- Conjunctions on the left can always be decomposed.
        let h33 := h32.left
        let h34 := h32.right
        -- Conjunctions on the left can always be decomposed.
        let h35 := h33.left
        let h36 := h33.right
        -- Conjunctions on the left can always be decomposed.
        let h37 := h3.left
        let h38 := h3.right
        -- Disjunctions on the left can always be decomposed.
        cases h37
        case inl h39 =>
          -- One of the premise coincides with the conclusion.
          exact h30
        case inr h40 =>
          -- One of the premise coincides with the conclusion.
          exact h30
    case inr h41 =>
      -- Conjunctions on the left can always be decomposed.
      let h42 := h41.left
      let h43 := h41.right
      -- Disjunctions on the left can always be decomposed.
      cases h43
      case inl h44 =>
        -- False on the left can always be used.
        apply False.elim h44
      case inr h45 =>
        -- Disjunctions on the left can always be decomposed.
        cases h5
        case inl h46 =>
          -- False on the left can always be used.
          apply False.elim h46
        case inr h47 =>
          -- Conjunctions on the left can always be decomposed.
          let h48 := h47.left
          let h49 := h47.right
          -- Conjunctions on the left can always be decomposed.
          let h50 := h48.left
          let h51 := h48.right
          -- Conjunctions on the left can always be decomposed.
          let h52 := h3.left
          let h53 := h3.right
          -- Disjunctions on the left can always be decomposed.
          cases h52
          case inl h54 =>
            -- We want to use the implication h49 based on <expert-advice>. So we show its premise.
            have h55 : p2 := by
              -- One of the premise coincides with the conclusion.
              exact h50
            -- We have shown the premise of h49, we can now drive its conclusion.
            let h56 := h49 h55
            -- We want to use the implication h56 based on <expert-advice>. So we show its premise.
            have h57 : True := by
              -- True on the right can always be proven directly.
              apply True.intro
            -- We have shown the premise of h56, we can now drive its conclusion.
            let h58 := h56 h57
            -- We want to use the implication h58 based on <expert-advice>. So we show its premise.
            have h59 : p5 := by
              -- One of the premise coincides with the conclusion.
              exact h53
            -- We have shown the premise of h58, we can now drive its conclusion.
            let h60 := h58 h59
            -- One of the premise coincides with the conclusion.
            exact h60
          case inr h61 =>
            -- We want to use the implication h49 based on <expert-advice>. So we show its premise.
            have h62 : p2 := by
              -- One of the premise coincides with the conclusion.
              exact h50
            -- We have shown the premise of h49, we can now drive its conclusion.
            let h63 := h49 h62
            -- We want to use the implication h63 based on <expert-advice>. So we show its premise.
            have h64 : True := by
              -- True on the right can always be proven directly.
              apply True.intro
            -- We have shown the premise of h63, we can now drive its conclusion.
            let h65 := h63 h64
            -- We want to use the implication h65 based on <expert-advice>. So we show its premise.
            have h66 : p5 := by
              -- One of the premise coincides with the conclusion.
              exact h53
            -- We have shown the premise of h65, we can now drive its conclusion.
            let h67 := h65 h66
            -- One of the premise coincides with the conclusion.
            exact h67



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_713757800479981378369584462378 : (((((p4 → (p5 ∨ (p3 → False))) ∧ p3) → ((((p3 → p2) → p5) ∨ ((True ∧ p5) ∧ p4)) ∨ (p2 → ((p3 ∨ True) → (p5 ∨ p2))))) ∨ p3) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h4
  -- Implications on the right can always be decomposed.
  intro h5
  -- Disjunctions on the left can always be decomposed.
  cases h5
  case inl h6 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h4
  case inr h7 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h4
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_164858615717216648291357791899 : (((p1 ∨ (((True ∧ p3) ∨ False) ∨ (p2 → (((p4 → (False ∨ p3)) ∧ p2) ∧ p4)))) ∨ p1) ∨ (False ∨ (p5 ∨ ((p4 ∨ p4) → (p4 ∨ p1))))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
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
    -- One of the premise coincides with the conclusion.
    exact h2
  case inr h3 =>
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- One of the premise coincides with the conclusion.
    exact h3



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_894132860707535052891009807476 : ((((p2 ∧ (((((True ∨ (p1 ∨ True)) ∨ True) ∨ (((p1 → True) ∨ p1) → (False ∨ False))) ∨ p5) ∨ (p4 ∧ p5))) ∧ ((p2 → p1) ∨ False)) → p1) ∧ True) := by
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
    -- Disjunctions on the left can always be decomposed.
    cases h6
    case inl h7 =>
      -- Disjunctions on the left can always be decomposed.
      cases h7
      case inl h8 =>
        -- Disjunctions on the left can always be decomposed.
        cases h8
        case inl h9 =>
          -- Disjunctions on the left can always be decomposed.
          cases h9
          case inl h10 =>
            -- Disjunctions on the left can always be decomposed.
            cases h3
            case inl h11 =>
              -- We want to use the implication h11 based on <expert-advice>. So we show its premise.
              have h12 : p2 := by
                -- One of the premise coincides with the conclusion.
                exact h4
              -- We have shown the premise of h11, we can now drive its conclusion.
              let h13 := h11 h12
              -- One of the premise coincides with the conclusion.
              exact h13
            case inr h14 =>
              -- False on the left can always be used.
              apply False.elim h14
          case inr h15 =>
            -- Disjunctions on the left can always be decomposed.
            cases h15
            case inl h16 =>
              -- Disjunctions on the left can always be decomposed.
              cases h3
              case inl h17 =>
                -- One of the premise coincides with the conclusion.
                exact h16
              case inr h18 =>
                -- False on the left can always be used.
                apply False.elim h18
            case inr h19 =>
              -- Disjunctions on the left can always be decomposed.
              cases h3
              case inl h20 =>
                -- We want to use the implication h20 based on <expert-advice>. So we show its premise.
                have h21 : p2 := by
                  -- One of the premise coincides with the conclusion.
                  exact h4
                -- We have shown the premise of h20, we can now drive its conclusion.
                let h22 := h20 h21
                -- One of the premise coincides with the conclusion.
                exact h22
              case inr h23 =>
                -- False on the left can always be used.
                apply False.elim h23
        case inr h24 =>
          -- Disjunctions on the left can always be decomposed.
          cases h3
          case inl h25 =>
            -- We want to use the implication h25 based on <expert-advice>. So we show its premise.
            have h26 : p2 := by
              -- One of the premise coincides with the conclusion.
              exact h4
            -- We have shown the premise of h25, we can now drive its conclusion.
            let h27 := h25 h26
            -- One of the premise coincides with the conclusion.
            exact h27
          case inr h28 =>
            -- False on the left can always be used.
            apply False.elim h28
      case inr h29 =>
        -- Disjunctions on the left can always be decomposed.
        cases h3
        case inl h30 =>
          -- We want to use the implication h30 based on <expert-advice>. So we show its premise.
          have h31 : p2 := by
            -- One of the premise coincides with the conclusion.
            exact h4
          -- We have shown the premise of h30, we can now drive its conclusion.
          let h32 := h30 h31
          -- One of the premise coincides with the conclusion.
          exact h32
        case inr h33 =>
          -- False on the left can always be used.
          apply False.elim h33
    case inr h34 =>
      -- Disjunctions on the left can always be decomposed.
      cases h3
      case inl h35 =>
        -- We want to use the implication h35 based on <expert-advice>. So we show its premise.
        have h36 : p2 := by
          -- One of the premise coincides with the conclusion.
          exact h4
        -- We have shown the premise of h35, we can now drive its conclusion.
        let h37 := h35 h36
        -- One of the premise coincides with the conclusion.
        exact h37
      case inr h38 =>
        -- False on the left can always be used.
        apply False.elim h38
  case inr h39 =>
    -- Conjunctions on the left can always be decomposed.
    let h40 := h39.left
    let h41 := h39.right
    -- Disjunctions on the left can always be decomposed.
    cases h3
    case inl h42 =>
      -- We want to use the implication h42 based on <expert-advice>. So we show its premise.
      have h43 : p2 := by
        -- One of the premise coincides with the conclusion.
        exact h4
      -- We have shown the premise of h42, we can now drive its conclusion.
      let h44 := h42 h43
      -- One of the premise coincides with the conclusion.
      exact h44
    case inr h45 =>
      -- False on the left can always be used.
      apply False.elim h45
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_608908724176733211640115918449 : (((((((((p1 ∨ p1) ∧ p4) → (((p2 ∨ p4) → (p4 ∨ p1)) ∨ False)) → p5) ∨ (p5 ∨ (((True ∧ p4) ∨ p1) ∧ p2))) ∨ True) ∨ p1) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_318907960875160195448459921653 : (p4 ∨ ((p3 → ((p2 ∨ p5) ∨ (p3 → ((False ∨ (p4 ∨ (True ∧ ((((False ∨ True) ∨ p3) → p1) ∧ True)))) ∨ p3)))) ∨ ((p5 → p1) ∨ p1))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
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
theorem thm_5_vars_304012213088017376177609921347 : (p1 ∨ ((True ∧ ((p3 → (((((p4 → (p5 ∨ ((((p5 ∧ p2) → p4) → p2) → p4))) ∧ (p2 ∧ p2)) ∨ p2) ∧ p1) ∨ False)) ∨ True)) ∨ p2)) := by
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
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_147683239336731783639010947590 : (((((((True ∧ p1) ∨ (p5 ∧ False)) ∨ p4) ∨ (((True ∨ p3) → p4) → p2)) ∨ (True → (p5 ∧ p2))) → p3) ∨ ((p1 ∧ (p4 → True)) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_356895877662699014674142959296 : (p5 → ((((False ∨ False) → p2) → False) → (p4 ∨ (p3 ∧ ((((p3 ∨ True) ∧ (p1 ∧ p2)) → ((True → ((False ∧ p2) → p1)) ∧ True)) → p4))))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
  have h3 : ((False ∨ False) → p2) := by
    -- Implications on the right can always be decomposed.
    intro h4
    -- Disjunctions on the left can always be decomposed.
    cases h4
    case inl h5 =>
      -- False on the left can always be used.
      apply False.elim h5
    case inr h6 =>
      -- False on the left can always be used.
      apply False.elim h6
  -- We have shown the premise of h2, we can now drive its conclusion.
  let h7 := h2 h3
  -- False on the left can always be used.
  apply False.elim h7



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_670654958059856465637504199056 : (((((p2 ∨ p1) → (((True → True) ∧ ((p5 ∨ False) ∨ p4)) ∧ (((False → p2) ∧ (p3 ∧ (True → False))) → False))) ∨ ((False ∧ False) → p3)) ∨ p1) ∧ True) := by
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
  -- False on the left can always be used.
  apply False.elim h2
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_160261792051135082779667779811 : (((False ∨ ((p4 → ((True ∧ p3) ∧ False)) ∧ ((p3 ∧ ((p1 ∧ p1) ∨ p2)) ∨ False))) ∨ (p1 ∨ False)) → ((p5 ∨ ((p3 → p1) ∨ p3)) ∨ p3)) := by
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
      -- Conjunctions on the left can always be decomposed.
      let h5 := h4.left
      let h6 := h4.right
      -- Disjunctions on the left can always be decomposed.
      cases h6
      case inl h7 =>
        -- Conjunctions on the left can always be decomposed.
        let h8 := h7.left
        let h9 := h7.right
        -- Disjunctions on the left can always be decomposed.
        cases h9
        case inl h10 =>
          -- Conjunctions on the left can always be decomposed.
          let h11 := h10.left
          let h12 := h10.right
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- One of the premise coincides with the conclusion.
          exact h8
        case inr h13 =>
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- One of the premise coincides with the conclusion.
          exact h8
      case inr h14 =>
        -- False on the left can always be used.
        apply False.elim h14
  case inr h15 =>
    -- Disjunctions on the left can always be decomposed.
    cases h15
    case inl h16 =>
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- Implications on the right can always be decomposed.
      intro h17
      -- One of the premise coincides with the conclusion.
      exact h16
    case inr h18 =>
      -- False on the left can always be used.
      apply False.elim h18



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_113869877892053881716363673717 : (((p5 → (p3 → ((p4 ∨ ((p2 → p4) ∧ ((p2 ∧ p3) ∧ p5))) ∧ (((p5 ∧ p5) ∨ p1) ∧ (p5 ∧ p4))))) → (False ∧ p1)) ∨ (True ∨ p1)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_114472706347359248562950607196 : (((((p5 ∧ (p5 → False)) ∨ ((p1 ∨ (p5 → p5)) ∧ (False ∧ (p4 → (p1 → p5))))) → p5) → ((p4 → p2) ∨ (p3 ∨ p1))) ∨ (p4 → p4)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_104648017613396970599272671096 : (((True ∧ ((p2 ∧ p2) → ((((((p4 ∧ False) ∧ p3) → True) ∧ (p2 → (p1 ∨ p3))) → (True → p5)) ∨ True))) ∨ (p5 → True)) ∧ (p5 → True)) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro
  -- Implications on the right can always be decomposed.
  intro h2
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_248607815339869330776655519736 : ((p3 ∨ False) ∨ (p4 ∨ ((False ∨ ((False ∨ (p2 → p2)) ∨ (p3 ∧ (p3 ∨ ((False → (p3 → (p1 → p1))) ∧ p3))))) ∧ (p5 ∨ (p1 → True))))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
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
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h2
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_733610325462935725681435507928 : ((((p4 ∧ p5) ∧ (p5 ∧ (((((p4 ∨ ((p4 ∨ (p4 → p1)) ∧ False)) ∧ True) ∨ (((False ∧ p4) ∧ False) ∨ False)) ∨ True) ∨ (p5 ∨ p2)))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_159237383960851850381662472134 : ((p3 → ((((p3 ∨ ((p5 ∨ p5) → ((p4 ∧ p3) ∧ p5))) → (p1 ∧ p4)) ∧ True) ∧ (p3 ∧ False))) ∨ (((p2 ∨ p4) → p1) → (p1 → p1))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- One of the premise coincides with the conclusion.
  exact h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_47179723989152584545818979268 : (((((p1 ∨ (p5 ∧ (p3 → p5))) ∧ (p2 ∧ (((p3 → True) ∨ p3) ∧ p5))) → (p4 ∧ (p5 ∨ (p4 ∧ (p1 ∧ p2))))) ∨ (p4 ∨ True)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_64768311130396560749844343338 : ((p2 ∨ ((p1 → (p3 → (((p2 ∧ p3) ∧ ((p3 → (p3 → (p3 ∧ True))) ∨ (p3 → p1))) ∨ ((False ∧ (p3 ∨ p3)) ∨ p2)))) ∧ p1)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_48509989765618926759273706990 : (((((p4 ∧ ((p3 → p4) ∨ (p2 ∨ (((p1 ∨ (False → False)) → (p3 ∨ False)) ∧ p3)))) ∧ (p5 → p4)) ∨ p2) ∧ (p3 → (p2 ∧ True))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_232371741208479940455678292869 : (((p5 → True) → False) → ((((p3 → p4) ∧ (p5 ∨ (p3 ∧ p1))) ∨ ((p4 → ((p2 ∧ True) ∧ (p5 → (True ∨ p1)))) → p5)) ∨ (p2 → p5))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h2 : (p5 → True) := by
    -- Implications on the right can always be decomposed.
    intro h3
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h4 := h1 h2
  -- False on the left can always be used.
  apply False.elim h4



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_136167068244702859453067711206 : (((p4 → ((True ∨ ((True ∨ p5) ∨ p1)) ∨ p2)) → (p5 → (p3 → ((p2 ∨ p1) ∨ (p5 → ((p4 → p1) ∨ p3)))))) ∨ (p4 → (True ∨ p4))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_620967051932179813462692013280 : (((((p5 ∨ p2) → ((p2 ∧ True) ∨ ((p3 ∨ ((True → (False ∧ p5)) ∨ ((p3 ∧ p1) ∨ False))) ∨ (((False → p5) ∧ p3) ∧ False)))) ∨ True) ∨ p4) ∧ True) := by
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
theorem thm_5_vars_186506697639746903573081921946 : (((False → ((True ∧ p3) ∧ (p1 ∨ (True → p2)))) ∧ (p5 ∧ p3)) → ((p2 ∨ (p1 → ((p4 → ((p1 → (False → False)) ∨ p5)) → p5))) ∨ False)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- Conjunctions on the left can always be decomposed.
  let h4 := h3.left
  let h5 := h3.right
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h6
  -- Implications on the right can always be decomposed.
  intro h7
  -- One of the premise coincides with the conclusion.
  exact h4



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_349935120920585345990493078409 : (p4 → ((((((((p3 ∨ ((p4 ∨ p4) ∧ (True → (True ∧ p3)))) → p4) → (p5 → p3)) → (True ∧ (p1 ∨ p3))) ∨ False) ∧ p3) ∧ p2) ∨ True)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_335771026194750711488066625888 : (p1 → ((((((((False → (False ∧ True)) → p1) → False) ∨ (p5 ∨ p3)) → ((True ∧ (False ∨ p5)) ∧ (p1 ∧ p2))) ∨ p1) ∨ (p5 → True)) ∧ True)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_301294292759266076143723217833 : (False ∨ (((p2 ∧ False) ∨ (p1 ∧ (p1 → p3))) → (p3 → ((p4 ∧ (p3 → (((True ∧ ((p5 ∧ (True → p5)) → p2)) ∧ False) ∧ p5))) → p2)))) := by
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
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h6 =>
    -- Conjunctions on the left can always be decomposed.
    let h7 := h6.left
    let h8 := h6.right
    -- False on the left can always be used.
    apply False.elim h8
  case inr h9 =>
    -- Conjunctions on the left can always be decomposed.
    let h10 := h9.left
    let h11 := h9.right
    -- We want to use the implication h5 based on <expert-advice>. So we show its premise.
    have h12 : p3 := by
      -- One of the premise coincides with the conclusion.
      exact h2
    -- We have shown the premise of h5, we can now drive its conclusion.
    let h13 := h5 h12
    -- We need to get the left conjuct of h13 based on <expert-advice>.
    let h14 := h13.left
    -- We need to get the right conjuct of h14 based on <expert-advice>.
    let h15 := h14.right
    -- False on the left can always be used.
    apply False.elim h15



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_748295516254644397555780815908 : ((((p2 → False) → (p4 ∨ ((p4 ∨ ((p1 ∨ ((False ∧ p2) ∨ ((True → p4) → p1))) ∧ True)) ∨ (((False ∨ (True ∨ False)) ∧ p3) ∧ p3)))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_259261393121942360036176456037 : ((False → p1) → ((((p3 ∨ (((p3 ∨ False) → p5) ∧ (p2 ∧ p2))) ∨ ((True ∧ ((p3 ∨ p5) → False)) → p1)) ∨ (p3 ∨ False)) ∨ (True ∨ p2))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_713447069285911970185630824867 : ((((p2 → (True → ((True ∨ p2) ∧ p4))) ∨ ((p4 ∨ (p4 ∧ p5)) ∨ (((p2 ∧ (p4 ∧ (True ∧ p3))) ∨ p1) → (p4 → (p3 ∧ p3))))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_1487127857116684982027643053 : (((False → (((False ∨ ((((p5 ∧ p1) ∧ (p3 ∨ p4)) ∧ (((True ∧ p3) → p5) ∨ False)) → False)) ∧ p1) ∧ False)) → p5) ∨ (False → False)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_116164751989593228576101797062 : (((p5 ∨ (False → p4)) ∧ ((((p1 → True) → p1) ∨ (p4 ∧ (p3 ∧ (((p3 ∧ (p5 → p5)) → p4) → (p1 ∧ True))))) ∨ False)) ∨ (p5 → p5)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_115792795595595505575084553069 : (((((p5 → p5) ∨ p1) ∨ p2) ∧ ((p3 → ((True ∨ False) → ((p3 ∧ (p2 ∧ p1)) ∨ (p1 ∧ True)))) ∧ ((p4 ∨ p5) ∧ p4))) ∨ (p3 → True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_604222925390312508518308674226 : ((((True → (((((False ∧ p2) → p3) → (False ∧ ((p4 ∧ (p1 ∨ True)) ∧ (True ∧ p3)))) ∧ ((False ∧ False) ∨ (p3 ∨ p1))) ∨ p1)) ∧ p2) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_216557925563415783132979413351 : ((((p4 ∧ True) ∧ p1) ∧ p4) → ((True ∧ ((((((True → (p2 ∧ p3)) ∧ p3) → p2) → p5) → False) ∧ ((p5 ∨ False) → (p2 → False)))) ∨ p4)) := by
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
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h3



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_193879924643963544472836943187 : ((False ∨ ((p3 ∧ ((p5 ∧ True) ∧ p3)) ∧ (False → p5))) → ((((p2 ∧ (p5 ∨ (p5 ∨ p5))) ∧ p1) ∨ (((False ∨ p2) ∨ True) ∧ p1)) ∨ True)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h2 =>
    -- False on the left can always be used.
    apply False.elim h2
  case inr h3 =>
    -- Conjunctions on the left can always be decomposed.
    let h4 := h3.left
    let h5 := h3.right
    -- Conjunctions on the left can always be decomposed.
    let h6 := h4.left
    let h7 := h4.right
    -- Conjunctions on the left can always be decomposed.
    let h8 := h7.left
    let h9 := h7.right
    -- Conjunctions on the left can always be decomposed.
    let h10 := h8.left
    let h11 := h8.right
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_185520691041958659697891176929 : ((p3 ∨ (((False ∨ p5) ∨ (p2 → ((p2 → False) ∨ p1))) ∨ True)) ∨ ((((p2 → p1) ∧ True) ∨ (p1 ∧ (False → True))) ∨ (False ∧ (p5 ∧ p3)))) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_681677296818623257724555915701 : ((((p4 → (((True ∨ p5) ∧ (p3 ∧ (p5 ∧ p1))) → (((p4 ∧ ((p3 ∧ True) ∨ p3)) ∨ False) ∨ p5))) → (p4 → ((p2 ∨ p3) ∨ False))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_231878374249704320192474777553 : (((True ∨ p2) → p2) → (((p1 → (p1 ∧ (p3 ∧ p1))) ∨ ((False ∨ (((True → p3) ∨ (p3 ∨ p4)) ∧ ((False → False) ∧ False))) ∨ p5)) ∨ True)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_336129989208871696616429762168 : (p1 → ((((True → (p4 ∨ True)) → ((p3 ∧ True) → (((p1 → p5) ∨ p2) ∨ (p5 → ((p2 ∧ p5) ∧ ((True → True) ∨ p1)))))) ∨ False) ∨ p1)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_549521412444681594257305942578 : (((False ∨ (p4 → (((p2 ∧ p5) → False) ∨ (((True ∨ (p3 ∧ False)) ∧ (((p2 → p2) ∧ ((True → p4) → p2)) ∨ (p2 ∨ p4))) ∧ p4)))) ∧ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
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
  -- One of the premise coincides with the conclusion.
  exact h1
  -- One of the premise coincides with the conclusion.
  exact h1
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_51254344921115637506454427556 : ((((p2 → p4) ∧ ((((p2 ∨ p3) → ((p3 ∨ p3) ∨ (False ∧ False))) ∧ p1) → (False ∧ True))) ∨ (((p4 ∨ (p2 → p4)) ∧ p5) ∧ p2)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_197449301926008352352374129930 : ((((p1 ∧ (p5 ∨ p1)) ∨ p1) ∧ (False ∧ True)) ∨ ((False → (p5 ∧ ((p3 ∧ p5) ∧ ((((False ∧ p5) ∨ (p5 → p3)) ∨ p2) ∨ p5)))) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_157460856513616451642725620375 : (((((p4 ∧ ((((p5 ∨ p4) ∧ p3) ∨ True) ∧ ((True → False) ∨ p5))) ∨ False) ∨ p3) ∨ (False → True)) ∨ ((p4 ∧ ((p3 ∧ p4) → False)) → p3)) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_324088116858290947267346768834 : (p5 ∨ (((True → p5) → ((p4 ∨ p5) ∨ (((p3 ∧ p4) → p5) ∧ p4))) ∨ (((p5 → (p3 → (p3 ∨ (p4 → True)))) ∧ p2) → (True ∨ p5)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
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
theorem thm_5_vars_208361593598164814551475881959 : (((False ∧ p1) ∨ ((p4 → p1) → True)) → (False ∨ (p4 → ((p5 ∨ ((p4 ∧ ((((p1 → p2) ∨ (p2 ∧ False)) ∧ False) ∨ False)) ∨ True)) ∧ p4)))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h2 =>
    -- Conjunctions on the left can always be decomposed.
    let h3 := h2.left
    let h4 := h2.right
    -- False on the left can always be used.
    apply False.elim h3
  case inr h5 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h6
    -- Conjunctions on the right can always be decomposed.
    apply And.intro
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro
    -- One of the premise coincides with the conclusion.
    exact h6



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_68630378485038369072802735574 : ((p4 → ((p2 ∨ (p1 ∧ (((p1 ∨ p4) ∧ ((True ∧ (p5 ∨ p4)) ∧ (p1 → (p5 ∧ ((p4 ∧ (True ∧ p5)) ∨ p5))))) ∧ True))) ∨ True)) ∨ False) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_345486237802917499427401384162 : (p3 → ((((p2 ∨ ((p3 ∧ (p1 ∨ ((True ∧ (p5 → p1)) ∨ (p5 ∧ (True ∨ True))))) ∧ p2)) ∧ p3) ∨ ((p2 ∨ (True ∨ p4)) ∨ False)) ∨ p4)) := by
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
theorem thm_5_vars_232087901629844670014660116148 : (((p4 ∨ p4) → p3) → (p4 → ((p3 → (((p1 ∧ (p4 → p2)) ∨ p4) ∧ (False ∨ (p2 ∧ p3)))) → ((False → p4) → ((p3 ∨ p4) → p2))))) := by
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
  -- Disjunctions on the left can always be decomposed.
  cases h5
  case inl h6 =>
    -- We want to use the implication h3 based on <expert-advice>. So we show its premise.
    have h7 : p3 := by
      -- One of the premise coincides with the conclusion.
      exact h6
    -- We have shown the premise of h3, we can now drive its conclusion.
    let h8 := h3 h7
    -- We need to get the right conjuct of h8 based on <expert-advice>.
    let h9 := h8.right
    -- Disjunctions on the left can always be decomposed.
    cases h9
    case inl h10 =>
      -- False on the left can always be used.
      apply False.elim h10
    case inr h11 =>
      -- Conjunctions on the left can always be decomposed.
      let h12 := h11.left
      let h13 := h11.right
      -- One of the premise coincides with the conclusion.
      exact h12
  case inr h14 =>
    -- We want to use the implication h3 based on <expert-advice>. So we show its premise.
    have h15 : p3 := by
      -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
      have h16 : (p4 ∨ p4) := by
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- One of the premise coincides with the conclusion.
        exact h2
      -- We have shown the premise of h1, we can now drive its conclusion.
      let h17 := h1 h16
      -- One of the premise coincides with the conclusion.
      exact h17
    -- We have shown the premise of h3, we can now drive its conclusion.
    let h18 := h3 h15
    -- We need to get the right conjuct of h18 based on <expert-advice>.
    let h19 := h18.right
    -- Disjunctions on the left can always be decomposed.
    cases h19
    case inl h20 =>
      -- False on the left can always be used.
      apply False.elim h20
    case inr h21 =>
      -- Conjunctions on the left can always be decomposed.
      let h22 := h21.left
      let h23 := h21.right
      -- One of the premise coincides with the conclusion.
      exact h22



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_60212390922736745888189921152 : (((True → False) → (((p2 ∧ False) ∧ (((((p3 ∧ (True → p3)) ∧ p1) ∨ (p5 → p2)) ∨ p5) ∨ p2)) ∧ (((p5 → False) ∧ p5) → False))) ∨ p1) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
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
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h4 : True := by
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h5 := h1 h4
  -- False on the left can always be used.
  apply False.elim h5
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h6 : True := by
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h7 := h1 h6
  -- False on the left can always be used.
  apply False.elim h7
  -- Implications on the right can always be decomposed.
  intro h8
  -- Conjunctions on the left can always be decomposed.
  let h9 := h8.left
  let h10 := h8.right
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h11 : True := by
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h12 := h1 h11
  -- False on the left can always be used.
  apply False.elim h12



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_165505563751324291271031157373 : ((((((p1 ∨ p4) ∧ (True ∨ (p4 ∧ p1))) → p4) ∧ p1) → (((p2 ∨ p2) ∨ p2) ∧ p2)) ∨ (((p2 → True) → (True ∨ (p1 ∧ p5))) ∨ p1)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_765539347603771297700021793208 : (((p4 ∧ (((p3 ∧ ((False → p3) → ((p2 ∧ p5) ∨ (((True ∨ p1) → p5) ∨ True)))) ∨ p1) → (p1 → (p3 ∧ ((p1 → False) ∨ False))))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_116704551417941456656278254880 : (((p1 ∧ False) ∨ (((p4 ∨ p5) ∧ ((p3 ∨ p2) → ((p3 ∧ ((p3 → (p2 → True)) ∨ True)) → (p5 ∨ p2)))) ∨ (p4 ∧ p1))) ∨ (p2 → True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_758432379356647529013640817223 : (((p2 ∧ (((True → p4) ∧ (p3 ∧ ((False → ((p2 → (((((p1 ∧ p1) ∨ p1) ∨ p3) → False) ∧ p4)) ∨ (True ∨ False))) → False))) ∧ p4)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_69006621523410163581940851053 : ((p5 → (((p1 ∨ (p5 → p3)) ∨ ((((p3 → False) ∨ p2) ∨ False) ∨ ((((((True ∨ False) ∧ p3) ∧ p5) ∨ p2) ∨ p3) ∨ p2))) ∧ p2)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_42686967006449564374578740864 : (((p5 ∨ ((((p3 → (p2 ∧ ((p1 ∧ p3) → (((p2 ∧ (p4 ∧ False)) ∨ p4) → (True ∨ (p2 → True)))))) ∨ p5) → p1) ∨ p5)) ∨ p5) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_152050808872711744713859435495 : (((((((p3 → p4) ∨ (p5 ∧ p3)) ∨ p4) → p3) ∨ p1) ∨ ((p3 ∨ p5) ∧ (p1 → (p3 ∧ (True → p4))))) → (p5 → (p4 → (p2 ∨ p4)))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Implications on the right can always be decomposed.
  intro h3
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h4 =>
    -- Disjunctions on the left can always be decomposed.
    cases h4
    case inl h5 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- One of the premise coincides with the conclusion.
      exact h3
    case inr h6 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- One of the premise coincides with the conclusion.
      exact h3
  case inr h7 =>
    -- Conjunctions on the left can always be decomposed.
    let h8 := h7.left
    let h9 := h7.right
    -- Disjunctions on the left can always be decomposed.
    cases h8
    case inl h10 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- One of the premise coincides with the conclusion.
      exact h3
    case inr h11 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- One of the premise coincides with the conclusion.
      exact h3



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_192666507652892063083897710035 : (((((p3 → p1) ∧ ((p3 → p4) ∧ p4)) → False) → p5) → (p4 ∨ (True ∧ (False → ((((p2 ∨ p5) ∧ (p5 ∨ (p2 ∨ p2))) ∧ p2) → p5))))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- True on the right can always be proven directly.
  apply True.intro
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
    -- Disjunctions on the left can always be decomposed.
    cases h7
    case inl h9 =>
      -- False on the left can always be used.
      apply False.elim h2
    case inr h10 =>
      -- Disjunctions on the left can always be decomposed.
      cases h10
      case inl h11 =>
        -- False on the left can always be used.
        apply False.elim h2
      case inr h12 =>
        -- False on the left can always be used.
        apply False.elim h2
  case inr h13 =>
    -- Disjunctions on the left can always be decomposed.
    cases h7
    case inl h14 =>
      -- False on the left can always be used.
      apply False.elim h2
    case inr h15 =>
      -- Disjunctions on the left can always be decomposed.
      cases h15
      case inl h16 =>
        -- False on the left can always be used.
        apply False.elim h2
      case inr h17 =>
        -- False on the left can always be used.
        apply False.elim h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_180998710512385357664773826314 : (((p5 ∧ p1) ∨ ((p2 → (p1 → (p3 ∧ (p4 ∧ (False ∧ False))))) ∨ True)) → (((((p3 ∧ p4) ∨ (p3 ∨ (p4 → True))) ∨ p4) ∨ p5) ∨ True)) := by
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



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_115184217225579774495217233787 : (((((False → ((p3 → True) ∧ False)) ∧ p3) → (p3 ∨ True)) ∧ (((p4 ∨ (((p1 → p1) ∨ False) → (p4 → p3))) ∧ p1) ∨ True)) ∨ (p1 → p1)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_80073393090596162880963158319 : ((((((False ∨ (((((False → p1) ∧ (p1 → p4)) → p1) ∧ (p4 → (p5 → True))) ∧ (p3 → p2))) ∨ p1) ∨ True) ∨ p5) → (p2 ∧ p3)) → p3) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h2 : ((((False ∨ (((((False → p1) ∧ (p1 → p4)) → p1) ∧ (p4 → (p5 → True))) ∧ (p3 → p2))) ∨ p1) ∨ True) ∨ p5) := by
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h3 := h1 h2
  -- We need to get the right conjuct of h3 based on <expert-advice>.
  let h4 := h3.right
  -- One of the premise coincides with the conclusion.
  exact h4



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_175429274308936033080378447608 : ((p1 → ((False ∨ (False ∨ (((((True ∧ p1) ∧ p5) → p4) → False) ∧ p4))) ∧ True)) → (p2 ∨ (True ∧ (p4 → (((False → True) → p1) ∨ p4))))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- Implications on the right can always be decomposed.
  intro h2
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_192237631466488624719783032416 : (((((p4 ∧ True) → (p2 ∨ p1)) ∨ (p3 ∨ p4)) ∧ True) → ((((p3 ∧ (p5 ∧ p2)) ∨ p1) ∨ (p3 → ((False ∨ (p4 ∨ False)) ∨ True))) ∨ p1)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- Disjunctions on the left can always be decomposed.
  cases h2
  case inl h4 =>
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h5
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro
  case inr h6 =>
    -- Disjunctions on the left can always be decomposed.
    cases h6
    case inl h7 =>
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Implications on the right can always be decomposed.
      intro h8
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- True on the right can always be proven directly.
      apply True.intro
    case inr h9 =>
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Implications on the right can always be decomposed.
      intro h10
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- True on the right can always be proven directly.
      apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_323710143829217221033244777247 : (p5 ∨ ((((((((True → p1) ∨ p4) → p5) ∧ False) → (True ∨ p3)) → (p3 → p2)) ∧ (p3 ∨ (p1 ∨ p3))) → ((p1 ∨ p1) → (p3 → p1)))) := by
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
    -- Conjunctions on the left can always be decomposed.
    let h5 := h1.left
    let h6 := h1.right
    -- Disjunctions on the left can always be decomposed.
    cases h6
    case inl h7 =>
      -- One of the premise coincides with the conclusion.
      exact h4
    case inr h8 =>
      -- Disjunctions on the left can always be decomposed.
      cases h8
      case inl h9 =>
        -- One of the premise coincides with the conclusion.
        exact h9
      case inr h10 =>
        -- One of the premise coincides with the conclusion.
        exact h4
  case inr h11 =>
    -- Conjunctions on the left can always be decomposed.
    let h12 := h1.left
    let h13 := h1.right
    -- Disjunctions on the left can always be decomposed.
    cases h13
    case inl h14 =>
      -- One of the premise coincides with the conclusion.
      exact h11
    case inr h15 =>
      -- Disjunctions on the left can always be decomposed.
      cases h15
      case inl h16 =>
        -- One of the premise coincides with the conclusion.
        exact h16
      case inr h17 =>
        -- One of the premise coincides with the conclusion.
        exact h11



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_684926282575887085060276909561 : ((((p1 ∧ (p4 ∧ (p5 → (((((p5 ∨ p2) ∧ (p5 → (p4 ∨ p3))) → False) ∨ False) ∨ False)))) ∨ ((False ∧ p4) ∨ (p4 ∨ (p3 → p3)))) ∨ p4) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
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
  -- One of the premise coincides with the conclusion.
  exact h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_40293623127338482033856188633 : ((((p5 → ((((p5 ∧ p5) ∨ (p1 ∨ ((((p4 → (False ∨ (p5 → p1))) → False) ∨ (p1 → p1)) → p5))) → False) ∧ True)) ∧ p3) ∨ False) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_253795537646706767365838760205 : ((p1 ∧ p2) → ((((p1 → (p5 ∨ (((p1 ∨ ((False ∧ p5) → p4)) → (p3 ∨ (True → p1))) ∨ (p4 → p4)))) ∨ p1) → False) ∨ (p2 ∧ True))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- One of the premise coincides with the conclusion.
  exact h3
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_152052030360794720199935948476 : (((((False → True) ∨ (True ∧ (p4 → (True → p5)))) ∨ p3) ∨ (p4 ∨ (((p3 → p4) → False) → (False ∧ True)))) → ((p1 ∧ p4) ∨ (p3 → True))) := by
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
        -- Implications on the right can always be decomposed.
        intro h5
        -- True on the right can always be proven directly.
        apply True.intro
      case inr h6 =>
        -- Conjunctions on the left can always be decomposed.
        let h7 := h6.left
        let h8 := h6.right
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- Implications on the right can always be decomposed.
        intro h9
        -- True on the right can always be proven directly.
        apply True.intro
    case inr h10 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Implications on the right can always be decomposed.
      intro h11
      -- True on the right can always be proven directly.
      apply True.intro
  case inr h12 =>
    -- Disjunctions on the left can always be decomposed.
    cases h12
    case inl h13 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Implications on the right can always be decomposed.
      intro h14
      -- True on the right can always be proven directly.
      apply True.intro
    case inr h15 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Implications on the right can always be decomposed.
      intro h16
      -- True on the right can always be proven directly.
      apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_228616444424398276515733548066 : ((p1 ∨ (p3 → p1)) ∨ (((((p4 ∨ (False ∧ p3)) ∧ p3) ∧ False) ∨ (p4 ∨ p2)) ∨ (((False → False) ∧ True) ∨ ((p4 → (p4 ∧ True)) → p2)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h1
  -- False on the left can always be used.
  apply False.elim h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_962399251588504982960676954251 : ((((True → False) ∧ ((((p2 ∧ p4) → ((p1 ∧ ((((p1 ∧ ((p4 → p4) ∧ p2)) ∧ p1) → p4) ∧ p2)) ∧ (True ∧ p3))) → False) → p5)) → p4) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
  have h4 : True := by
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h2, we can now drive its conclusion.
  let h5 := h2 h4
  -- False on the left can always be used.
  apply False.elim h5
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_747930395254469488720454760321 : ((((False → p5) → ((p4 → (False ∨ p1)) ∧ ((p5 ∨ (p5 ∧ p2)) ∧ ((((p5 ∧ (False → (True ∨ p2))) → p5) ∧ (False → p4)) → p5)))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_190048311171297927877953334096 : ((((p1 ∧ (False ∨ ((p5 ∨ p4) ∧ False))) ∨ False) ∧ p4) ∨ (p3 → (((False ∨ ((True → (p5 ∨ ((p1 ∨ p2) → p1))) → p3)) ∨ p1) → p3))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
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
      -- False on the left can always be used.
      apply False.elim h4
    case inr h5 =>
      -- One of the premise coincides with the conclusion.
      exact h1
  case inr h6 =>
    -- One of the premise coincides with the conclusion.
    exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_329034690632210708762023786002 : (True → (((True ∨ False) → ((p3 ∧ p2) ∨ p1)) → (True ∧ (((((p5 → p3) → False) ∧ (p1 → p3)) ∨ p1) ∨ (p2 → ((p2 ∧ False) → False)))))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h3
  -- Implications on the right can always be decomposed.
  intro h4
  -- Conjunctions on the left can always be decomposed.
  let h5 := h4.left
  let h6 := h4.right
  -- False on the left can always be used.
  apply False.elim h6



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_304095072168626640612600972061 : (p1 ∨ ((True → (True → (p4 ∨ ((p4 ∨ (((p4 → (True → (False → ((p2 ∧ p2) ∨ (True → p3))))) → p5) ∧ True)) → (False ∧ p1))))) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_70577246682063457389650467600 : (((((p4 ∧ (False → (p5 → p2))) ∨ (((((p4 → (True ∧ True)) ∧ p5) → False) ∨ p5) ∨ (True ∨ False))) → ((False ∧ p4) ∧ False)) ∧ p5) → p1) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
  have h4 : ((p4 ∧ (False → (p5 → p2))) ∨ (((((p4 → (True ∧ True)) ∧ p5) → False) ∨ p5) ∨ (True ∨ False))) := by
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h3
  -- We have shown the premise of h2, we can now drive its conclusion.
  let h5 := h2 h4
  -- We need to get the right conjuct of h5 based on <expert-advice>.
  let h6 := h5.right
  -- False on the left can always be used.
  apply False.elim h6



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_65091270105830353734010700003 : ((p2 ∨ (p1 ∨ (((p1 ∨ ((p3 → p1) → (p4 ∧ (p4 ∨ (p5 ∧ (p5 ∨ p4)))))) → False) → ((True → (p5 ∨ (p4 ∨ p2))) ∧ p3)))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_57148635933742592432105878161 : ((((p5 → False) ∧ p2) ∨ (((((((p2 → p2) → (p1 ∧ (p4 ∧ True))) ∨ ((True → True) ∨ (p1 → False))) ∧ p1) ∧ p5) ∨ True) ∨ p3)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_166336976019858407776881516429 : ((p5 ∧ (p4 ∨ ((((False → p2) ∨ (p3 ∧ p5)) ∨ (p3 ∧ p1)) → (p4 ∨ (p1 ∧ p1))))) ∨ ((True ∨ ((True ∨ p4) ∨ p4)) ∨ (p5 ∧ p4))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_775274088565631853487968539980 : (((False ∨ ((p4 → p4) → ((p3 → ((p3 ∨ p1) → ((((p2 → (True → p4)) ∨ p4) ∨ (p4 → False)) → p1))) → (p3 ∨ (p1 ∧ False))))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_234681872193201752086721858023 : ((p4 → (p4 ∧ True)) → ((((p5 → ((p2 ∨ p4) → (((p3 ∨ (p4 ∧ (p2 ∨ (p2 ∨ p3)))) → (False ∨ p2)) → p2))) ∧ p2) → p3) ∨ True)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_668530100658082110910124346026 : (((((((p1 ∧ ((p4 ∧ p2) ∨ p5)) → (True ∨ p4)) → ((False ∨ p5) → (((p4 → p5) ∨ p2) ∧ p2))) ∧ p4) ∨ (p3 ∧ (False → p3))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_219331914801880700471962601781 : ((p2 ∨ (p1 ∨ (p5 ∨ p3))) → (((p3 ∨ (((p1 ∨ (True ∨ p3)) ∧ ((False ∧ True) → False)) ∨ p1)) ∧ p2) → ((p4 ∨ (p2 ∧ p1)) ∨ True))) := by
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
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- True on the right can always be proven directly.
      apply True.intro
    case inr h7 =>
      -- Disjunctions on the left can always be decomposed.
      cases h7
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
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- True on the right can always be proven directly.
          apply True.intro
  case inr h12 =>
    -- Disjunctions on the left can always be decomposed.
    cases h12
    case inl h13 =>
      -- Conjunctions on the left can always be decomposed.
      let h14 := h13.left
      let h15 := h13.right
      -- Disjunctions on the left can always be decomposed.
      cases h14
      case inl h16 =>
        -- Disjunctions on the left can always be decomposed.
        cases h1
        case inl h17 =>
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
            -- True on the right can always be proven directly.
            apply True.intro
          case inr h20 =>
            -- Disjunctions on the left can always be decomposed.
            cases h20
            case inl h21 =>
              -- Show the right disjunct based on <expert-advice>.
              apply Or.inr
              -- True on the right can always be proven directly.
              apply True.intro
            case inr h22 =>
              -- Show the right disjunct based on <expert-advice>.
              apply Or.inr
              -- True on the right can always be proven directly.
              apply True.intro
      case inr h23 =>
        -- Disjunctions on the left can always be decomposed.
        cases h23
        case inl h24 =>
          -- Disjunctions on the left can always be decomposed.
          cases h1
          case inl h25 =>
            -- Show the right disjunct based on <expert-advice>.
            apply Or.inr
            -- True on the right can always be proven directly.
            apply True.intro
          case inr h26 =>
            -- Disjunctions on the left can always be decomposed.
            cases h26
            case inl h27 =>
              -- Show the right disjunct based on <expert-advice>.
              apply Or.inr
              -- True on the right can always be proven directly.
              apply True.intro
            case inr h28 =>
              -- Disjunctions on the left can always be decomposed.
              cases h28
              case inl h29 =>
                -- Show the right disjunct based on <expert-advice>.
                apply Or.inr
                -- True on the right can always be proven directly.
                apply True.intro
              case inr h30 =>
                -- Show the right disjunct based on <expert-advice>.
                apply Or.inr
                -- True on the right can always be proven directly.
                apply True.intro
        case inr h31 =>
          -- Disjunctions on the left can always be decomposed.
          cases h1
          case inl h32 =>
            -- Show the right disjunct based on <expert-advice>.
            apply Or.inr
            -- True on the right can always be proven directly.
            apply True.intro
          case inr h33 =>
            -- Disjunctions on the left can always be decomposed.
            cases h33
            case inl h34 =>
              -- Show the right disjunct based on <expert-advice>.
              apply Or.inr
              -- True on the right can always be proven directly.
              apply True.intro
            case inr h35 =>
              -- Disjunctions on the left can always be decomposed.
              cases h35
              case inl h36 =>
                -- Show the right disjunct based on <expert-advice>.
                apply Or.inr
                -- True on the right can always be proven directly.
                apply True.intro
              case inr h37 =>
                -- Show the right disjunct based on <expert-advice>.
                apply Or.inr
                -- True on the right can always be proven directly.
                apply True.intro
    case inr h38 =>
      -- Disjunctions on the left can always be decomposed.
      cases h1
      case inl h39 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- True on the right can always be proven directly.
        apply True.intro
      case inr h40 =>
        -- Disjunctions on the left can always be decomposed.
        cases h40
        case inl h41 =>
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- True on the right can always be proven directly.
          apply True.intro
        case inr h42 =>
          -- Disjunctions on the left can always be decomposed.
          cases h42
          case inl h43 =>
            -- Show the right disjunct based on <expert-advice>.
            apply Or.inr
            -- True on the right can always be proven directly.
            apply True.intro
          case inr h44 =>
            -- Show the right disjunct based on <expert-advice>.
            apply Or.inr
            -- True on the right can always be proven directly.
            apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_262483289474505794187048104217 : (True ∧ ((True → (((((p2 ∧ (p3 ∨ p4)) ∨ p5) ∨ p3) ∨ (((((p4 ∨ p1) → ((True ∨ False) → p5)) → p5) ∨ p1) ∨ p2)) ∨ True)) ∨ p3)) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_327122883702514044915215285525 : (True → (((True → False) → (False ∨ (((p5 ∨ (True ∨ False)) ∧ (p4 ∨ (p4 ∧ p2))) ∨ (p2 ∧ (p2 ∧ (True ∨ (p2 ∧ (p5 ∧ False)))))))) ∨ True)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_178789982761121578934602402205 : ((((p2 ∧ p3) ∧ p5) ∨ ((p3 ∧ p4) ∨ ((p5 ∧ (p5 → p3)) ∧ p3))) ∨ ((((p3 ∧ (True ∧ (p1 ∧ True))) ∨ True) ∨ p5) ∨ (p2 ∨ p2))) := by
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
theorem thm_5_vars_178895773201185438106100005284 : (((False ∨ p5) ∧ ((p3 → (p5 ∨ (p2 ∧ True))) ∨ (p3 ∧ (p4 → p4)))) ∨ (((True ∧ p2) → (p3 ∨ ((p1 → True) ∨ p5))) ∨ (p5 → p5))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_69307436142818178014176100837 : ((p5 → (p2 ∧ (((p1 ∧ p5) ∨ ((((p1 ∨ p1) ∧ (p4 → (p5 ∧ p1))) ∨ p1) → (p1 → ((True ∨ (p4 ∧ False)) ∨ p5)))) → False))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_611885662459399154170792951195 : (((((p5 → ((((True ∨ p4) ∨ p2) ∧ (((((p3 ∧ True) → (p4 → p4)) → p4) ∧ p3) → False)) ∨ ((p4 ∨ p2) → p3))) → p1) ∨ p5) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_8572403194865325257162423766 : ((((((((True → (p1 ∧ False)) → (p4 → False)) ∧ (False ∧ (((p4 ∨ p2) → (True ∧ p1)) ∨ p1))) ∨ p3) ∨ p2) ∨ (p4 ∨ True)) ∨ p1) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_659837332018533321316280382885 : (((((True → (((((False ∨ ((((p2 ∨ p3) ∨ (False → (p1 → False))) ∧ False) ∧ False)) → p2) ∧ p5) ∧ p2) ∧ p4)) ∧ True) → (p1 ∨ p1)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_307150324632988084620910136396 : (p1 ∨ (False ∨ (((True ∨ p5) → False) ∨ ((p3 ∧ (False ∧ p3)) ∨ (p2 ∨ (((p1 ∨ p1) → (((True ∧ p3) → p3) ∨ True)) ∧ (True ∨ True))))))) := by
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
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_45933358704587724432671042903 : (((p4 → (p5 → (((((p5 ∧ (p5 ∨ (False ∧ (p4 ∧ (True ∧ False))))) → ((p4 ∧ (True ∨ p1)) ∧ p3)) → p3) → p5) ∨ True))) → p4) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_705612929666616319087015081701 : (((((p3 ∨ (p4 ∨ (True ∨ (p4 ∧ False)))) → p2) ∧ (p5 → (((p4 → ((p4 ∧ (p5 ∨ p3)) → ((p1 ∨ p5) ∨ p3))) → p3) ∨ True))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_4511784965180952891211770046 : (p3 → (((False ∧ True) ∨ (p1 ∧ ((p5 ∨ ((((p3 ∨ p3) ∨ ((p2 ∧ (p3 → False)) → False)) ∨ (p1 → p5)) ∧ p4)) ∧ p2))) ∨ True)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_670169361656270592180674728615 : (((((p2 ∨ (p5 → (p3 → (True → p2)))) → ((p4 → ((p2 → False) ∨ (p5 → (p2 → (p1 ∨ p4))))) ∨ p5)) ∨ (p3 ∧ (p3 → p2))) ∨ p2) ∧ True) := by
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
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Implications on the right can always be decomposed.
    intro h3
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h4
    -- Implications on the right can always be decomposed.
    intro h5
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h3
  case inr h6 =>
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Implications on the right can always be decomposed.
    intro h7
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h8
    -- Implications on the right can always be decomposed.
    intro h9
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h7
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_57939080421443937360409901486 : (((False → (p1 ∨ p2)) → (p4 ∨ (True ∧ (p2 → ((((p3 → (False ∨ (p5 ∨ p5))) → False) → (((p4 → p2) ∧ p4) ∨ p1)) ∨ p4))))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_254063682756362183675975170509 : ((p2 ∧ True) → (True ∧ ((p4 ∧ (((False ∧ p5) ∨ ((p5 ∨ p5) ∨ (((((p1 ∨ True) ∨ True) ∧ (False → p4)) → p1) ∧ p2))) ∨ p3)) ∨ True))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_50887681146654129115314780342 : ((((((p2 ∧ p2) → p3) ∧ ((p5 ∧ p1) ∨ ((p4 ∧ (False ∨ False)) → (p4 → p5)))) → p2) ∧ (p3 ∧ (False ∧ (p4 → (p5 → True))))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



