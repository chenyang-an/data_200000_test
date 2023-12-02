variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_48043834197485723072239180165 : ((((((((p2 ∨ p3) ∧ p5) → False) ∧ (p5 ∨ p2)) ∨ False) → ((((p4 ∧ p3) ∧ ((True → True) ∧ p4)) ∨ True) ∨ p4)) → (False ∨ p3)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_44674191731609182169658131943 : (((((p4 ∨ (p5 → (p4 ∨ p4))) → p5) → ((((p1 ∧ ((((False → (True ∧ p2)) ∨ p1) ∧ False) ∧ False)) ∨ p5) ∨ p5) → p5)) → False) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_41703822391327140043897554769 : (((((p1 ∧ True) ∨ ((p4 ∨ False) → p5)) → (((True → (p1 ∧ ((p5 ∨ p5) ∨ ((p2 ∨ True) ∧ p1)))) ∨ (p5 ∨ p5)) ∨ p3)) ∨ p3) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_680689521878763053750379159230 : (((((((True → p3) ∨ p3) ∨ p4) ∧ (False ∨ ((False ∧ p3) ∨ (((p4 ∧ (p1 ∧ p2)) → p2) → False)))) → (((p1 ∧ p5) → False) ∧ p1)) ∨ p1) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h2
  -- Conjunctions on the left can always be decomposed.
  let h3 := h2.left
  let h4 := h2.right
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
      cases h6
      case inl h9 =>
        -- False on the left can always be used.
        apply False.elim h9
      case inr h10 =>
        -- Disjunctions on the left can always be decomposed.
        cases h10
        case inl h11 =>
          -- Conjunctions on the left can always be decomposed.
          let h12 := h11.left
          let h13 := h11.right
          -- False on the left can always be used.
          apply False.elim h12
        case inr h14 =>
          -- We want to use the implication h14 based on <expert-advice>. So we show its premise.
          have h15 : ((p4 ∧ (p1 ∧ p2)) → p2) := by
            -- Implications on the right can always be decomposed.
            intro h16
            -- Conjunctions on the left can always be decomposed.
            let h17 := h16.left
            let h18 := h16.right
            -- Conjunctions on the left can always be decomposed.
            let h19 := h18.left
            let h20 := h18.right
            -- One of the premise coincides with the conclusion.
            exact h20
          -- We have shown the premise of h14, we can now drive its conclusion.
          let h21 := h14 h15
          -- False on the left can always be used.
          apply False.elim h21
    case inr h22 =>
      -- Disjunctions on the left can always be decomposed.
      cases h6
      case inl h23 =>
        -- False on the left can always be used.
        apply False.elim h23
      case inr h24 =>
        -- Disjunctions on the left can always be decomposed.
        cases h24
        case inl h25 =>
          -- Conjunctions on the left can always be decomposed.
          let h26 := h25.left
          let h27 := h25.right
          -- False on the left can always be used.
          apply False.elim h26
        case inr h28 =>
          -- We want to use the implication h28 based on <expert-advice>. So we show its premise.
          have h29 : ((p4 ∧ (p1 ∧ p2)) → p2) := by
            -- Implications on the right can always be decomposed.
            intro h30
            -- Conjunctions on the left can always be decomposed.
            let h31 := h30.left
            let h32 := h30.right
            -- Conjunctions on the left can always be decomposed.
            let h33 := h32.left
            let h34 := h32.right
            -- One of the premise coincides with the conclusion.
            exact h34
          -- We have shown the premise of h28, we can now drive its conclusion.
          let h35 := h28 h29
          -- False on the left can always be used.
          apply False.elim h35
  case inr h36 =>
    -- Disjunctions on the left can always be decomposed.
    cases h6
    case inl h37 =>
      -- False on the left can always be used.
      apply False.elim h37
    case inr h38 =>
      -- Disjunctions on the left can always be decomposed.
      cases h38
      case inl h39 =>
        -- Conjunctions on the left can always be decomposed.
        let h40 := h39.left
        let h41 := h39.right
        -- False on the left can always be used.
        apply False.elim h40
      case inr h42 =>
        -- We want to use the implication h42 based on <expert-advice>. So we show its premise.
        have h43 : ((p4 ∧ (p1 ∧ p2)) → p2) := by
          -- Implications on the right can always be decomposed.
          intro h44
          -- Conjunctions on the left can always be decomposed.
          let h45 := h44.left
          let h46 := h44.right
          -- Conjunctions on the left can always be decomposed.
          let h47 := h46.left
          let h48 := h46.right
          -- One of the premise coincides with the conclusion.
          exact h48
        -- We have shown the premise of h42, we can now drive its conclusion.
        let h49 := h42 h43
        -- False on the left can always be used.
        apply False.elim h49
  -- Conjunctions on the left can always be decomposed.
  let h50 := h1.left
  let h51 := h1.right
  -- Disjunctions on the left can always be decomposed.
  cases h50
  case inl h52 =>
    -- Disjunctions on the left can always be decomposed.
    cases h52
    case inl h53 =>
      -- Disjunctions on the left can always be decomposed.
      cases h51
      case inl h54 =>
        -- False on the left can always be used.
        apply False.elim h54
      case inr h55 =>
        -- Disjunctions on the left can always be decomposed.
        cases h55
        case inl h56 =>
          -- Conjunctions on the left can always be decomposed.
          let h57 := h56.left
          let h58 := h56.right
          -- False on the left can always be used.
          apply False.elim h57
        case inr h59 =>
          -- We want to use the implication h59 based on <expert-advice>. So we show its premise.
          have h60 : ((p4 ∧ (p1 ∧ p2)) → p2) := by
            -- Implications on the right can always be decomposed.
            intro h61
            -- Conjunctions on the left can always be decomposed.
            let h62 := h61.left
            let h63 := h61.right
            -- Conjunctions on the left can always be decomposed.
            let h64 := h63.left
            let h65 := h63.right
            -- One of the premise coincides with the conclusion.
            exact h65
          -- We have shown the premise of h59, we can now drive its conclusion.
          let h66 := h59 h60
          -- False on the left can always be used.
          apply False.elim h66
    case inr h67 =>
      -- Disjunctions on the left can always be decomposed.
      cases h51
      case inl h68 =>
        -- False on the left can always be used.
        apply False.elim h68
      case inr h69 =>
        -- Disjunctions on the left can always be decomposed.
        cases h69
        case inl h70 =>
          -- Conjunctions on the left can always be decomposed.
          let h71 := h70.left
          let h72 := h70.right
          -- False on the left can always be used.
          apply False.elim h71
        case inr h73 =>
          -- We want to use the implication h73 based on <expert-advice>. So we show its premise.
          have h74 : ((p4 ∧ (p1 ∧ p2)) → p2) := by
            -- Implications on the right can always be decomposed.
            intro h75
            -- Conjunctions on the left can always be decomposed.
            let h76 := h75.left
            let h77 := h75.right
            -- Conjunctions on the left can always be decomposed.
            let h78 := h77.left
            let h79 := h77.right
            -- One of the premise coincides with the conclusion.
            exact h79
          -- We have shown the premise of h73, we can now drive its conclusion.
          let h80 := h73 h74
          -- False on the left can always be used.
          apply False.elim h80
  case inr h81 =>
    -- Disjunctions on the left can always be decomposed.
    cases h51
    case inl h82 =>
      -- False on the left can always be used.
      apply False.elim h82
    case inr h83 =>
      -- Disjunctions on the left can always be decomposed.
      cases h83
      case inl h84 =>
        -- Conjunctions on the left can always be decomposed.
        let h85 := h84.left
        let h86 := h84.right
        -- False on the left can always be used.
        apply False.elim h85
      case inr h87 =>
        -- We want to use the implication h87 based on <expert-advice>. So we show its premise.
        have h88 : ((p4 ∧ (p1 ∧ p2)) → p2) := by
          -- Implications on the right can always be decomposed.
          intro h89
          -- Conjunctions on the left can always be decomposed.
          let h90 := h89.left
          let h91 := h89.right
          -- Conjunctions on the left can always be decomposed.
          let h92 := h91.left
          let h93 := h91.right
          -- One of the premise coincides with the conclusion.
          exact h93
        -- We have shown the premise of h87, we can now drive its conclusion.
        let h94 := h87 h88
        -- False on the left can always be used.
        apply False.elim h94
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_340827228996857417729413815795 : (p2 → (((p3 ∨ ((((p3 ∧ (p2 ∧ p1)) ∨ p3) ∧ (((p5 → (p2 ∨ p5)) → p2) ∧ (p1 ∧ p3))) ∧ (p3 ∨ p4))) ∨ (p1 → p3)) ∨ p2)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_684440536126891872610397912433 : ((((((p2 ∨ p5) ∨ (p3 → ((p5 → False) ∧ True))) ∨ (True → ((False → (p4 → p1)) ∧ p1))) ∨ ((p3 → (False ∧ (p2 ∧ p3))) → False)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_51620537456076950303776601747 : ((((((p3 ∧ p2) → p5) ∨ (False ∧ ((p4 ∧ (True ∨ (True ∧ p5))) ∧ p1))) ∧ p2) ∧ ((p4 → (p1 ∨ (p2 ∧ False))) ∨ (True ∨ True))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_204221887363150829884112072766 : ((((p2 ∨ (p3 → p4)) → p3) ∧ p2) ∨ (((True ∨ p4) ∧ p2) → ((((p5 → ((p5 ∧ p4) → True)) ∧ (False ∨ (False ∧ p5))) ∨ False) → p2))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
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
    -- Disjunctions on the left can always be decomposed.
    cases h5
    case inl h6 =>
      -- False on the left can always be used.
      apply False.elim h6
    case inr h7 =>
      -- Conjunctions on the left can always be decomposed.
      let h8 := h7.left
      let h9 := h7.right
      -- False on the left can always be used.
      apply False.elim h8
  case inr h10 =>
    -- False on the left can always be used.
    apply False.elim h10



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_45119045260722679648195295943 : ((((p5 ∨ p2) → ((((True → p1) → p2) ∨ (p5 ∨ (False → p3))) → ((p5 → ((p4 → (p5 ∧ p5)) ∧ (False ∨ p2))) ∨ True))) → p2) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_310672949232897536465493124844 : (p2 ∨ (((p3 ∧ p3) ∨ (p3 ∧ True)) → ((p3 ∨ ((False ∨ p1) ∧ p4)) → (p4 ∨ (((False ∨ True) → False) → ((p4 ∨ p2) ∧ (p1 ∨ p3))))))) := by
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
    cases h1
    case inl h4 =>
      -- Conjunctions on the left can always be decomposed.
      let h5 := h4.left
      let h6 := h4.right
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Implications on the right can always be decomposed.
      intro h7
      -- Conjunctions on the right can always be decomposed.
      apply And.intro
      -- We want to use the implication h7 based on <expert-advice>. So we show its premise.
      have h8 : (False ∨ True) := by
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- True on the right can always be proven directly.
        apply True.intro
      -- We have shown the premise of h7, we can now drive its conclusion.
      let h9 := h7 h8
      -- False on the left can always be used.
      apply False.elim h9
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- One of the premise coincides with the conclusion.
      exact h6
    case inr h10 =>
      -- Conjunctions on the left can always be decomposed.
      let h11 := h10.left
      let h12 := h10.right
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Implications on the right can always be decomposed.
      intro h13
      -- Conjunctions on the right can always be decomposed.
      apply And.intro
      -- We want to use the implication h13 based on <expert-advice>. So we show its premise.
      have h14 : (False ∨ True) := by
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- True on the right can always be proven directly.
        apply True.intro
      -- We have shown the premise of h13, we can now drive its conclusion.
      let h15 := h13 h14
      -- False on the left can always be used.
      apply False.elim h15
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- One of the premise coincides with the conclusion.
      exact h11
  case inr h16 =>
    -- Conjunctions on the left can always be decomposed.
    let h17 := h16.left
    let h18 := h16.right
    -- Disjunctions on the left can always be decomposed.
    cases h17
    case inl h19 =>
      -- False on the left can always be used.
      apply False.elim h19
    case inr h20 =>
      -- Disjunctions on the left can always be decomposed.
      cases h1
      case inl h21 =>
        -- Conjunctions on the left can always be decomposed.
        let h22 := h21.left
        let h23 := h21.right
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- One of the premise coincides with the conclusion.
        exact h18
      case inr h24 =>
        -- Conjunctions on the left can always be decomposed.
        let h25 := h24.left
        let h26 := h24.right
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- One of the premise coincides with the conclusion.
        exact h18



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_19169267658222273310503138305 : ((((p2 → True) → (p2 ∧ ((p1 ∧ (((p2 ∧ (p1 → p4)) ∨ (p1 ∧ p1)) ∨ p5)) ∧ False))) → (p5 ∧ ((True → (p5 ∧ False)) ∨ p2))) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h2 : (p2 → True) := by
    -- Implications on the right can always be decomposed.
    intro h3
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h4 := h1 h2
  -- We need to get the right conjuct of h4 based on <expert-advice>.
  let h5 := h4.right
  -- We need to get the right conjuct of h5 based on <expert-advice>.
  let h6 := h5.right
  -- False on the left can always be used.
  apply False.elim h6
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h7 : (p2 → True) := by
    -- Implications on the right can always be decomposed.
    intro h8
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h9 := h1 h7
  -- We need to get the right conjuct of h9 based on <expert-advice>.
  let h10 := h9.right
  -- We need to get the right conjuct of h10 based on <expert-advice>.
  let h11 := h10.right
  -- False on the left can always be used.
  apply False.elim h11
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_135649275027897947682672405539 : ((((False ∧ (((p1 ∧ p2) ∨ (True ∧ p4)) → p5)) → ((p2 → (p2 ∧ True)) ∨ True)) → (p5 ∨ (p5 ∧ (False ∨ p2)))) ∨ (p2 → (True ∨ p5))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_654245271569500550709312650590 : ((((((True ∨ ((((p1 → False) ∧ p5) → (p2 → (p4 ∨ False))) ∧ (p4 ∧ (p3 ∨ ((p4 → p1) → True))))) → p2) ∨ p5) ∨ (p3 ∨ p3)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_202227248993463744305941109024 : (((p2 ∧ (p4 ∧ (False ∧ False))) → True) ∧ ((p4 → p3) → (((p5 ∧ (p2 ∨ ((True ∧ p2) → False))) ∨ (p5 ∨ p2)) ∨ (False → (p5 ∨ p5))))) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro
  -- Implications on the right can always be decomposed.
  intro h2
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h3
  -- False on the left can always be used.
  apply False.elim h3



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_175931936899279103122524774535 : (((p1 ∧ (p3 ∨ ((((True → False) ∧ True) → True) ∨ (p4 ∨ p1)))) ∨ True) ∧ (((p4 → ((True → p3) → p1)) → (p5 ∨ p1)) ∨ (False → p5))) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_116564809362092171854309577359 : (((p2 ∨ p2) ∧ (((p4 ∨ p4) ∧ (p4 ∨ p5)) ∨ (((p4 ∨ p2) ∨ (False ∧ p3)) → ((True ∨ ((True ∧ p5) → p4)) ∧ p3)))) ∨ (False → p2)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_691965581836455694681251932734 : ((((p4 → (p2 → (p3 ∧ (True ∧ (((p3 ∧ p2) ∧ False) ∨ (p3 ∧ (p4 → False))))))) → ((((p1 ∧ p1) → p3) ∨ (p4 ∧ p3)) ∨ True)) ∨ p5) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_204933605883966166629357301310 : ((((p2 ∧ p1) → (p1 → p5)) → False) ∨ ((True ∧ (False ∨ ((p1 ∨ (True ∨ p2)) ∧ False))) → (False → (p2 → ((p3 ∧ p2) ∧ (p1 → True)))))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
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
  -- False on the left can always be used.
  apply False.elim h2
  -- False on the left can always be used.
  apply False.elim h2
  -- Implications on the right can always be decomposed.
  intro h4
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_147039665440914194195157066815 : (((((p5 ∧ p1) ∧ ((((False ∨ p4) ∨ False) ∨ p2) ∧ (p5 ∧ True))) ∧ ((p2 ∧ p1) → (False ∧ p4))) ∧ p3) ∨ ((p5 → p5) ∨ (False → False))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_37994550536318168265455021662 : (((((((p5 → p2) ∧ False) → p2) → ((p4 ∨ True) ∧ (p4 → ((((p3 → True) ∧ p3) ∨ p3) ∧ (p1 ∨ p2))))) ∨ (p2 → True)) ∧ p3) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_64918433869210171593621790176 : ((p2 ∨ ((((p2 ∨ p5) ∧ ((p1 ∨ ((p1 ∧ p1) ∧ False)) ∧ ((p5 ∧ p1) ∨ True))) ∨ p2) ∨ (((p3 ∨ (p4 ∧ p4)) → False) → p5))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_389149966281824309758176792805 : (((((((p3 ∧ (((p1 → p3) → (p3 ∨ p2)) ∨ p4)) → False) → (p2 → p3)) ∧ ((((True ∨ p1) ∨ p4) → p3) → (False → p5))) ∨ True) ∧ True) ∧ True) := by
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
theorem thm_5_vars_475683446000388031985298278447 : ((((((((p2 ∨ p5) → p2) → (p5 → True)) → False) ∧ p3) ∨ (((p3 ∨ (p5 → ((p4 ∨ True) ∨ p4))) ∧ True) ∧ ((p4 ∨ p4) → p4))) ∧ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
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
  -- Implications on the right can always be decomposed.
  intro h2
  -- Disjunctions on the left can always be decomposed.
  cases h2
  case inl h3 =>
    -- One of the premise coincides with the conclusion.
    exact h3
  case inr h4 =>
    -- One of the premise coincides with the conclusion.
    exact h4
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_730256841510608854725671525683 : (((((p2 → p3) → True) → ((p4 ∨ ((p2 ∨ False) → True)) → (p2 ∨ (((p1 ∨ (p5 → p1)) ∧ ((p2 ∨ True) → p4)) → (p3 → p2))))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_111279589470131924577895315806 : ((((p2 ∨ True) → ((p4 ∨ (((False ∨ True) ∨ p3) ∨ ((((((p1 ∧ p5) ∨ p1) → False) ∨ p5) ∧ p5) ∨ p4))) ∧ p4)) ∧ True) ∨ (p5 → p5)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_217765860004164927191348736571 : (((p5 ∧ (p4 ∧ p5)) → p5) → ((((False ∨ (((True → False) ∨ False) ∨ (p1 ∨ (False → p5)))) ∨ p5) → p5) ∨ ((p4 ∨ False) → (p4 ∨ p5)))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h2
  -- Disjunctions on the left can always be decomposed.
  cases h2
  case inl h3 =>
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- One of the premise coincides with the conclusion.
    exact h3
  case inr h4 =>
    -- False on the left can always be used.
    apply False.elim h4



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_116546423047593648378060930627 : (((False ∨ p4) ∧ (p5 ∨ (((p3 → (p1 ∧ ((p2 → p3) → False))) ∧ (((p4 → (False → (p4 ∧ p5))) ∨ p2) ∧ p1)) ∨ p4))) ∨ (p5 → p5)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_57743972397946736531846527085 : ((((True → False) → p4) → ((p4 → (True ∧ (p4 ∧ p2))) ∨ (((p5 ∨ (((p5 → p3) ∧ p2) ∨ True)) ∨ (p4 ∨ p5)) ∧ (True ∨ p3)))) ∨ p4) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
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
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_637913650940548360345190930175 : (((((p2 ∧ ((p3 → (p2 → (p1 ∧ p2))) ∨ True)) ∧ ((((False ∧ p5) ∨ p1) ∨ ((p2 ∧ p1) ∧ (False → (p4 ∨ p1)))) → False)) → p1) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_198666729365503112381134824476 : ((p4 ∨ ((p1 ∨ ((p3 ∨ p3) → False)) ∧ False)) ∨ ((p5 → (((p1 ∧ True) ∨ ((((True ∨ (True ∨ p3)) ∨ p3) ∨ True) → p2)) ∧ p3)) → True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_347224714100850403906381290709 : (p3 → ((((False → (p2 ∧ (p1 → p2))) → False) ∧ ((False ∧ False) → False)) → ((False ∨ p5) ∧ (p1 → ((True ∨ ((p2 → p1) ∧ p5)) → p4))))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Conjunctions on the left can always be decomposed.
  let h3 := h2.left
  let h4 := h2.right
  -- We want to use the implication h3 based on <expert-advice>. So we show its premise.
  have h5 : (False → (p2 ∧ (p1 → p2))) := by
    -- Implications on the right can always be decomposed.
    intro h6
    -- Conjunctions on the right can always be decomposed.
    apply And.intro
    -- False on the left can always be used.
    apply False.elim h6
    -- Implications on the right can always be decomposed.
    intro h7
    -- False on the left can always be used.
    apply False.elim h6
  -- We have shown the premise of h3, we can now drive its conclusion.
  let h8 := h3 h5
  -- False on the left can always be used.
  apply False.elim h8
  -- Implications on the right can always be decomposed.
  intro h9
  -- Implications on the right can always be decomposed.
  intro h10
  -- Disjunctions on the left can always be decomposed.
  cases h10
  case inl h11 =>
    -- Conjunctions on the left can always be decomposed.
    let h12 := h2.left
    let h13 := h2.right
    -- We want to use the implication h12 based on <expert-advice>. So we show its premise.
    have h14 : (False → (p2 ∧ (p1 → p2))) := by
      -- Implications on the right can always be decomposed.
      intro h15
      -- Conjunctions on the right can always be decomposed.
      apply And.intro
      -- False on the left can always be used.
      apply False.elim h15
      -- Implications on the right can always be decomposed.
      intro h16
      -- False on the left can always be used.
      apply False.elim h15
    -- We have shown the premise of h12, we can now drive its conclusion.
    let h17 := h12 h14
    -- False on the left can always be used.
    apply False.elim h17
  case inr h18 =>
    -- Conjunctions on the left can always be decomposed.
    let h19 := h18.left
    let h20 := h18.right
    -- Conjunctions on the left can always be decomposed.
    let h21 := h2.left
    let h22 := h2.right
    -- We want to use the implication h21 based on <expert-advice>. So we show its premise.
    have h23 : (False → (p2 ∧ (p1 → p2))) := by
      -- Implications on the right can always be decomposed.
      intro h24
      -- Conjunctions on the right can always be decomposed.
      apply And.intro
      -- False on the left can always be used.
      apply False.elim h24
      -- Implications on the right can always be decomposed.
      intro h25
      -- False on the left can always be used.
      apply False.elim h24
    -- We have shown the premise of h21, we can now drive its conclusion.
    let h26 := h21 h23
    -- False on the left can always be used.
    apply False.elim h26



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_1865531664178568063563168039 : (((True ∧ p3) ∧ (((p2 ∧ True) ∧ ((((p2 ∨ p5) ∧ p2) ∧ (p5 ∨ False)) ∧ (p5 ∨ True))) ∧ (True ∨ True))) → (False ∨ (p3 ∨ False))) := by
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
  -- Conjunctions on the left can always be decomposed.
  let h8 := h6.left
  let h9 := h6.right
  -- Conjunctions on the left can always be decomposed.
  let h10 := h8.left
  let h11 := h8.right
  -- Conjunctions on the left can always be decomposed.
  let h12 := h9.left
  let h13 := h9.right
  -- Conjunctions on the left can always be decomposed.
  let h14 := h12.left
  let h15 := h12.right
  -- Conjunctions on the left can always be decomposed.
  let h16 := h14.left
  let h17 := h14.right
  -- Disjunctions on the left can always be decomposed.
  cases h16
  case inl h18 =>
    -- Disjunctions on the left can always be decomposed.
    cases h15
    case inl h19 =>
      -- Disjunctions on the left can always be decomposed.
      cases h13
      case inl h20 =>
        -- Disjunctions on the left can always be decomposed.
        cases h7
        case inl h21 =>
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- Show the left disjunct based on <expert-advice>.
          apply Or.inl
          -- One of the premise coincides with the conclusion.
          exact h5
        case inr h22 =>
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- Show the left disjunct based on <expert-advice>.
          apply Or.inl
          -- One of the premise coincides with the conclusion.
          exact h5
      case inr h23 =>
        -- Disjunctions on the left can always be decomposed.
        cases h7
        case inl h24 =>
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- Show the left disjunct based on <expert-advice>.
          apply Or.inl
          -- One of the premise coincides with the conclusion.
          exact h5
        case inr h25 =>
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- Show the left disjunct based on <expert-advice>.
          apply Or.inl
          -- One of the premise coincides with the conclusion.
          exact h5
    case inr h26 =>
      -- False on the left can always be used.
      apply False.elim h26
  case inr h27 =>
    -- Disjunctions on the left can always be decomposed.
    cases h15
    case inl h28 =>
      -- Disjunctions on the left can always be decomposed.
      cases h13
      case inl h29 =>
        -- Disjunctions on the left can always be decomposed.
        cases h7
        case inl h30 =>
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- Show the left disjunct based on <expert-advice>.
          apply Or.inl
          -- One of the premise coincides with the conclusion.
          exact h5
        case inr h31 =>
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- Show the left disjunct based on <expert-advice>.
          apply Or.inl
          -- One of the premise coincides with the conclusion.
          exact h5
      case inr h32 =>
        -- Disjunctions on the left can always be decomposed.
        cases h7
        case inl h33 =>
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- Show the left disjunct based on <expert-advice>.
          apply Or.inl
          -- One of the premise coincides with the conclusion.
          exact h5
        case inr h34 =>
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- Show the left disjunct based on <expert-advice>.
          apply Or.inl
          -- One of the premise coincides with the conclusion.
          exact h5
    case inr h35 =>
      -- False on the left can always be used.
      apply False.elim h35



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_598604528186453516048580873019 : (((((p5 ∧ (p5 ∨ p2)) → (((True ∧ (((p1 → ((p3 ∨ ((True ∨ (False ∨ p1)) ∨ False)) ∧ p3)) ∧ p1) ∨ p5)) → p2) ∧ p4)) ∧ p4) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_228651494168583477284053310655 : ((p2 ∨ (p2 ∧ p3)) ∨ ((((p4 ∨ (p4 ∧ ((True ∧ p2) ∨ p2))) → (((p3 ∨ p1) → p2) ∨ (p5 ∨ True))) → (False ∨ (p3 ∧ p3))) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_114196270370438025076554792916 : ((((False → (False → ((p2 → True) → (p5 → True)))) ∧ (p2 ∨ ((p2 ∨ True) ∧ (False ∨ (p4 ∧ p2))))) → (p5 → (p2 → p1))) ∨ (p4 ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_113970584647849081294239594070 : (((p3 ∧ (((((p2 → ((p2 ∨ (p3 ∧ True)) ∧ (p2 ∨ False))) ∨ p4) ∧ (p4 ∧ p1)) → False) ∧ p2)) ∧ ((p3 → False) → p4)) ∨ (p4 ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_315312799511586185646967714564 : (p3 ∨ ((p4 ∨ (p5 ∧ (p3 ∧ p3))) → ((((((((p1 ∨ p3) ∧ ((p2 → False) → True)) → True) → p2) ∨ (p1 → p1)) ∨ True) → p4) ∨ p3))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h2 =>
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Implications on the right can always be decomposed.
    intro h3
    -- Disjunctions on the left can always be decomposed.
    cases h3
    case inl h4 =>
      -- Disjunctions on the left can always be decomposed.
      cases h4
      case inl h5 =>
        -- One of the premise coincides with the conclusion.
        exact h2
      case inr h6 =>
        -- One of the premise coincides with the conclusion.
        exact h2
    case inr h7 =>
      -- One of the premise coincides with the conclusion.
      exact h2
  case inr h8 =>
    -- Conjunctions on the left can always be decomposed.
    let h9 := h8.left
    let h10 := h8.right
    -- Conjunctions on the left can always be decomposed.
    let h11 := h10.left
    let h12 := h10.right
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h12



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_2192295652393289034749124995 : ((((True ∧ p4) ∨ (p5 ∧ p4)) → (((False ∧ (p4 ∧ (p3 ∧ True))) ∨ p3) ∨ p3)) ∨ (p5 → ((p1 ∨ (p3 → (True ∧ p3))) ∨ p5))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_68604032735662162719277260474 : ((p4 → ((((False ∨ (((((True ∧ p4) ∧ (p5 ∨ True)) ∨ (False ∨ ((p4 ∨ p1) → p3))) → p1) → (False ∧ p5))) ∧ True) → p3) ∨ True)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_327828249767573587656990860704 : (True → (((((p3 ∧ (p3 → (p3 ∨ (((p4 → False) → (p5 ∨ p3)) → True)))) ∨ p3) → (p3 ∨ (p5 ∧ p5))) → (True ∧ p3)) ∨ (p4 ∨ True))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_666831195448398743520906827063 : ((((((p5 → True) → ((p4 ∨ (True ∨ p1)) → False)) → (((((p3 ∨ (p5 ∧ True)) → p2) → False) ∨ p4) ∧ p1)) ∧ (p5 ∧ (p4 ∧ p4))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_200751933395108158850882186035 : ((p3 ∧ (True → (((p3 ∧ False) → p4) ∧ True))) → ((p3 ∧ (p1 ∧ (p2 ∨ p3))) ∨ ((((p2 ∨ False) → (p5 → p1)) ∧ p5) → (p4 ∨ True)))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h4
  -- Conjunctions on the left can always be decomposed.
  let h5 := h4.left
  let h6 := h4.right
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_55015427757476958103806473979 : (((True ∧ ((p5 → (True ∨ p1)) → p4)) ∧ (False ∧ (((p1 ∨ (p3 ∧ ((p4 ∧ (p4 ∨ p5)) ∨ p3))) ∧ (p3 ∨ (p2 ∨ p3))) → p2))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_342771217113359341742031430221 : (p2 → ((p1 → (((p5 → p4) ∧ (p4 ∨ True)) ∧ p4)) ∨ ((False ∧ ((p5 ∨ p4) ∨ (p2 ∨ True))) ∨ (p2 ∧ (((p5 ∨ p3) ∧ p5) ∨ p2))))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- One of the premise coincides with the conclusion.
  exact h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_111327897471642297966598835358 : (((p2 ∧ ((((False → (p5 ∧ ((p5 ∧ p5) ∨ p3))) → (p2 ∨ p4)) ∧ (p1 → (p4 ∧ (p1 ∧ p1)))) → (p3 ∨ False))) ∧ p3) ∨ (True → True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_41388862796382707151306621430 : (((((p1 → ((False → (p5 ∧ p2)) → (p4 ∨ p2))) ∧ (p1 ∨ (p4 → p2))) ∧ (p4 → ((False → (p1 ∧ p2)) → (p5 ∨ p1)))) ∨ True) ∨ p2) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_63340435899084388678759526051 : ((p5 ∧ (True ∧ ((p2 ∧ (p2 ∧ (False ∧ (((True → p3) ∨ p3) ∧ p1)))) ∧ (((True ∧ (True ∨ True)) ∨ ((False ∨ p3) → True)) ∨ False)))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_654159459912682867311211862070 : (((((((((p1 ∨ ((p1 → p1) ∧ ((p5 → p2) → (p3 → p5)))) ∨ (p2 ∨ False)) → (p5 ∧ True)) ∨ p5) ∨ True) ∨ p1) ∨ (p4 ∧ p5)) ∨ p2) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
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
theorem thm_5_vars_148565205563906637792319403776 : ((((p5 → p4) → (((p4 ∧ p3) ∨ p3) ∨ (p1 ∧ False))) ∧ ((p5 ∧ (((p2 ∨ p3) ∨ True) → False)) ∨ p5)) ∨ ((p4 ∧ (p1 ∧ False)) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_58111529014106643966620118914 : (((p1 ∧ p4) ∧ (p4 ∧ (p3 → (p2 → ((((True ∧ True) ∨ True) → (True → (True ∧ (((p4 → p1) → False) ∧ p3)))) ∧ (False ∨ p4)))))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_139444423696615288040454405255 : ((((((p5 → ((((p2 ∨ (False ∧ (p2 ∧ p1))) ∨ p2) ∨ (p5 ∨ p2)) ∨ p4)) ∧ (p2 ∧ p2)) ∨ True) ∨ p1) → p2) → (p2 ∨ (p2 ∨ p3))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h2 : ((((p5 → ((((p2 ∨ (False ∧ (p2 ∧ p1))) ∨ p2) ∨ (p5 ∨ p2)) ∨ p4)) ∧ (p2 ∧ p2)) ∨ True) ∨ p1) := by
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h3 := h1 h2
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- One of the premise coincides with the conclusion.
  exact h3



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_14899404277226902075662568003 : ((((((p4 → p2) ∧ True) ∨ (True ∧ True)) → ((True → ((p5 ∨ (False ∨ (p1 ∨ True))) ∨ (p1 ∧ p3))) ∨ (False ∨ p1))) ∨ (p3 → p2)) ∧ True) := by
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
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Implications on the right can always be decomposed.
    intro h5
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
  case inr h6 =>
    -- Conjunctions on the left can always be decomposed.
    let h7 := h6.left
    let h8 := h6.right
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Implications on the right can always be decomposed.
    intro h9
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
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_40082133836962570638173222653 : (((((((((p1 ∧ p3) ∧ p1) → True) ∧ (p5 → ((False ∨ p3) ∨ ((p1 ∧ False) ∨ (p5 ∨ False))))) → (p1 ∧ False)) → False) ∧ True) ∨ False) ∨ p3) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h1
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h2 : ((((p1 ∧ p3) ∧ p1) → True) ∧ (p5 → ((False ∨ p3) ∨ ((p1 ∧ False) ∨ (p5 ∨ False))))) := by
    -- Conjunctions on the right can always be decomposed.
    apply And.intro
    -- Implications on the right can always be decomposed.
    intro h3
    -- True on the right can always be proven directly.
    apply True.intro
    -- Implications on the right can always be decomposed.
    intro h4
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- One of the premise coincides with the conclusion.
    exact h4
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h5 := h1 h2
  -- We need to get the right conjuct of h5 based on <expert-advice>.
  let h6 := h5.right
  -- False on the left can always be used.
  apply False.elim h6
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_319409010812131430200919129928 : (p4 ∨ ((p4 ∧ ((True ∧ ((p5 ∧ (p2 ∧ (p4 ∨ (p4 ∨ p1)))) → p1)) ∧ p4)) → (((True ∨ ((False ∨ (p1 → p5)) ∧ p2)) → p3) ∨ True))) := by
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
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_116992763845380188510357642182 : (((True ∨ p1) → (((p1 ∧ ((p5 ∨ (((False ∨ True) ∧ p5) → True)) → ((p3 ∨ p4) ∨ p2))) ∧ p2) ∨ (p4 → (p5 → p4)))) ∨ (False → p5)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_340804390426949311570007310433 : (p2 → (((p1 → (False ∧ (p1 ∨ (((((p2 ∨ (((p4 ∧ p2) ∨ p4) → ((False ∨ False) ∨ p5))) ∨ p5) ∧ p5) ∧ p1) → True)))) → p3) ∨ p2)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_50781457014927341954666006655 : (((p3 ∨ ((p4 → True) → (p1 ∨ (p2 ∧ (p3 ∨ (((p4 ∨ True) ∧ p5) → (True ∧ (True ∧ False)))))))) → (((p1 → p5) → p3) → p2)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_209349518126084329725228195899 : ((False → (p5 ∧ (p3 ∧ (p1 → p4)))) → ((((p1 ∨ p4) → ((p4 → (False ∨ p1)) ∨ p2)) ∧ (p5 ∧ False)) ∨ (p4 → (p1 ∨ (p4 ∨ p3))))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h2
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- One of the premise coincides with the conclusion.
  exact h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_248671880897384401942682144401 : ((p3 ∨ p1) ∨ (p1 → (((p4 ∧ p2) ∧ ((p3 ∨ p2) ∧ (p3 ∧ p3))) ∨ ((p5 ∧ ((p5 → (True → (p1 ∧ p1))) → (p3 ∨ False))) → p5)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h2
  -- Conjunctions on the left can always be decomposed.
  let h3 := h2.left
  let h4 := h2.right
  -- One of the premise coincides with the conclusion.
  exact h3



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_153478577707652041285469896423 : ((p5 ∨ ((True ∨ (((False ∧ p2) ∨ (((p3 ∨ p1) ∧ p5) → (p5 ∧ ((p5 ∨ p5) ∨ p3)))) → True)) ∨ False)) → (p2 → (p3 ∨ (p1 ∨ p2)))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h3 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h2
  case inr h4 =>
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
        -- One of the premise coincides with the conclusion.
        exact h2
      case inr h7 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- One of the premise coincides with the conclusion.
        exact h2
    case inr h8 =>
      -- False on the left can always be used.
      apply False.elim h8



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_135380759079269162833112191029 : ((((((False ∧ p2) → (p1 ∧ (((p1 ∨ (p5 → (p4 → p5))) ∧ p2) → True))) ∧ p4) → p3) ∨ ((p5 ∨ p1) ∨ False)) ∨ (True ∨ (True → p2))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_779573502427624141133241766967 : (((p2 ∨ ((p4 ∧ ((p3 ∧ ((((p3 → p3) ∧ ((((p4 ∨ (p5 ∧ False)) → (p2 → p5)) ∨ p5) ∧ False)) → p3) → p3)) ∧ p1)) ∨ True)) ∨ p5) ∧ True) := by
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
theorem thm_5_vars_190157216900501836642220220210 : (((True ∧ (((p1 ∧ (False → p1)) ∨ False) ∧ p5)) ∧ p5) ∨ (p4 → (p3 ∨ (((p1 ∧ False) ∧ (p2 ∨ (p3 → p4))) → ((p5 ∨ True) → False))))) := by
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
  -- Disjunctions on the left can always be decomposed.
  cases h3
  case inl h4 =>
    -- Conjunctions on the left can always be decomposed.
    let h5 := h2.left
    let h6 := h2.right
    -- Conjunctions on the left can always be decomposed.
    let h7 := h5.left
    let h8 := h5.right
    -- False on the left can always be used.
    apply False.elim h8
  case inr h9 =>
    -- Conjunctions on the left can always be decomposed.
    let h10 := h2.left
    let h11 := h2.right
    -- Conjunctions on the left can always be decomposed.
    let h12 := h10.left
    let h13 := h10.right
    -- False on the left can always be used.
    apply False.elim h13



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_487301691266331183455209942897 : (((((((p1 ∧ False) → p3) → p2) ∨ p3) → ((((p5 ∧ (((p3 ∧ (p4 → p5)) ∧ (p2 ∧ False)) → False)) → (p4 ∨ p2)) ∨ p3) ∨ p4)) ∧ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
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
    -- Conjunctions on the left can always be decomposed.
    let h4 := h3.left
    let h5 := h3.right
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
    have h6 : ((p1 ∧ False) → p3) := by
      -- Implications on the right can always be decomposed.
      intro h7
      -- Conjunctions on the left can always be decomposed.
      let h8 := h7.left
      let h9 := h7.right
      -- False on the left can always be used.
      apply False.elim h9
    -- We have shown the premise of h2, we can now drive its conclusion.
    let h10 := h2 h6
    -- One of the premise coincides with the conclusion.
    exact h10
  case inr h11 =>
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h11
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_330356621177459061961296562685 : (True → (p2 ∨ (((p2 ∧ (((p4 ∧ (False ∧ (((False ∨ p2) → (p4 ∨ p2)) ∧ p2))) ∨ p2) → (False ∨ (p5 ∧ False)))) ∧ (p2 ∨ True)) ∨ True))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_671515013946480903830588419119 : ((((p3 → ((p2 → p3) → (((p1 ∧ ((((p4 → False) ∨ ((True ∧ p5) ∨ p1)) ∨ p2) ∧ p3)) ∨ p2) ∧ p5))) ∨ (False → (p5 → p5))) ∨ p2) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
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
theorem thm_5_vars_319388082393112598591793626489 : (p4 ∨ (((p2 ∧ (p4 ∨ (p4 ∧ (p1 ∨ ((p3 ∧ (p5 → p3)) ∧ p2))))) ∧ p2) → (((((p2 → (False ∧ False)) ∧ False) ∨ p1) ∨ p4) ∧ True))) := by
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
  -- Disjunctions on the left can always be decomposed.
  cases h5
  case inl h6 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h6
  case inr h7 =>
    -- Conjunctions on the left can always be decomposed.
    let h8 := h7.left
    let h9 := h7.right
    -- Disjunctions on the left can always be decomposed.
    cases h9
    case inl h10 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- One of the premise coincides with the conclusion.
      exact h8
    case inr h11 =>
      -- Conjunctions on the left can always be decomposed.
      let h12 := h11.left
      let h13 := h11.right
      -- Conjunctions on the left can always be decomposed.
      let h14 := h12.left
      let h15 := h12.right
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- One of the premise coincides with the conclusion.
      exact h8
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_158471767761034418102321567231 : (((p4 → False) ∨ (p5 ∨ ((p1 ∧ ((((False → (False → p4)) ∨ p2) → False) ∨ p5)) ∧ (p1 ∨ p4)))) ∨ (((False ∨ (True ∧ p5)) ∧ p3) → True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_67339191048521245908798874646 : ((p1 → ((((False ∧ (p4 ∧ p1)) ∨ ((((False ∨ p5) ∨ False) ∧ p1) → (True → p1))) → (p4 → ((p3 ∧ p3) ∧ (p3 → p1)))) ∨ True)) ∨ p4) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_615989987789085406952387426648 : ((((((((p3 ∧ (p3 ∨ p2)) ∧ ((True ∧ p5) ∧ p4)) ∧ p3) → (False ∧ True)) → (p5 ∧ ((p3 ∧ (p2 ∨ (p1 ∨ False))) ∨ p5))) ∨ True) ∨ p2) ∧ True) := by
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
theorem thm_5_vars_8049352098002609503599616553 : ((((((p5 ∧ p5) → (p5 → (((p2 → ((p2 ∨ p1) ∨ p2)) ∨ (p1 ∧ p1)) → p5))) ∧ (((p2 ∧ False) ∨ p5) ∧ p1)) ∨ False) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_116556713641501212667739039150 : (((p1 ∨ p4) ∧ ((p2 ∧ ((p3 → p4) ∧ ((False ∧ p4) ∧ (p2 ∨ ((p1 ∧ p4) → True))))) ∨ (((False → False) → p1) → p1))) ∨ (True ∨ p2)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_650459609114073860533345707899 : (((((p4 → (((p1 ∧ True) ∧ p4) ∨ (p4 ∨ ((p4 ∨ (p1 → p5)) ∨ True)))) → (((p1 → p4) → (p3 ∨ False)) → p3)) ∧ (False ∨ p1)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_177688085932260647956906076370 : (((((True ∧ (p5 → (p3 → (p2 ∨ p4)))) ∧ p3) ∧ (p5 ∧ p1)) ∧ p5) ∨ ((p5 → (p3 → False)) → (p4 ∨ ((False ∨ (p3 ∧ p5)) → False)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h2
  -- Disjunctions on the left can always be decomposed.
  cases h2
  case inl h3 =>
    -- False on the left can always be used.
    apply False.elim h3
  case inr h4 =>
    -- Conjunctions on the left can always be decomposed.
    let h5 := h4.left
    let h6 := h4.right
    -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
    have h7 : p5 := by
      -- One of the premise coincides with the conclusion.
      exact h6
    -- We have shown the premise of h1, we can now drive its conclusion.
    let h8 := h1 h7
    -- We want to use the implication h8 based on <expert-advice>. So we show its premise.
    have h9 : p3 := by
      -- One of the premise coincides with the conclusion.
      exact h5
    -- We have shown the premise of h8, we can now drive its conclusion.
    let h10 := h8 h9
    -- False on the left can always be used.
    apply False.elim h10



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_303980291359004669989888045794 : (p1 ∨ (((p3 ∧ True) ∧ (p3 → ((((p4 ∧ (((((False ∨ p4) ∧ False) → p5) ∧ (p4 ∨ (p3 → True))) ∧ p4)) ∧ p3) ∨ p4) ∨ p5))) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_4146848122701841846130244893 : (p4 ∨ ((((False → False) → (p2 ∧ p4)) ∧ (p3 ∨ ((True ∨ (True ∧ p5)) ∧ ((((False ∨ True) ∨ p3) ∨ False) → (p4 → p5))))) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_51700010307740984511432265442 : ((((((((p1 ∨ p2) ∨ p2) ∨ p4) ∧ p3) ∧ (True → p2)) ∨ (p4 ∨ (True ∨ True))) ∧ ((p2 → p3) → (p2 ∨ ((p3 ∧ p4) → p3)))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_314651997586059590954125509979 : (p3 ∨ (((p1 → (p1 ∧ ((p2 ∨ ((p2 ∨ p2) → p3)) ∨ True))) → ((p1 ∧ False) ∧ p1)) ∨ ((p2 ∧ p4) ∨ ((True → p3) → (p4 ∨ True))))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
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
theorem thm_5_vars_720204970871159829822471262439 : (((((p5 ∨ (p1 ∨ True)) ∧ p3) → (p5 → (((p1 ∧ p4) ∨ (p5 ∨ False)) ∧ ((False ∨ p5) → ((((p1 ∨ p5) ∨ p1) ∨ p2) ∨ p4))))) ∨ p2) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Conjunctions on the left can always be decomposed.
  let h3 := h1.left
  let h4 := h1.right
  -- Disjunctions on the left can always be decomposed.
  cases h3
  case inl h5 =>
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
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- One of the premise coincides with the conclusion.
      exact h2
    case inr h8 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- One of the premise coincides with the conclusion.
      exact h2
  -- Implications on the right can always be decomposed.
  intro h9
  -- Disjunctions on the left can always be decomposed.
  cases h9
  case inl h10 =>
    -- False on the left can always be used.
    apply False.elim h10
  case inr h11 =>
    -- Conjunctions on the left can always be decomposed.
    let h12 := h1.left
    let h13 := h1.right
    -- Disjunctions on the left can always be decomposed.
    cases h12
    case inl h14 =>
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- One of the premise coincides with the conclusion.
      exact h14
    case inr h15 =>
      -- Disjunctions on the left can always be decomposed.
      cases h15
      case inl h16 =>
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- One of the premise coincides with the conclusion.
        exact h16
      case inr h17 =>
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- One of the premise coincides with the conclusion.
        exact h2
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_994913996301264001779285311 : ((((((p3 → (True → (p3 ∨ (((p2 ∨ ((p4 → p5) ∧ p4)) → ((p4 → True) → False)) ∧ True)))) ∨ False) → p3) ∨ True) → p2) → p2) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h2 : ((((p3 → (True → (p3 ∨ (((p2 ∨ ((p4 → p5) ∧ p4)) → ((p4 → True) → False)) ∧ True)))) ∨ False) → p3) ∨ True) := by
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h3 := h1 h2
  -- One of the premise coincides with the conclusion.
  exact h3



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_136858949946465825556334770088 : (((p5 ∧ p1) ∨ ((p5 ∨ (True → True)) → (p3 ∨ ((((True ∨ (p2 → p2)) → p3) → p1) ∨ (False ∧ (True ∧ True)))))) ∨ ((p3 ∧ p2) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_184878622551483902518204984845 : (((p3 ∧ (p5 ∨ p4)) ∧ (((p2 ∨ p5) ∧ (True → p4)) ∧ p4)) ∨ ((True ∨ p2) ∨ (True → (p5 ∨ (p3 ∨ ((True → p3) ∧ (True ∨ False))))))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_354755271898799741402587402275 : (p5 → ((((((True ∧ p1) ∧ (True → (((p5 ∧ p3) ∧ p3) → True))) → p2) ∨ p3) ∨ ((True → p1) ∨ (p3 ∧ ((p4 ∨ p5) ∧ p1)))) ∨ p5)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_165203161338488819660905756129 : ((((((((((p1 ∧ p2) → p3) ∨ p4) → p1) → False) ∨ p2) ∨ False) → p1) ∨ (False → p5)) ∨ (True ∨ (False ∧ (p4 ∨ ((p3 → True) ∨ p2))))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_337044093602645898628753772353 : (p1 → (((p1 → (((True → (((((p2 ∧ p3) ∨ False) ∧ True) ∧ p5) ∨ p2)) ∨ (p4 ∨ (p4 ∨ (p2 → p1)))) ∨ False)) ∧ p4) ∨ (True ∧ True))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_115021825422017804260347211674 : (((False ∨ ((((p3 ∨ (p5 → p5)) → p1) ∨ True) → (True → False))) ∧ (p5 ∧ ((((p1 ∨ (p2 → p1)) → True) ∨ p2) → p4))) ∨ (p5 → True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_166278387774152377149921719671 : ((p4 ∧ ((p3 ∧ ((p4 ∨ False) ∧ (((True ∧ True) ∧ (p4 ∧ (True ∨ False))) ∨ p5))) ∧ True)) ∨ ((True ∨ ((p2 ∧ True) ∧ p5)) ∨ (p5 ∧ p5))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_52022223428343332626382476473 : (((False ∨ ((((p1 ∧ True) ∨ p2) → (p3 → p1)) ∧ (((p3 ∧ False) ∧ p2) ∨ p4))) ∨ (((p2 ∧ True) → ((p3 → p3) ∧ p2)) → True)) ∨ False) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_1857646868191524120971552509 : (((((p5 ∧ (p3 → p1)) ∨ (p2 ∧ False)) ∧ p3) → (True → (p1 → ((p3 ∨ False) ∧ ((p4 ∨ p2) → True))))) → (p1 ∨ (p1 ∨ True))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_326233142533319131907896946375 : (p5 ∨ (p3 → (((p2 ∨ p1) ∧ (((p1 ∧ (p1 → (False ∨ (False ∧ p5)))) ∧ ((p2 ∨ (p2 ∨ p4)) ∧ True)) ∨ (True → p1))) → (p4 ∨ p3)))) := by
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
    -- Disjunctions on the left can always be decomposed.
    cases h4
    case inl h6 =>
      -- Conjunctions on the left can always be decomposed.
      let h7 := h6.left
      let h8 := h6.right
      -- Conjunctions on the left can always be decomposed.
      let h9 := h7.left
      let h10 := h7.right
      -- Conjunctions on the left can always be decomposed.
      let h11 := h8.left
      let h12 := h8.right
      -- Disjunctions on the left can always be decomposed.
      cases h11
      case inl h13 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- One of the premise coincides with the conclusion.
        exact h1
      case inr h14 =>
        -- Disjunctions on the left can always be decomposed.
        cases h14
        case inl h15 =>
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- One of the premise coincides with the conclusion.
          exact h1
        case inr h16 =>
          -- Show the left disjunct based on <expert-advice>.
          apply Or.inl
          -- One of the premise coincides with the conclusion.
          exact h16
    case inr h17 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- One of the premise coincides with the conclusion.
      exact h1
  case inr h18 =>
    -- Disjunctions on the left can always be decomposed.
    cases h4
    case inl h19 =>
      -- Conjunctions on the left can always be decomposed.
      let h20 := h19.left
      let h21 := h19.right
      -- Conjunctions on the left can always be decomposed.
      let h22 := h20.left
      let h23 := h20.right
      -- Conjunctions on the left can always be decomposed.
      let h24 := h21.left
      let h25 := h21.right
      -- Disjunctions on the left can always be decomposed.
      cases h24
      case inl h26 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- One of the premise coincides with the conclusion.
        exact h1
      case inr h27 =>
        -- Disjunctions on the left can always be decomposed.
        cases h27
        case inl h28 =>
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- One of the premise coincides with the conclusion.
          exact h1
        case inr h29 =>
          -- Show the left disjunct based on <expert-advice>.
          apply Or.inl
          -- One of the premise coincides with the conclusion.
          exact h29
    case inr h30 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- One of the premise coincides with the conclusion.
      exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_57831223091157663424415766665 : (((p4 ∧ (True → True)) → (((((((p2 → (p4 → (p4 ∨ (p5 → p1)))) → True) ∧ p2) ∧ (p5 → p2)) ∨ p5) ∧ p1) ∨ (False → p1))) ∨ p1) := by
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
  -- False on the left can always be used.
  apply False.elim h4



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_230369186028351096416779313669 : (((p3 ∨ False) ∧ True) → ((((True → False) ∧ ((False ∨ ((p1 ∧ (True → (False ∧ p2))) ∧ False)) → p2)) → p1) ∨ ((p1 → p1) ∧ (p4 ∨ p3)))) := by
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
    -- Conjunctions on the right can always be decomposed.
    apply And.intro
    -- Implications on the right can always be decomposed.
    intro h5
    -- One of the premise coincides with the conclusion.
    exact h5
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h4
  case inr h6 =>
    -- False on the left can always be used.
    apply False.elim h6



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_638367598789377748544738827762 : ((((((p2 ∧ p1) ∨ ((p5 ∨ p1) → p4)) ∧ (p1 ∨ (((p4 ∧ p2) ∧ ((((True ∨ p5) ∧ p3) ∨ p2) ∧ p3)) ∨ (p4 → p4)))) → p2) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_51843993397603141674340434478 : (((((p4 ∧ (p3 → (p5 ∨ ((p2 ∨ p5) → p2)))) ∧ ((p1 ∨ p4) → p4)) ∧ True) ∨ ((p1 ∨ (p2 → (False ∨ (p2 ∨ True)))) ∨ p3)) ∨ p3) := by
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
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_701360675187464976307453093803 : (((((((p1 ∧ p1) ∧ p4) ∧ p4) ∨ (True ∨ (p3 → p4))) ∧ (p5 ∧ ((True ∧ ((True ∨ (p2 ∧ True)) → False)) → ((p2 → p5) ∨ p2)))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_777476257212703223899273837602 : (((p1 ∨ (((p5 ∨ (p2 ∧ False)) ∨ (False ∧ ((False → p5) ∨ (p1 ∧ (p2 ∧ p3))))) ∧ ((False ∨ (p1 ∨ False)) ∧ ((True → False) ∨ p1)))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_68865087242781350131517332391 : ((p4 → (True ∧ ((p2 → (p2 → ((((p1 ∧ p2) ∧ ((p4 → p5) ∨ (p4 ∧ False))) → False) → ((p4 → p3) ∧ (p5 ∧ p3))))) ∨ True))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_169036977522109646560613737665 : ((p2 → ((p1 ∨ (((True ∧ p3) ∨ p4) ∨ p3)) → (p2 ∨ ((p3 ∨ (p4 → p5)) → p4)))) → ((False ∨ (False → False)) ∧ ((p1 → False) ∨ True))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h2
  -- False on the left can always be used.
  apply False.elim h2
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_698739315910113669132047457036 : (((((p2 ∧ p1) ∨ (p2 → (p2 ∧ ((True ∧ (p2 ∧ p1)) ∧ p3)))) ∨ (p1 ∧ ((p4 ∧ (p3 ∧ (p1 ∧ (False ∧ p5)))) ∨ (p3 → p1)))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_199824987278407412579596480376 : ((((p2 ∨ False) ∧ (p5 → p5)) ∧ (True → p5)) → (p1 → (((False → (((p3 ∨ p1) ∧ p4) ∨ ((p1 ∨ (p5 ∧ p3)) ∧ p5))) → False) ∨ p1))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Conjunctions on the left can always be decomposed.
  let h3 := h1.left
  let h4 := h1.right
  -- Conjunctions on the left can always be decomposed.
  let h5 := h3.left
  let h6 := h3.right
  -- Disjunctions on the left can always be decomposed.
  cases h5
  case inl h7 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h2
  case inr h8 =>
    -- False on the left can always be used.
    apply False.elim h8



