variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_59368058930858472440531844966 : (((p5 ∨ p4) ∨ ((p2 ∧ (((p1 ∨ (p3 ∨ ((p2 → p3) ∧ p2))) → ((p2 ∨ ((p5 → (p5 → p4)) ∧ p1)) → p3)) ∧ p5)) → p3)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_248576532679661992190788786449 : ((p3 ∨ False) ∨ ((((p3 → (((p5 → True) → ((p3 ∨ False) ∧ (p1 ∨ p4))) ∧ True)) ∧ ((p1 ∨ p4) ∨ p5)) ∧ p3) ∨ (p2 → (p5 → p2)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_747487250659887993500612831576 : ((((True → p1) → ((True ∧ (True → (((False ∧ (p4 → ((p1 ∧ p5) → False))) → (p2 ∨ (p4 ∨ (p1 → False)))) ∨ p4))) → (p3 ∧ True))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_124113808008155675726209716757 : (((((p2 ∧ (True ∨ p3)) ∨ True) ∧ ((p5 → p4) ∧ p1)) ∧ (p3 → (((((p3 ∧ (p1 ∧ p3)) → p1) → p3) ∧ True) ∧ False))) → (p3 → p2)) := by
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
    -- Conjunctions on the left can always be decomposed.
    let h8 := h7.left
    let h9 := h7.right
    -- Disjunctions on the left can always be decomposed.
    cases h9
    case inl h10 =>
      -- Conjunctions on the left can always be decomposed.
      let h11 := h6.left
      let h12 := h6.right
      -- One of the premise coincides with the conclusion.
      exact h8
    case inr h13 =>
      -- Conjunctions on the left can always be decomposed.
      let h14 := h6.left
      let h15 := h6.right
      -- One of the premise coincides with the conclusion.
      exact h8
  case inr h16 =>
    -- Conjunctions on the left can always be decomposed.
    let h17 := h6.left
    let h18 := h6.right
    -- We want to use the implication h4 based on <expert-advice>. So we show its premise.
    have h19 : p3 := by
      -- One of the premise coincides with the conclusion.
      exact h2
    -- We have shown the premise of h4, we can now drive its conclusion.
    let h20 := h4 h19
    -- We need to get the right conjuct of h20 based on <expert-advice>.
    let h21 := h20.right
    -- False on the left can always be used.
    apply False.elim h21



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_163010882248594196553094812471 : ((((True ∧ ((p1 ∧ p5) ∨ (((False ∨ p3) ∨ False) ∨ p5))) ∧ p1) ∨ ((p4 ∧ True) ∨ True)) ∧ (True ∧ ((p2 → True) ∨ (p4 ∨ (p1 ∧ p2))))) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_178663929919120229982440989956 : ((((p4 → p4) ∧ (False ∨ False)) ∧ ((False → True) ∧ (p3 ∧ (p4 ∨ p2)))) ∨ (((p4 ∨ p1) ∨ ((p5 → (True ∨ (p4 ∧ p5))) ∨ False)) ∨ p1)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
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
theorem thm_5_vars_166143117284373764637628493485 : ((True ∧ (True → (((p1 ∧ True) ∨ (p2 ∧ ((p3 ∧ False) → p3))) ∧ (p2 ∨ (p3 ∨ p2))))) ∨ ((p4 → ((p1 ∧ (p2 → p1)) → p4)) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_2127922761917402602982896102 : (((p1 ∧ p2) ∧ (((p2 ∧ (p3 ∨ p2)) ∧ (((False → p2) ∧ p3) ∨ p3)) ∧ (p3 → False))) → ((p3 ∨ p2) → ((p1 ∨ p4) → False))) := by
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
    cases h2
    case inl h5 =>
      -- Conjunctions on the left can always be decomposed.
      let h6 := h1.left
      let h7 := h1.right
      -- Conjunctions on the left can always be decomposed.
      let h8 := h6.left
      let h9 := h6.right
      -- Conjunctions on the left can always be decomposed.
      let h10 := h7.left
      let h11 := h7.right
      -- Conjunctions on the left can always be decomposed.
      let h12 := h10.left
      let h13 := h10.right
      -- Conjunctions on the left can always be decomposed.
      let h14 := h12.left
      let h15 := h12.right
      -- Disjunctions on the left can always be decomposed.
      cases h15
      case inl h16 =>
        -- Disjunctions on the left can always be decomposed.
        cases h13
        case inl h17 =>
          -- Conjunctions on the left can always be decomposed.
          let h18 := h17.left
          let h19 := h17.right
          -- We want to use the implication h11 based on <expert-advice>. So we show its premise.
          have h20 : p3 := by
            -- One of the premise coincides with the conclusion.
            exact h19
          -- We have shown the premise of h11, we can now drive its conclusion.
          let h21 := h11 h20
          -- False on the left can always be used.
          apply False.elim h21
        case inr h22 =>
          -- We want to use the implication h11 based on <expert-advice>. So we show its premise.
          have h23 : p3 := by
            -- One of the premise coincides with the conclusion.
            exact h22
          -- We have shown the premise of h11, we can now drive its conclusion.
          let h24 := h11 h23
          -- False on the left can always be used.
          apply False.elim h24
      case inr h25 =>
        -- Disjunctions on the left can always be decomposed.
        cases h13
        case inl h26 =>
          -- Conjunctions on the left can always be decomposed.
          let h27 := h26.left
          let h28 := h26.right
          -- We want to use the implication h11 based on <expert-advice>. So we show its premise.
          have h29 : p3 := by
            -- One of the premise coincides with the conclusion.
            exact h28
          -- We have shown the premise of h11, we can now drive its conclusion.
          let h30 := h11 h29
          -- False on the left can always be used.
          apply False.elim h30
        case inr h31 =>
          -- We want to use the implication h11 based on <expert-advice>. So we show its premise.
          have h32 : p3 := by
            -- One of the premise coincides with the conclusion.
            exact h31
          -- We have shown the premise of h11, we can now drive its conclusion.
          let h33 := h11 h32
          -- False on the left can always be used.
          apply False.elim h33
    case inr h34 =>
      -- Conjunctions on the left can always be decomposed.
      let h35 := h1.left
      let h36 := h1.right
      -- Conjunctions on the left can always be decomposed.
      let h37 := h35.left
      let h38 := h35.right
      -- Conjunctions on the left can always be decomposed.
      let h39 := h36.left
      let h40 := h36.right
      -- Conjunctions on the left can always be decomposed.
      let h41 := h39.left
      let h42 := h39.right
      -- Conjunctions on the left can always be decomposed.
      let h43 := h41.left
      let h44 := h41.right
      -- Disjunctions on the left can always be decomposed.
      cases h44
      case inl h45 =>
        -- Disjunctions on the left can always be decomposed.
        cases h42
        case inl h46 =>
          -- Conjunctions on the left can always be decomposed.
          let h47 := h46.left
          let h48 := h46.right
          -- We want to use the implication h40 based on <expert-advice>. So we show its premise.
          have h49 : p3 := by
            -- One of the premise coincides with the conclusion.
            exact h48
          -- We have shown the premise of h40, we can now drive its conclusion.
          let h50 := h40 h49
          -- False on the left can always be used.
          apply False.elim h50
        case inr h51 =>
          -- We want to use the implication h40 based on <expert-advice>. So we show its premise.
          have h52 : p3 := by
            -- One of the premise coincides with the conclusion.
            exact h51
          -- We have shown the premise of h40, we can now drive its conclusion.
          let h53 := h40 h52
          -- False on the left can always be used.
          apply False.elim h53
      case inr h54 =>
        -- Disjunctions on the left can always be decomposed.
        cases h42
        case inl h55 =>
          -- Conjunctions on the left can always be decomposed.
          let h56 := h55.left
          let h57 := h55.right
          -- We want to use the implication h40 based on <expert-advice>. So we show its premise.
          have h58 : p3 := by
            -- One of the premise coincides with the conclusion.
            exact h57
          -- We have shown the premise of h40, we can now drive its conclusion.
          let h59 := h40 h58
          -- False on the left can always be used.
          apply False.elim h59
        case inr h60 =>
          -- We want to use the implication h40 based on <expert-advice>. So we show its premise.
          have h61 : p3 := by
            -- One of the premise coincides with the conclusion.
            exact h60
          -- We have shown the premise of h40, we can now drive its conclusion.
          let h62 := h40 h61
          -- False on the left can always be used.
          apply False.elim h62
  case inr h63 =>
    -- Disjunctions on the left can always be decomposed.
    cases h2
    case inl h64 =>
      -- Conjunctions on the left can always be decomposed.
      let h65 := h1.left
      let h66 := h1.right
      -- Conjunctions on the left can always be decomposed.
      let h67 := h65.left
      let h68 := h65.right
      -- Conjunctions on the left can always be decomposed.
      let h69 := h66.left
      let h70 := h66.right
      -- Conjunctions on the left can always be decomposed.
      let h71 := h69.left
      let h72 := h69.right
      -- Conjunctions on the left can always be decomposed.
      let h73 := h71.left
      let h74 := h71.right
      -- Disjunctions on the left can always be decomposed.
      cases h74
      case inl h75 =>
        -- Disjunctions on the left can always be decomposed.
        cases h72
        case inl h76 =>
          -- Conjunctions on the left can always be decomposed.
          let h77 := h76.left
          let h78 := h76.right
          -- We want to use the implication h70 based on <expert-advice>. So we show its premise.
          have h79 : p3 := by
            -- One of the premise coincides with the conclusion.
            exact h78
          -- We have shown the premise of h70, we can now drive its conclusion.
          let h80 := h70 h79
          -- False on the left can always be used.
          apply False.elim h80
        case inr h81 =>
          -- We want to use the implication h70 based on <expert-advice>. So we show its premise.
          have h82 : p3 := by
            -- One of the premise coincides with the conclusion.
            exact h81
          -- We have shown the premise of h70, we can now drive its conclusion.
          let h83 := h70 h82
          -- False on the left can always be used.
          apply False.elim h83
      case inr h84 =>
        -- Disjunctions on the left can always be decomposed.
        cases h72
        case inl h85 =>
          -- Conjunctions on the left can always be decomposed.
          let h86 := h85.left
          let h87 := h85.right
          -- We want to use the implication h70 based on <expert-advice>. So we show its premise.
          have h88 : p3 := by
            -- One of the premise coincides with the conclusion.
            exact h87
          -- We have shown the premise of h70, we can now drive its conclusion.
          let h89 := h70 h88
          -- False on the left can always be used.
          apply False.elim h89
        case inr h90 =>
          -- We want to use the implication h70 based on <expert-advice>. So we show its premise.
          have h91 : p3 := by
            -- One of the premise coincides with the conclusion.
            exact h90
          -- We have shown the premise of h70, we can now drive its conclusion.
          let h92 := h70 h91
          -- False on the left can always be used.
          apply False.elim h92
    case inr h93 =>
      -- Conjunctions on the left can always be decomposed.
      let h94 := h1.left
      let h95 := h1.right
      -- Conjunctions on the left can always be decomposed.
      let h96 := h94.left
      let h97 := h94.right
      -- Conjunctions on the left can always be decomposed.
      let h98 := h95.left
      let h99 := h95.right
      -- Conjunctions on the left can always be decomposed.
      let h100 := h98.left
      let h101 := h98.right
      -- Conjunctions on the left can always be decomposed.
      let h102 := h100.left
      let h103 := h100.right
      -- Disjunctions on the left can always be decomposed.
      cases h103
      case inl h104 =>
        -- Disjunctions on the left can always be decomposed.
        cases h101
        case inl h105 =>
          -- Conjunctions on the left can always be decomposed.
          let h106 := h105.left
          let h107 := h105.right
          -- We want to use the implication h99 based on <expert-advice>. So we show its premise.
          have h108 : p3 := by
            -- One of the premise coincides with the conclusion.
            exact h107
          -- We have shown the premise of h99, we can now drive its conclusion.
          let h109 := h99 h108
          -- False on the left can always be used.
          apply False.elim h109
        case inr h110 =>
          -- We want to use the implication h99 based on <expert-advice>. So we show its premise.
          have h111 : p3 := by
            -- One of the premise coincides with the conclusion.
            exact h110
          -- We have shown the premise of h99, we can now drive its conclusion.
          let h112 := h99 h111
          -- False on the left can always be used.
          apply False.elim h112
      case inr h113 =>
        -- Disjunctions on the left can always be decomposed.
        cases h101
        case inl h114 =>
          -- Conjunctions on the left can always be decomposed.
          let h115 := h114.left
          let h116 := h114.right
          -- We want to use the implication h99 based on <expert-advice>. So we show its premise.
          have h117 : p3 := by
            -- One of the premise coincides with the conclusion.
            exact h116
          -- We have shown the premise of h99, we can now drive its conclusion.
          let h118 := h99 h117
          -- False on the left can always be used.
          apply False.elim h118
        case inr h119 =>
          -- We want to use the implication h99 based on <expert-advice>. So we show its premise.
          have h120 : p3 := by
            -- One of the premise coincides with the conclusion.
            exact h119
          -- We have shown the premise of h99, we can now drive its conclusion.
          let h121 := h99 h120
          -- False on the left can always be used.
          apply False.elim h121



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_218281906244300805281575689867 : (((p3 ∨ True) ∨ (False → p4)) → (p1 ∨ (p5 → (((((p2 → p4) ∨ ((p3 → p1) → p4)) → (p3 → False)) ∨ (p2 → p5)) ∨ (False ∨ True))))) := by
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
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- True on the right can always be proven directly.
      apply True.intro
    case inr h5 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Implications on the right can always be decomposed.
      intro h6
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- True on the right can always be proven directly.
      apply True.intro
  case inr h7 =>
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
theorem thm_5_vars_227267398683704165183493267010 : (((p1 → p1) → p2) ∨ (((((p3 → ((p4 ∧ (True ∧ (p4 ∨ False))) → (p4 → (True ∨ (p3 ∧ p4))))) ∨ p4) ∧ p3) → (p5 ∨ p1)) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_14817230636196763367903438401 : (((((p1 ∨ ((False ∨ p2) ∧ (((p2 ∨ p3) ∨ True) ∨ p2))) ∨ (p4 ∨ p4)) → (((p5 ∨ p4) ∨ (p4 → p4)) ∨ True)) ∨ (p3 ∧ p1)) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
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
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- True on the right can always be proven directly.
      apply True.intro
    case inr h4 =>
      -- Conjunctions on the left can always be decomposed.
      let h5 := h4.left
      let h6 := h4.right
      -- Disjunctions on the left can always be decomposed.
      cases h5
      case inl h7 =>
        -- False on the left can always be used.
        apply False.elim h7
      case inr h8 =>
        -- Disjunctions on the left can always be decomposed.
        cases h6
        case inl h9 =>
          -- Disjunctions on the left can always be decomposed.
          cases h9
          case inl h10 =>
            -- Disjunctions on the left can always be decomposed.
            cases h10
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
          case inr h13 =>
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
    -- Disjunctions on the left can always be decomposed.
    cases h15
    case inl h16 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- True on the right can always be proven directly.
      apply True.intro
    case inr h17 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- True on the right can always be proven directly.
      apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_200368117008905310063691882998 : (((p2 → p4) ∧ ((p4 ∨ (False ∧ p3)) ∨ p1)) → (p1 → ((((p5 → False) ∧ False) ∨ False) ∨ ((p3 → p3) ∨ (p1 ∧ (p1 ∧ (p4 ∨ p4))))))) := by
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
    -- Disjunctions on the left can always be decomposed.
    cases h5
    case inl h6 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- Implications on the right can always be decomposed.
      intro h7
      -- One of the premise coincides with the conclusion.
      exact h7
    case inr h8 =>
      -- Conjunctions on the left can always be decomposed.
      let h9 := h8.left
      let h10 := h8.right
      -- False on the left can always be used.
      apply False.elim h9
  case inr h11 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Implications on the right can always be decomposed.
    intro h12
    -- One of the premise coincides with the conclusion.
    exact h12



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_600759810068989587116935539278 : ((((False ∧ ((((p2 ∧ False) → p5) ∧ p4) ∧ (p1 → (((((p3 → p2) ∨ True) ∧ (p4 ∨ True)) ∨ ((False → True) ∨ p2)) ∨ p2)))) ∧ False) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_690306596854844873854600608987 : ((((p1 → (p4 ∨ ((p3 ∨ (p4 → ((p4 ∨ p1) → p1))) → ((p3 ∧ False) ∧ p3)))) ∨ ((p4 ∧ (p3 ∧ (False ∨ True))) ∧ (p1 ∧ p2))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_382109231144411884699753583332 : (((((((p2 ∧ (((p2 → p2) ∧ p3) ∧ ((p5 ∨ p1) ∨ ((p5 ∨ True) ∧ (p1 → (p2 → p1)))))) ∧ p4) ∨ (p4 → False)) ∨ True) ∨ p3) ∧ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
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
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_345529036339430918979535667030 : (p3 → ((((p4 ∨ False) ∨ ((p4 ∧ p2) ∧ (p4 → (p1 ∨ p5)))) ∨ ((True → ((True ∨ p2) ∧ p2)) → ((True ∧ (False ∨ False)) ∨ p3))) ∨ p5)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h2
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_181030415229237493535779786511 : (((p1 → p5) ∨ (((p5 ∨ p2) → ((p4 → p3) ∨ (p4 → p4))) ∨ p2)) → ((False ∧ (((p3 ∨ p2) ∧ (p2 ∧ p5)) ∨ False)) ∨ (p4 → True))) := by
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
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Implications on the right can always be decomposed.
      intro h6
      -- True on the right can always be proven directly.
      apply True.intro
    case inr h7 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Implications on the right can always be decomposed.
      intro h8
      -- True on the right can always be proven directly.
      apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_337712863087619993422905579490 : (p1 → ((p4 ∧ (True → (((False → ((True → ((p2 → p5) ∨ (p1 ∧ p3))) ∧ p5)) ∨ False) → False))) → (p2 ∨ ((False ∨ p2) ∧ (p2 ∧ p2))))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Conjunctions on the left can always be decomposed.
  let h3 := h2.left
  let h4 := h2.right
  -- We want to use the implication h4 based on <expert-advice>. So we show its premise.
  have h5 : True := by
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h4, we can now drive its conclusion.
  let h6 := h4 h5
  -- We want to use the implication h6 based on <expert-advice>. So we show its premise.
  have h7 : ((False → ((True → ((p2 → p5) ∨ (p1 ∧ p3))) ∧ p5)) ∨ False) := by
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Implications on the right can always be decomposed.
    intro h8
    -- Conjunctions on the right can always be decomposed.
    apply And.intro
    -- Implications on the right can always be decomposed.
    intro h9
    -- False on the left can always be used.
    apply False.elim h8
    -- False on the left can always be used.
    apply False.elim h8
  -- We have shown the premise of h6, we can now drive its conclusion.
  let h10 := h6 h7
  -- False on the left can always be used.
  apply False.elim h10



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_52929432223082451519572033903 : ((((((False ∧ (p4 ∨ False)) ∧ p5) → (p5 ∧ (p3 ∧ p1))) ∧ p2) ∧ (((p1 ∧ p2) ∧ ((p2 → p3) → (p5 ∨ False))) ∨ (p4 ∨ p3))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_169733528706229770406420780350 : (((p4 ∧ (((True → False) ∧ (p1 ∧ p2)) ∧ (((True → False) ∧ p5) → p1))) → p5) ∧ (p3 ∨ ((True ∧ True) ∨ ((False ∧ (False → p4)) ∧ p5)))) := by
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
  -- Conjunctions on the left can always be decomposed.
  let h8 := h7.left
  let h9 := h7.right
  -- We want to use the implication h6 based on <expert-advice>. So we show its premise.
  have h10 : True := by
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h6, we can now drive its conclusion.
  let h11 := h6 h10
  -- False on the left can always be used.
  apply False.elim h11
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_110841856203393494739822312222 : ((((p5 ∨ (((p4 ∧ ((True ∨ False) ∧ (((False ∨ False) ∨ True) ∧ (p1 → (p2 ∨ (p1 → p3)))))) ∨ True) ∧ True)) ∨ p1) ∧ True) ∨ (p4 → p3)) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
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
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_604080371540225752919005808752 : ((((p5 ∨ (((p5 ∨ p3) ∨ p3) ∨ (((((p4 → p5) ∧ p4) ∧ (p1 ∧ ((p4 → p5) ∧ (p2 ∧ (True → p4))))) ∧ p3) → p3))) ∧ p2) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_117555909915887358953688275389 : ((p2 ∧ ((p2 ∧ ((True → p4) → (False ∨ (False ∨ (p4 → p3))))) ∧ (False ∨ ((((p1 ∨ p2) → True) ∨ p4) ∨ (p4 ∧ False))))) ∨ (True ∨ p1)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_148254458722587371401490736439 : ((((p4 → True) → ((p1 → (p3 ∨ (((False → True) ∨ p5) ∧ p4))) → (p1 ∨ p4))) ∨ (p2 ∧ (p4 → p2))) ∨ (True ∧ (p3 → (True ∨ p1)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_2005879687100556988314816282 : ((((p2 → p2) ∧ ((p5 ∧ True) ∧ (False ∨ p1))) ∧ ((p4 ∧ p2) → (p5 → ((p2 → p1) ∧ p3)))) → (((p3 ∨ False) ∧ p3) → p3)) := by
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
    -- Conjunctions on the left can always be decomposed.
    let h6 := h1.left
    let h7 := h1.right
    -- Conjunctions on the left can always be decomposed.
    let h8 := h6.left
    let h9 := h6.right
    -- Conjunctions on the left can always be decomposed.
    let h10 := h9.left
    let h11 := h9.right
    -- Conjunctions on the left can always be decomposed.
    let h12 := h10.left
    let h13 := h10.right
    -- Disjunctions on the left can always be decomposed.
    cases h11
    case inl h14 =>
      -- False on the left can always be used.
      apply False.elim h14
    case inr h15 =>
      -- One of the premise coincides with the conclusion.
      exact h4
  case inr h16 =>
    -- False on the left can always be used.
    apply False.elim h16



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_197954117196392496747474543838 : (((p3 ∧ p1) ∧ (p5 → (p3 ∧ (True → False)))) ∨ ((p3 ∨ (p1 ∨ (((True ∧ p2) ∧ ((True ∨ p4) ∨ p4)) ∨ ((p2 ∧ True) → True)))) ∨ p2)) := by
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
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_139661129314526741643471488904 : ((((False ∧ ((False → p2) → p5)) ∨ (True ∧ ((False ∧ ((True ∧ (True → p5)) → p5)) → (p4 → (p4 ∧ p2))))) → False) → ((p1 → True) → p3)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h3 : ((False ∧ ((False → p2) → p5)) ∨ (True ∧ ((False ∧ ((True ∧ (True → p5)) → p5)) → (p4 → (p4 ∧ p2))))) := by
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Conjunctions on the right can always be decomposed.
    apply And.intro
    -- True on the right can always be proven directly.
    apply True.intro
    -- Implications on the right can always be decomposed.
    intro h4
    -- Implications on the right can always be decomposed.
    intro h5
    -- Conjunctions on the right can always be decomposed.
    apply And.intro
    -- Conjunctions on the left can always be decomposed.
    let h6 := h4.left
    let h7 := h4.right
    -- False on the left can always be used.
    apply False.elim h6
    -- Conjunctions on the left can always be decomposed.
    let h8 := h4.left
    let h9 := h4.right
    -- False on the left can always be used.
    apply False.elim h8
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h10 := h1 h3
  -- False on the left can always be used.
  apply False.elim h10



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_673232283461275526507799793919 : (((((True → (p3 ∧ ((False → True) ∨ ((p3 ∧ p2) ∧ p5)))) → (p3 → ((p3 ∨ ((p5 ∧ p2) → p4)) ∨ True))) → ((p4 ∨ p5) ∨ True)) ∨ p3) ∧ True) := by
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
theorem thm_5_vars_666533419288313641074245086803 : (((((p5 ∨ ((True ∨ ((p1 ∧ p2) → (p1 ∧ False))) ∧ (p4 ∧ (p1 ∧ p5)))) ∨ ((p4 → (p2 → p3)) ∧ p4)) ∧ ((p2 ∧ p2) ∨ p1)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_210271941966415578215099588105 : ((((p1 → True) → True) ∨ p3) ∧ ((((((p5 ∧ True) ∨ p1) ∨ ((p5 ∨ (p3 ∧ p3)) ∧ p2)) ∨ ((p3 ∧ (p4 ∧ p2)) ∧ p3)) ∧ p3) ∨ True)) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_337087455469574561021353537986 : (p1 → (((p1 → ((p4 → ((True ∨ (((p5 ∧ p5) ∨ p4) ∧ p4)) ∧ p5)) → p4)) ∨ (p4 ∧ (True ∧ ((True ∧ p2) → p3)))) ∨ (False ∨ True))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_707834495656506798770362389889 : ((((p1 ∧ (False → ((p5 ∨ p4) → (p2 → p5)))) ∨ ((True ∨ ((((False → p4) ∨ ((p4 → p1) → p4)) → (p1 ∧ p2)) → p2)) → False)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_1880072657327423133849523353 : ((p2 ∨ ((p1 ∨ (False ∨ (p3 ∨ (((p1 ∨ (p5 → p2)) ∧ True) → (p3 ∧ p2))))) ∨ ((p4 ∧ p5) ∨ False))) → ((False ∨ True) ∨ p5)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h2 =>
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro
  case inr h3 =>
    -- Disjunctions on the left can always be decomposed.
    cases h3
    case inl h4 =>
      -- Disjunctions on the left can always be decomposed.
      cases h4
      case inl h5 =>
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- True on the right can always be proven directly.
        apply True.intro
      case inr h6 =>
        -- Disjunctions on the left can always be decomposed.
        cases h6
        case inl h7 =>
          -- False on the left can always be used.
          apply False.elim h7
        case inr h8 =>
          -- Disjunctions on the left can always be decomposed.
          cases h8
          case inl h9 =>
            -- Show the left disjunct based on <expert-advice>.
            apply Or.inl
            -- Show the right disjunct based on <expert-advice>.
            apply Or.inr
            -- True on the right can always be proven directly.
            apply True.intro
          case inr h10 =>
            -- Show the left disjunct based on <expert-advice>.
            apply Or.inl
            -- Show the right disjunct based on <expert-advice>.
            apply Or.inr
            -- True on the right can always be proven directly.
            apply True.intro
    case inr h11 =>
      -- Disjunctions on the left can always be decomposed.
      cases h11
      case inl h12 =>
        -- Conjunctions on the left can always be decomposed.
        let h13 := h12.left
        let h14 := h12.right
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- One of the premise coincides with the conclusion.
        exact h14
      case inr h15 =>
        -- False on the left can always be used.
        apply False.elim h15



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_112310871754543992804625537572 : (((p2 → ((((False ∨ (p3 ∧ True)) ∨ p2) ∧ p4) ∨ (((p4 ∧ p2) ∨ (p4 ∨ (False → True))) ∨ (p2 → (True ∧ p2))))) ∨ True) ∨ (False ∧ False)) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_214888518664487612323635719419 : (((p3 → False) ∨ (p2 ∨ p2)) ∨ (True ∧ (p3 ∨ (((True ∧ p1) ∧ p5) ∨ ((p5 → (False → (False ∨ True))) ∨ (p1 ∧ ((True → p1) ∨ p4))))))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
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
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- False on the left can always be used.
  apply False.elim h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_256026889620349022900977796565 : ((True ∨ p4) → (((((p4 ∨ (p4 → True)) ∧ p5) ∨ p1) → (p4 → (p1 → ((p2 → ((False ∧ (True ∨ (p4 ∨ p5))) ∨ p1)) ∨ p5)))) ∧ True)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h2
  -- Implications on the right can always be decomposed.
  intro h3
  -- Implications on the right can always be decomposed.
  intro h4
  -- Disjunctions on the left can always be decomposed.
  cases h2
  case inl h5 =>
    -- Conjunctions on the left can always be decomposed.
    let h6 := h5.left
    let h7 := h5.right
    -- Disjunctions on the left can always be decomposed.
    cases h6
    case inl h8 =>
      -- Disjunctions on the left can always be decomposed.
      cases h1
      case inl h9 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- One of the premise coincides with the conclusion.
        exact h7
      case inr h10 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- One of the premise coincides with the conclusion.
        exact h7
    case inr h11 =>
      -- Disjunctions on the left can always be decomposed.
      cases h1
      case inl h12 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- One of the premise coincides with the conclusion.
        exact h7
      case inr h13 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- One of the premise coincides with the conclusion.
        exact h7
  case inr h14 =>
    -- Disjunctions on the left can always be decomposed.
    cases h1
    case inl h15 =>
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- Implications on the right can always be decomposed.
      intro h16
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- One of the premise coincides with the conclusion.
      exact h14
    case inr h17 =>
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- Implications on the right can always be decomposed.
      intro h18
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- One of the premise coincides with the conclusion.
      exact h14
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_763832889003128426030421232962 : (((p3 ∧ (p3 ∨ (((p4 → p4) → False) ∨ (True ∨ ((p5 → (((p4 ∨ ((p3 ∧ False) ∨ (p3 ∧ p1))) ∧ p2) ∧ (True → True))) → p5))))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_310649631908413768353359530263 : (p2 ∨ ((p5 → ((False ∨ False) ∧ False)) ∨ (p3 ∨ (((((p2 ∨ p3) ∨ p4) ∨ p5) ∨ (True ∧ (p5 → True))) ∨ (p2 → (p2 → (p4 ∧ p2))))))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
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
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_41047373778172008815351373742 : (((((((p3 → p1) → p4) ∨ p5) → ((p1 ∧ (p4 ∧ (False ∨ ((p5 ∧ p1) → (p1 ∧ False))))) ∨ (p2 → p4))) → (p2 → p4)) ∨ True) ∨ p4) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_199000260846184382089269123272 : ((((((p3 → p2) ∧ p3) ∧ p2) ∧ p2) ∧ p3) → (True → (((p5 → (p3 → (((p3 → (p4 → p5)) → p4) ∨ p4))) ∧ (True → p3)) ∨ p3))) := by
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
  -- Conjunctions on the left can always be decomposed.
  let h7 := h5.left
  let h8 := h5.right
  -- Conjunctions on the left can always be decomposed.
  let h9 := h7.left
  let h10 := h7.right
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h4



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_110815279292808972225875270257 : ((((((False → (True ∧ (p5 ∨ True))) ∨ p2) → (((p1 ∧ p2) ∨ (p3 ∨ (p5 ∨ (p1 → p5)))) → (p2 ∧ p1))) ∨ p1) ∧ p1) ∨ (False → True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_116031010545725911228376746501 : (((p5 ∧ (True ∨ (False ∧ p5))) → (p3 ∨ (p2 → (p1 → (False ∧ ((p4 → (False ∨ p2)) → (True ∨ ((p1 ∨ True) ∨ False)))))))) ∨ (True ∧ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_136132809370517574879595888185 : ((((((p1 → p5) ∧ (p5 → p4)) ∧ p3) ∨ False) → ((False ∧ (p3 ∧ ((p4 ∨ (p3 ∨ p3)) → True))) ∧ (p1 → True))) ∨ (False ∨ (p5 → p5))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_185008523086352659136868132493 : (((True ∨ p1) ∧ ((False ∨ p1) ∨ (((p3 ∨ p3) ∨ p4) ∨ True))) ∨ ((True ∨ p3) → (((p1 ∨ ((p4 ∨ p3) ∨ p3)) → False) ∧ (p5 ∨ p1)))) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
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
theorem thm_5_vars_246031144827716180068745367626 : ((p4 ∧ False) ∨ (((((p5 ∧ ((p2 ∨ (True ∧ True)) ∧ p2)) ∧ True) ∧ (p3 ∨ p4)) ∨ True) ∧ (True → ((p4 ∨ (p4 → p4)) ∧ (p2 ∨ True))))) := by
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
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h2
  -- One of the premise coincides with the conclusion.
  exact h2
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_789476271632119835239624876399 : (((p5 ∨ ((((p4 → (False ∧ False)) ∨ ((p2 ∧ (p3 ∨ p3)) → p5)) ∧ p2) → (((p5 → p3) ∨ True) ∨ (p1 → (p5 → (True ∧ p1)))))) ∨ False) ∧ True) := by
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
  -- Disjunctions on the left can always be decomposed.
  cases h2
  case inl h4 =>
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro
  case inr h5 =>
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_233294729036440355578539071463 : ((True ∨ (p2 ∨ p1)) → (((((((p1 → ((p2 ∧ p4) ∨ (False → p2))) → (p4 → (p4 → True))) → p4) → p1) ∨ True) → p3) ∨ (p2 → True))) := by
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
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Implications on the right can always be decomposed.
      intro h6
      -- True on the right can always be proven directly.
      apply True.intro
    case inr h7 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Implications on the right can always be decomposed.
      intro h8
      -- True on the right can always be proven directly.
      apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_153800143681191019282955362755 : ((p5 → ((((True → p3) ∨ p3) ∧ (p2 ∧ (((((p5 ∧ True) ∧ True) → False) ∧ (p4 ∧ p3)) → p1))) ∧ p2)) → ((p1 ∨ (p5 ∧ p1)) ∨ True)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_600650193169074967528849296631 : ((((False ∧ ((p3 ∧ (((p4 ∨ (False ∧ ((p3 → p3) ∧ p4))) ∨ ((p2 ∧ p2) → (True → ((p4 ∨ p5) → False)))) → p1)) ∨ p4)) ∧ False) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_254452446597943963399242436658 : ((p3 ∧ True) → ((((p2 → ((p5 ∧ p2) ∧ ((((p1 ∧ p5) ∨ p1) ∧ p1) ∨ ((p2 → p3) ∧ p4)))) ∧ True) ∧ (p1 ∨ (p1 → p5))) ∨ True)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_605097904890981955618550304836 : ((((p2 → (((((True ∨ p3) → p2) ∧ (((p1 → (False ∧ p2)) ∧ False) ∨ (((p3 ∨ p3) ∨ False) → p1))) ∧ p5) ∨ (p2 ∧ p1))) ∧ p4) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_197287505005329377633942809124 : (((((p1 ∨ p3) ∧ False) → (p1 → False)) → p5) ∨ (((p2 ∧ (((p2 → False) ∧ (p5 → p3)) ∧ ((False ∨ p4) ∨ p5))) ∧ p4) ∨ (p3 → p3))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_198464212838609464419515096457 : ((p5 ∧ (False ∧ (p5 ∨ (p4 ∨ (p1 ∧ p4))))) ∨ ((((((True → ((((p4 → p3) ∧ p2) → p1) ∨ p2)) → True) ∨ p1) ∨ p4) ∨ p2) → True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_125230854744667171491770635220 : (((p1 → (p5 ∧ p4)) ∨ ((p3 ∨ p4) → (((((p3 → (p5 ∨ p3)) → p2) ∧ p5) → p1) ∧ ((True ∨ p3) ∨ (p5 ∨ p1))))) → (p5 ∨ True)) := by
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
theorem thm_5_vars_112805174008120429169541895621 : ((((True ∨ (((p3 ∨ False) → True) ∧ True)) ∨ (((True → p5) ∧ (p1 ∨ (p1 ∧ (p1 → (p3 ∨ False))))) ∧ (p1 ∨ p5))) → False) ∨ (False → p2)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_666335890173068662913143984633 : ((((((p1 → ((True → p1) → ((p3 → True) → p4))) → (((p2 → p4) ∧ True) ∧ p5)) ∧ ((p4 ∧ p2) ∨ p4)) ∧ (p4 ∨ (p1 ∨ p2))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_324125971935637307921605335355 : (p5 ∨ ((p4 → ((((p2 ∨ p5) ∨ p3) ∧ p4) ∧ ((False ∧ p1) ∧ p5))) → (((p4 ∧ p4) ∨ (True → (((True ∧ p1) ∧ False) ∨ True))) ∨ True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_932795394301454628742384303045 : ((((p2 ∧ (False ∨ (((p3 → True) ∧ p5) ∨ p5))) ∧ (((((p4 → (p5 → p3)) ∧ p1) ∨ True) ∨ ((True ∨ False) → p1)) → (p5 ∧ False))) → p1) ∧ True) := by
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
    apply False.elim h6
  case inr h7 =>
    -- Disjunctions on the left can always be decomposed.
    cases h7
    case inl h8 =>
      -- Conjunctions on the left can always be decomposed.
      let h9 := h8.left
      let h10 := h8.right
      -- We want to use the implication h3 based on <expert-advice>. So we show its premise.
      have h11 : ((((p4 → (p5 → p3)) ∧ p1) ∨ True) ∨ ((True ∨ False) → p1)) := by
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- True on the right can always be proven directly.
        apply True.intro
      -- We have shown the premise of h3, we can now drive its conclusion.
      let h12 := h3 h11
      -- We need to get the right conjuct of h12 based on <expert-advice>.
      let h13 := h12.right
      -- False on the left can always be used.
      apply False.elim h13
    case inr h14 =>
      -- We want to use the implication h3 based on <expert-advice>. So we show its premise.
      have h15 : ((((p4 → (p5 → p3)) ∧ p1) ∨ True) ∨ ((True ∨ False) → p1)) := by
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- True on the right can always be proven directly.
        apply True.intro
      -- We have shown the premise of h3, we can now drive its conclusion.
      let h16 := h3 h15
      -- We need to get the right conjuct of h16 based on <expert-advice>.
      let h17 := h16.right
      -- False on the left can always be used.
      apply False.elim h17
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_178386993382385050765197820496 : ((((False → ((True ∨ (p5 ∧ True)) → p5)) ∧ (p3 ∧ True)) → (p1 ∨ p4)) ∨ (p1 → (((p5 ∧ False) → p2) ∨ (p2 ∨ (p2 ∧ (p5 ∧ False)))))) := by
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
  -- False on the left can always be used.
  apply False.elim h4



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_44769289882700224999030230203 : (((((False → p5) ∨ (p3 → p4)) → (((p5 ∨ (p1 → p5)) ∧ (p1 → p5)) → (False ∧ (((p2 ∨ p3) → (p5 → False)) → p2)))) → False) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_810640521612659190968703311739 : (((p5 → (((False ∧ p4) → False) ∧ (((((((p1 ∧ False) ∧ ((p5 ∨ True) ∧ False)) → p5) ∨ (p1 → (p1 ∧ p5))) ∨ p1) → p2) ∧ False))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_685068808772893345481023341446 : ((((False ∨ ((p1 → (((p4 ∨ ((p1 ∧ p2) ∧ p3)) → p3) ∨ p1)) → ((p5 ∨ p4) ∨ p4))) ∨ (((p3 → (p4 → p3)) ∧ p4) ∨ True)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_64896636067406457364506472972 : ((p2 ∨ (((((False ∨ (p5 ∨ False)) ∧ ((p2 → ((False ∧ (p5 → p5)) ∨ p1)) → p4)) ∧ p3) ∨ (p1 ∨ p2)) → ((p5 ∨ False) ∨ True))) ∨ p3) := by
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
    -- Conjunctions on the left can always be decomposed.
    let h5 := h3.left
    let h6 := h3.right
    -- Disjunctions on the left can always be decomposed.
    cases h5
    case inl h7 =>
      -- False on the left can always be used.
      apply False.elim h7
    case inr h8 =>
      -- Disjunctions on the left can always be decomposed.
      cases h8
      case inl h9 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- True on the right can always be proven directly.
        apply True.intro
      case inr h10 =>
        -- False on the left can always be used.
        apply False.elim h10
  case inr h11 =>
    -- Disjunctions on the left can always be decomposed.
    cases h11
    case inl h12 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- True on the right can always be proven directly.
      apply True.intro
    case inr h13 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- True on the right can always be proven directly.
      apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_181515807976873431679567593541 : ((True → ((((p1 ∧ (p5 ∨ p4)) ∨ (p2 ∧ (p3 → False))) ∨ p5) ∧ p2)) → ((p1 ∨ (((p5 ∧ p1) ∧ p1) → (p4 ∧ p2))) ∨ (p2 ∨ p1))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h2 : True := by
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h3 := h1 h2
  -- We need to get the right conjuct of h3 based on <expert-advice>.
  let h4 := h3.right
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- One of the premise coincides with the conclusion.
  exact h4



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_117933080584962398141913903684 : ((p5 ∧ ((p1 → p3) ∨ (((p4 → (False ∨ (((p3 ∨ ((True ∨ (p1 → p3)) ∧ False)) → p2) ∧ True))) ∨ (p4 ∧ False)) ∨ p4))) ∨ (False ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_80306759347244983726835518928 : ((((p4 ∧ (((False ∧ (p1 ∨ (((False → p1) ∨ (p3 → (False ∨ False))) ∧ p2))) ∨ p2) ∨ p1)) ∨ ((False → True) ∨ p2)) → (False ∧ p1)) → False) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h2 : ((p4 ∧ (((False ∧ (p1 ∨ (((False → p1) ∨ (p3 → (False ∨ False))) ∧ p2))) ∨ p2) ∨ p1)) ∨ ((False → True) ∨ p2)) := by
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Implications on the right can always be decomposed.
    intro h3
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h4 := h1 h2
  -- We need to get the left conjuct of h4 based on <expert-advice>.
  let h5 := h4.left
  -- False on the left can always be used.
  apply False.elim h5



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_178424259476953360588159657789 : (((p2 → ((((p3 ∨ p4) → (p3 → p1)) → p5) ∨ p1)) → (p5 ∨ p4)) ∨ ((p3 → (p1 ∨ (False → ((p4 → True) → p4)))) ∨ (p1 ∨ True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_261981751729973651958724300130 : (True ∧ ((True ∧ ((p3 ∧ ((p4 ∧ True) ∨ (p5 ∧ True))) ∨ (((p1 ∧ p1) ∧ p4) ∨ (p5 → (True ∨ (False ∨ (p4 ∨ (False ∨ p4)))))))) ∧ True)) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
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
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_50828685680687433258120631579 : (((((((p3 → ((p4 ∧ p5) → p1)) → ((False → p1) ∧ p1)) → (True ∧ p4)) → True) ∧ p2) ∧ ((p4 ∨ p5) ∨ (p5 ∨ (p3 ∨ False)))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_923385344283921723144754313409 : ((((((p5 → ((p5 → (p4 → p3)) ∨ p1)) → False) ∧ (p2 ∨ p2)) ∧ ((p3 ∨ (p5 ∧ p4)) ∧ (p3 ∧ ((p1 ∨ (p1 ∧ p3)) → False)))) → p3) ∧ True) := by
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
    -- Conjunctions on the left can always be decomposed.
    let h7 := h3.left
    let h8 := h3.right
    -- Disjunctions on the left can always be decomposed.
    cases h7
    case inl h9 =>
      -- Conjunctions on the left can always be decomposed.
      let h10 := h8.left
      let h11 := h8.right
      -- One of the premise coincides with the conclusion.
      exact h10
    case inr h12 =>
      -- Conjunctions on the left can always be decomposed.
      let h13 := h12.left
      let h14 := h12.right
      -- Conjunctions on the left can always be decomposed.
      let h15 := h8.left
      let h16 := h8.right
      -- One of the premise coincides with the conclusion.
      exact h15
  case inr h17 =>
    -- Conjunctions on the left can always be decomposed.
    let h18 := h3.left
    let h19 := h3.right
    -- Disjunctions on the left can always be decomposed.
    cases h18
    case inl h20 =>
      -- Conjunctions on the left can always be decomposed.
      let h21 := h19.left
      let h22 := h19.right
      -- One of the premise coincides with the conclusion.
      exact h21
    case inr h23 =>
      -- Conjunctions on the left can always be decomposed.
      let h24 := h23.left
      let h25 := h23.right
      -- Conjunctions on the left can always be decomposed.
      let h26 := h19.left
      let h27 := h19.right
      -- One of the premise coincides with the conclusion.
      exact h26
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_110873420398553101787008801766 : ((((((p4 → p5) → ((((False ∧ (p2 → (p3 ∨ p5))) ∧ ((p2 ∧ p4) ∨ p4)) ∨ p5) → p1)) ∧ (p5 ∨ p2)) → p2) ∧ p3) ∨ (True ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_351730244181173402881011898693 : (p4 → (((((p2 ∨ ((p3 → p2) → False)) ∧ p2) → True) → (False ∧ (p5 → p4))) ∨ ((p1 ∧ p5) → (True → (p5 ∨ (False ∧ (p1 → p1))))))) := by
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
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- One of the premise coincides with the conclusion.
  exact h5



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_707435168565135825974005374045 : ((((((p1 → False) ∨ False) ∧ (p4 ∧ (p5 ∧ p5))) ∨ (False → ((False ∧ (((p1 ∧ (p2 → (p2 ∨ False))) ∨ True) ∧ p3)) ∨ (True ∨ False)))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_643635804863929352383492874885 : ((((p4 ∧ (p4 → ((((True ∨ ((p3 ∧ p2) ∨ p1)) ∧ ((p5 ∨ ((p5 → (p5 ∨ p4)) ∨ (p1 ∨ p5))) ∨ True)) ∧ p2) ∨ p5))) → False) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_353507958806875932471244778391 : (p4 → (p2 ∨ ((False → True) → (((((((False ∨ p4) ∨ (p4 ∨ p2)) → True) → (True → (p5 → p1))) ∧ False) ∧ (False ∧ (p1 → p1))) ∨ p4)))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h2
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_158806502225402286871532836045 : ((p5 ∧ (p2 ∧ (p3 ∧ ((p2 → p5) ∧ ((p5 → p1) ∧ (True ∧ (p1 ∧ ((p4 → True) → p1)))))))) ∨ (p4 ∨ ((p2 → p2) ∧ (p4 ∨ True)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h1
  -- One of the premise coincides with the conclusion.
  exact h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_258931098219717202915863008649 : ((True → p2) → (p3 ∨ ((((False → p3) → (p4 ∨ p3)) ∨ (False ∧ (((p1 ∧ (p1 → p5)) ∨ p3) ∧ False))) ∨ ((False → (True → p5)) ∨ True)))) := by
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
theorem thm_5_vars_117654304285400836097253768147 : ((p3 ∧ ((p4 ∧ (p2 ∧ (((True ∨ p2) ∨ (((p5 ∧ False) → (False ∨ p3)) → (p3 ∧ p3))) ∨ (p3 ∧ p5)))) ∨ (p1 ∧ p5))) ∨ (p5 → p5)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_65096836451940539117251535253 : ((p2 ∨ (p2 ∨ ((((True ∧ True) ∧ (((p5 ∨ p2) → (p4 → True)) → (p4 ∧ p2))) ∨ p5) ∨ (True ∨ (p3 ∨ (p1 ∧ (True ∨ False))))))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_134196358590325229772320332237 : ((((((p1 ∧ p4) → (p2 ∨ ((p1 ∨ True) → False))) ∧ p1) ∨ (p2 → (((p1 → p4) → p4) → (p3 ∨ p2)))) ∨ p2) ∨ ((p3 ∨ p5) ∨ False)) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_354708975956788211656616493425 : (p5 → ((((((((p3 ∨ p1) → True) ∨ True) ∨ (((p1 ∨ (p5 → p5)) ∧ (p5 → p1)) ∧ True)) → False) ∧ p3) ∧ ((False ∧ p5) ∧ True)) ∨ True)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_339702029145109995313977779768 : (p1 → (p3 ∨ (p1 ∧ ((((p4 ∨ p3) → p5) ∨ ((p5 ∨ p1) → p5)) → (((p2 ∨ p3) ∧ False) ∨ (False ∨ ((p4 ∧ False) → (p3 ∨ p1)))))))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- One of the premise coincides with the conclusion.
  exact h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Disjunctions on the left can always be decomposed.
  cases h2
  case inl h3 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h4
    -- Conjunctions on the left can always be decomposed.
    let h5 := h4.left
    let h6 := h4.right
    -- False on the left can always be used.
    apply False.elim h6
  case inr h7 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h8
    -- Conjunctions on the left can always be decomposed.
    let h9 := h8.left
    let h10 := h8.right
    -- False on the left can always be used.
    apply False.elim h10



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_247736738957055712038867543000 : ((p1 ∨ False) ∨ ((p2 ∨ ((p3 → (True ∧ (True ∧ p3))) → p4)) → (p5 → ((((p5 ∨ (p5 ∨ p3)) → p3) ∨ ((p5 ∨ p5) → p3)) ∨ p5)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h3 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h2
  case inr h4 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_238009734514140293735478300244 : ((True ∨ p1) ∧ (((((p1 ∧ ((False ∨ p2) ∧ p5)) ∧ ((False → (p5 → False)) ∧ (p5 → p3))) → (p4 ∨ p2)) → p4) ∨ ((p5 ∧ p2) ∨ True))) := by
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
theorem thm_5_vars_40203540536275870779160733000 : (((((False → False) ∧ (p3 ∨ ((((((p5 ∨ p3) ∨ p5) ∨ p5) ∧ True) ∨ (p3 → p1)) ∧ ((p4 → (p3 → p3)) ∨ p2)))) ∧ p4) ∨ True) ∨ p3) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_793583736958181467755492750575 : (((True → (p3 ∨ (((((p5 ∧ ((p1 → p2) ∧ ((p2 ∨ False) ∨ p1))) ∨ p5) ∨ p5) → p4) ∨ (False → (((True ∧ p3) ∨ p2) → p4))))) ∨ False) ∧ True) := by
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
    -- False on the left can always be used.
    apply False.elim h2
  case inr h7 =>
    -- False on the left can always be used.
    apply False.elim h2
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_782568427344387408912028690758 : (((p3 ∨ ((p2 ∨ ((((p1 ∧ p1) ∧ ((p3 ∨ p4) ∧ (True ∨ ((p5 → (False ∧ True)) ∨ p5)))) ∧ (p3 ∧ p5)) ∧ (False → p2))) ∨ p1)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_713812170549134407928296056567 : ((((((False ∨ (p3 ∨ False)) ∨ False) ∨ p5) → ((p2 → False) → ((p1 → ((((True ∨ p1) ∨ (p1 → p3)) ∨ (p5 → p3)) → p4)) ∧ p2))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_641765350471583478898245436333 : (((((p4 ∨ False) → (p3 → ((((p3 ∨ p1) ∧ p2) ∧ ((((p4 ∨ True) ∨ p4) ∨ ((p1 → True) ∧ p3)) ∨ (p1 → False))) ∨ p5))) → False) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_207765199951153545328912439525 : (((p2 ∨ (p3 ∧ (p4 → p1))) → p5) → (p2 ∨ (((((p5 ∨ p4) ∧ p3) ∧ p3) ∧ (((p4 ∧ (p3 ∧ p1)) ∨ p2) ∨ p2)) ∨ (True ∨ p5)))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_679725502604994272846674381980 : ((((((True ∧ ((p4 → p4) ∧ ((p3 ∨ p1) → (p1 ∧ (p4 ∨ (p5 ∨ p1)))))) ∨ (p1 → p5)) ∨ p2) → ((True ∧ p2) ∨ (False ∨ p5))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_564978244839444439630887089277 : (((True → ((p5 ∨ ((((p1 → (p2 ∨ p5)) ∧ p3) → (p4 → True)) → (p4 ∧ (((p2 ∧ (p2 ∨ (p5 ∧ p4))) ∨ p1) ∧ False)))) ∨ True)) ∧ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_119406144220028758636589369266 : ((p4 → ((False ∧ (p3 ∨ (((p3 → (p4 → p3)) ∨ (((p1 → False) → (p5 ∨ (p2 ∧ p5))) → (False ∨ False))) → p5))) ∨ True)) ∨ (p5 ∨ p4)) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_148390161631433087377056867409 : ((((p5 ∧ p1) ∨ (p3 ∧ (((p3 ∧ p4) ∧ (p1 ∧ (True ∨ p2))) → True))) ∨ (((p1 ∧ False) ∨ p4) ∨ p1)) ∨ ((p1 → p5) ∨ (p3 → True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_8714026104417509268572685772 : ((((p1 → (p4 ∧ (p2 → (((False ∧ (((p2 ∧ p5) ∧ ((p1 → p3) → False)) → (p3 ∧ False))) ∨ False) → p5)))) → (p1 ∨ p5)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_259678311139315795949592179145 : ((p1 → p1) → ((True → (((p2 → p5) ∧ (p4 → (p4 → p5))) ∨ ((p2 ∨ (((p2 ∨ p5) → (False ∧ p4)) ∧ p5)) → (p1 ∨ p1)))) ∨ True)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_906289617043109188456841757042 : ((((((True ∨ (p3 → (((p2 ∧ p3) ∧ p5) ∧ p1))) → (p5 ∨ ((p2 ∨ False) → (p2 → False)))) ∨ True) → ((True → False) ∧ (p2 ∨ p1))) → p4) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h1
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h2 : (((True ∨ (p3 → (((p2 ∧ p3) ∧ p5) ∧ p1))) → (p5 ∨ ((p2 ∨ False) → (p2 → False)))) ∨ True) := by
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h3 := h1 h2
  -- We need to get the left conjuct of h3 based on <expert-advice>.
  let h4 := h3.left
  -- We want to use the implication h4 based on <expert-advice>. So we show its premise.
  have h5 : True := by
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h4, we can now drive its conclusion.
  let h6 := h4 h5
  -- False on the left can always be used.
  apply False.elim h6
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_149870249820323732635514289516 : ((p2 ∨ (((p5 → (False ∧ p2)) ∨ (p5 ∨ (p4 ∨ (p3 ∧ (((False ∨ p4) ∨ p1) ∧ (p5 ∧ p2)))))) → False)) ∨ (p2 → ((False ∧ True) → False))) := by
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



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_147840464731598149218764569375 : (((p3 ∨ ((p1 ∨ True) ∨ (p1 → (p4 ∧ ((p3 → False) ∧ ((p1 ∧ (False ∨ (p3 ∨ p3))) ∧ p3)))))) → p3) ∨ ((p2 → True) → (True ∨ p1))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_1938161664903361547964526254 : (((((p2 → True) → ((p4 ∨ (p1 ∧ p5)) → (p4 ∧ p2))) ∧ (True ∧ (True ∧ (p1 ∧ p2)))) ∧ p5) ∨ (((p1 ∧ p1) ∧ False) → True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



