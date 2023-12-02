variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_347001711030557479598026436621 : (p3 → (((p5 ∧ ((((((p5 → p5) ∧ p1) ∧ p3) → p5) → p5) → (p4 → p1))) ∧ p1) ∨ (True ∨ ((p2 → p1) → (False ∨ (True ∨ p5)))))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_53902169670532992262322700495 : (((p3 ∧ (p5 ∧ (True ∨ ((p1 ∧ True) ∧ (p2 ∨ False))))) ∨ (p5 → ((((((True ∨ False) ∨ p2) ∧ p1) ∨ p1) ∧ (p3 ∨ p2)) ∨ True))) ∨ p5) := by
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



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_245610618964057771291148724013 : ((p3 ∧ False) ∨ (((p1 ∧ p4) ∧ ((p2 ∨ False) ∧ (False ∧ p1))) ∨ ((((False ∨ ((p2 → p5) → p4)) → True) ∨ (False → p1)) ∨ (False ∨ p3)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_51612085813015639069499146694 : (((((p3 → (((p1 → p1) → p2) ∧ (((p5 ∨ p2) → False) ∨ p5))) ∨ p3) ∧ p1) ∧ ((((p4 ∧ p1) → p1) ∨ p5) → (p4 → True))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_338913020251859669666324752207 : (p1 → ((True ∨ p3) → ((p3 ∧ ((p5 ∨ (False ∨ (False ∨ p1))) ∧ False)) ∨ ((p3 ∨ (((False → p5) ∧ p3) → True)) → (p3 ∨ (True ∨ p1)))))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Disjunctions on the left can always be decomposed.
  cases h2
  case inl h3 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h4
    -- Disjunctions on the left can always be decomposed.
    cases h4
    case inl h5 =>
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- One of the premise coincides with the conclusion.
      exact h5
    case inr h6 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- True on the right can always be proven directly.
      apply True.intro
  case inr h7 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h8
    -- Disjunctions on the left can always be decomposed.
    cases h8
    case inl h9 =>
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- One of the premise coincides with the conclusion.
      exact h9
    case inr h10 =>
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- One of the premise coincides with the conclusion.
      exact h7



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_9030270683620079668719784588 : (((((((p2 ∧ p5) → p3) ∧ p1) → (False ∨ ((p1 ∧ (True → True)) ∧ p3))) ∧ ((True ∧ True) → ((p4 ∧ p3) ∧ (p2 ∧ True)))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_67637447550053359614652731155 : ((p1 → (False ∨ ((p2 → p2) ∧ ((False ∧ ((p4 ∨ (p5 ∧ (((True ∧ True) ∧ (False ∧ p1)) ∧ True))) ∨ ((p3 → p5) ∨ p3))) ∧ True)))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_752385091790383227737097797792 : (((False ∧ (((((p3 → (False ∧ (p2 → ((((((True → p4) ∨ p3) ∨ p1) ∧ False) ∨ p5) ∧ p1)))) ∨ p5) → p1) ∨ (p4 → p5)) ∧ p5)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_165767904049133745388379270025 : (((((p3 ∨ p2) → p1) ∨ False) → (((False ∨ False) ∨ p2) ∨ ((p2 → p5) ∧ (True ∨ p3)))) ∨ ((p2 ∨ (((p5 ∧ True) ∨ p2) → p1)) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_215106714740484080161698123542 : (((p2 → True) → (False ∧ p4)) ∨ ((p5 → ((True ∧ (p1 → (False → False))) ∧ p5)) ∧ (((False ∨ p4) → (p3 ∧ ((p5 → p1) ∨ p5))) ∨ True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
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
  -- Implications on the right can always be decomposed.
  intro h3
  -- False on the left can always be used.
  apply False.elim h3
  -- One of the premise coincides with the conclusion.
  exact h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_62719725019939872577978175786 : ((p4 ∧ ((p5 ∨ (((p4 ∨ True) ∧ p2) ∧ (((p1 → (p4 → (False ∧ (p3 → p2)))) ∧ p2) ∨ (p1 ∨ (p2 ∧ (p3 ∧ p1)))))) → False)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_676850589618196395264822470833 : ((((p3 ∨ ((((p1 → p3) ∧ p4) → False) → (((p3 → ((p1 ∧ p3) ∧ (p5 ∨ False))) ∨ p2) → p3))) ∧ ((True → p2) ∧ (p2 ∨ p1))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_342596234069401967018719948933 : (p2 → (((((((p2 ∧ False) ∨ True) ∨ (p2 ∧ p4)) ∧ False) → p5) → False) → ((p1 ∨ (((p5 → False) ∧ True) ∨ True)) → ((False ∧ False) ∧ p3)))) := by
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
  cases h3
  case inl h4 =>
    -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
    have h5 : (((((p2 ∧ False) ∨ True) ∨ (p2 ∧ p4)) ∧ False) → p5) := by
      -- Implications on the right can always be decomposed.
      intro h6
      -- Conjunctions on the left can always be decomposed.
      let h7 := h6.left
      let h8 := h6.right
      -- Disjunctions on the left can always be decomposed.
      cases h7
      case inl h9 =>
        -- Disjunctions on the left can always be decomposed.
        cases h9
        case inl h10 =>
          -- Conjunctions on the left can always be decomposed.
          let h11 := h10.left
          let h12 := h10.right
          -- False on the left can always be used.
          apply False.elim h12
        case inr h13 =>
          -- False on the left can always be used.
          apply False.elim h8
      case inr h14 =>
        -- Conjunctions on the left can always be decomposed.
        let h15 := h14.left
        let h16 := h14.right
        -- False on the left can always be used.
        apply False.elim h8
    -- We have shown the premise of h2, we can now drive its conclusion.
    let h17 := h2 h5
    -- False on the left can always be used.
    apply False.elim h17
  case inr h18 =>
    -- Disjunctions on the left can always be decomposed.
    cases h18
    case inl h19 =>
      -- Conjunctions on the left can always be decomposed.
      let h20 := h19.left
      let h21 := h19.right
      -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
      have h22 : (((((p2 ∧ False) ∨ True) ∨ (p2 ∧ p4)) ∧ False) → p5) := by
        -- Implications on the right can always be decomposed.
        intro h23
        -- Conjunctions on the left can always be decomposed.
        let h24 := h23.left
        let h25 := h23.right
        -- Disjunctions on the left can always be decomposed.
        cases h24
        case inl h26 =>
          -- Disjunctions on the left can always be decomposed.
          cases h26
          case inl h27 =>
            -- Conjunctions on the left can always be decomposed.
            let h28 := h27.left
            let h29 := h27.right
            -- False on the left can always be used.
            apply False.elim h29
          case inr h30 =>
            -- False on the left can always be used.
            apply False.elim h25
        case inr h31 =>
          -- Conjunctions on the left can always be decomposed.
          let h32 := h31.left
          let h33 := h31.right
          -- False on the left can always be used.
          apply False.elim h25
      -- We have shown the premise of h2, we can now drive its conclusion.
      let h34 := h2 h22
      -- False on the left can always be used.
      apply False.elim h34
    case inr h35 =>
      -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
      have h36 : (((((p2 ∧ False) ∨ True) ∨ (p2 ∧ p4)) ∧ False) → p5) := by
        -- Implications on the right can always be decomposed.
        intro h37
        -- Conjunctions on the left can always be decomposed.
        let h38 := h37.left
        let h39 := h37.right
        -- Disjunctions on the left can always be decomposed.
        cases h38
        case inl h40 =>
          -- Disjunctions on the left can always be decomposed.
          cases h40
          case inl h41 =>
            -- Conjunctions on the left can always be decomposed.
            let h42 := h41.left
            let h43 := h41.right
            -- False on the left can always be used.
            apply False.elim h43
          case inr h44 =>
            -- False on the left can always be used.
            apply False.elim h39
        case inr h45 =>
          -- Conjunctions on the left can always be decomposed.
          let h46 := h45.left
          let h47 := h45.right
          -- False on the left can always be used.
          apply False.elim h39
      -- We have shown the premise of h2, we can now drive its conclusion.
      let h48 := h2 h36
      -- False on the left can always be used.
      apply False.elim h48
  -- Disjunctions on the left can always be decomposed.
  cases h3
  case inl h49 =>
    -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
    have h50 : (((((p2 ∧ False) ∨ True) ∨ (p2 ∧ p4)) ∧ False) → p5) := by
      -- Implications on the right can always be decomposed.
      intro h51
      -- Conjunctions on the left can always be decomposed.
      let h52 := h51.left
      let h53 := h51.right
      -- Disjunctions on the left can always be decomposed.
      cases h52
      case inl h54 =>
        -- Disjunctions on the left can always be decomposed.
        cases h54
        case inl h55 =>
          -- Conjunctions on the left can always be decomposed.
          let h56 := h55.left
          let h57 := h55.right
          -- False on the left can always be used.
          apply False.elim h57
        case inr h58 =>
          -- False on the left can always be used.
          apply False.elim h53
      case inr h59 =>
        -- Conjunctions on the left can always be decomposed.
        let h60 := h59.left
        let h61 := h59.right
        -- False on the left can always be used.
        apply False.elim h53
    -- We have shown the premise of h2, we can now drive its conclusion.
    let h62 := h2 h50
    -- False on the left can always be used.
    apply False.elim h62
  case inr h63 =>
    -- Disjunctions on the left can always be decomposed.
    cases h63
    case inl h64 =>
      -- Conjunctions on the left can always be decomposed.
      let h65 := h64.left
      let h66 := h64.right
      -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
      have h67 : (((((p2 ∧ False) ∨ True) ∨ (p2 ∧ p4)) ∧ False) → p5) := by
        -- Implications on the right can always be decomposed.
        intro h68
        -- Conjunctions on the left can always be decomposed.
        let h69 := h68.left
        let h70 := h68.right
        -- Disjunctions on the left can always be decomposed.
        cases h69
        case inl h71 =>
          -- Disjunctions on the left can always be decomposed.
          cases h71
          case inl h72 =>
            -- Conjunctions on the left can always be decomposed.
            let h73 := h72.left
            let h74 := h72.right
            -- False on the left can always be used.
            apply False.elim h74
          case inr h75 =>
            -- False on the left can always be used.
            apply False.elim h70
        case inr h76 =>
          -- Conjunctions on the left can always be decomposed.
          let h77 := h76.left
          let h78 := h76.right
          -- False on the left can always be used.
          apply False.elim h70
      -- We have shown the premise of h2, we can now drive its conclusion.
      let h79 := h2 h67
      -- False on the left can always be used.
      apply False.elim h79
    case inr h80 =>
      -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
      have h81 : (((((p2 ∧ False) ∨ True) ∨ (p2 ∧ p4)) ∧ False) → p5) := by
        -- Implications on the right can always be decomposed.
        intro h82
        -- Conjunctions on the left can always be decomposed.
        let h83 := h82.left
        let h84 := h82.right
        -- Disjunctions on the left can always be decomposed.
        cases h83
        case inl h85 =>
          -- Disjunctions on the left can always be decomposed.
          cases h85
          case inl h86 =>
            -- Conjunctions on the left can always be decomposed.
            let h87 := h86.left
            let h88 := h86.right
            -- False on the left can always be used.
            apply False.elim h88
          case inr h89 =>
            -- False on the left can always be used.
            apply False.elim h84
        case inr h90 =>
          -- Conjunctions on the left can always be decomposed.
          let h91 := h90.left
          let h92 := h90.right
          -- False on the left can always be used.
          apply False.elim h84
      -- We have shown the premise of h2, we can now drive its conclusion.
      let h93 := h2 h81
      -- False on the left can always be used.
      apply False.elim h93
  -- Disjunctions on the left can always be decomposed.
  cases h3
  case inl h94 =>
    -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
    have h95 : (((((p2 ∧ False) ∨ True) ∨ (p2 ∧ p4)) ∧ False) → p5) := by
      -- Implications on the right can always be decomposed.
      intro h96
      -- Conjunctions on the left can always be decomposed.
      let h97 := h96.left
      let h98 := h96.right
      -- Disjunctions on the left can always be decomposed.
      cases h97
      case inl h99 =>
        -- Disjunctions on the left can always be decomposed.
        cases h99
        case inl h100 =>
          -- Conjunctions on the left can always be decomposed.
          let h101 := h100.left
          let h102 := h100.right
          -- False on the left can always be used.
          apply False.elim h102
        case inr h103 =>
          -- False on the left can always be used.
          apply False.elim h98
      case inr h104 =>
        -- Conjunctions on the left can always be decomposed.
        let h105 := h104.left
        let h106 := h104.right
        -- False on the left can always be used.
        apply False.elim h98
    -- We have shown the premise of h2, we can now drive its conclusion.
    let h107 := h2 h95
    -- False on the left can always be used.
    apply False.elim h107
  case inr h108 =>
    -- Disjunctions on the left can always be decomposed.
    cases h108
    case inl h109 =>
      -- Conjunctions on the left can always be decomposed.
      let h110 := h109.left
      let h111 := h109.right
      -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
      have h112 : (((((p2 ∧ False) ∨ True) ∨ (p2 ∧ p4)) ∧ False) → p5) := by
        -- Implications on the right can always be decomposed.
        intro h113
        -- Conjunctions on the left can always be decomposed.
        let h114 := h113.left
        let h115 := h113.right
        -- Disjunctions on the left can always be decomposed.
        cases h114
        case inl h116 =>
          -- Disjunctions on the left can always be decomposed.
          cases h116
          case inl h117 =>
            -- Conjunctions on the left can always be decomposed.
            let h118 := h117.left
            let h119 := h117.right
            -- False on the left can always be used.
            apply False.elim h119
          case inr h120 =>
            -- False on the left can always be used.
            apply False.elim h115
        case inr h121 =>
          -- Conjunctions on the left can always be decomposed.
          let h122 := h121.left
          let h123 := h121.right
          -- False on the left can always be used.
          apply False.elim h115
      -- We have shown the premise of h2, we can now drive its conclusion.
      let h124 := h2 h112
      -- False on the left can always be used.
      apply False.elim h124
    case inr h125 =>
      -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
      have h126 : (((((p2 ∧ False) ∨ True) ∨ (p2 ∧ p4)) ∧ False) → p5) := by
        -- Implications on the right can always be decomposed.
        intro h127
        -- Conjunctions on the left can always be decomposed.
        let h128 := h127.left
        let h129 := h127.right
        -- Disjunctions on the left can always be decomposed.
        cases h128
        case inl h130 =>
          -- Disjunctions on the left can always be decomposed.
          cases h130
          case inl h131 =>
            -- Conjunctions on the left can always be decomposed.
            let h132 := h131.left
            let h133 := h131.right
            -- False on the left can always be used.
            apply False.elim h133
          case inr h134 =>
            -- False on the left can always be used.
            apply False.elim h129
        case inr h135 =>
          -- Conjunctions on the left can always be decomposed.
          let h136 := h135.left
          let h137 := h135.right
          -- False on the left can always be used.
          apply False.elim h129
      -- We have shown the premise of h2, we can now drive its conclusion.
      let h138 := h2 h126
      -- False on the left can always be used.
      apply False.elim h138



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_190818125451447764259738285536 : (((p3 ∧ (p4 → (p5 → (p2 ∨ True)))) ∨ (p2 ∧ False)) ∨ ((True → p2) → (p2 ∨ ((p2 ∨ p2) → ((p4 → ((p5 ∧ False) ∧ p5)) ∨ p5))))) := by
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
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- One of the premise coincides with the conclusion.
  exact h3



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_345384806180544621600166148001 : (p3 → (((p2 ∨ (((True → ((p5 → False) ∨ p1)) ∧ (p3 ∨ p1)) ∨ ((p5 ∨ p5) ∨ (((False ∨ False) ∨ p5) ∧ (p5 ∨ p1))))) ∨ p3) ∨ False)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_230517688175382899473696377507 : (((True → p5) ∧ p2) → (((((p3 → (p2 ∧ (p4 → ((((p1 → (True → True)) ∧ p3) ∨ p2) ∧ False)))) ∨ p3) ∧ False) ∨ p5) ∧ (False ∨ True))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
  have h4 : True := by
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h2, we can now drive its conclusion.
  let h5 := h2 h4
  -- One of the premise coincides with the conclusion.
  exact h5
  -- Conjunctions on the left can always be decomposed.
  let h6 := h1.left
  let h7 := h1.right
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_300149988953705983187977724094 : (False ∨ ((p1 ∨ (p3 ∨ (p5 ∨ ((p3 ∨ (p3 ∨ p2)) ∧ (((p3 → p4) ∨ (p5 → True)) ∧ (p5 → (p1 ∧ (p1 ∧ p2)))))))) ∨ (p3 ∨ True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_687692903453747721433025576615 : (((((((p3 ∨ False) ∧ ((((p5 ∧ p1) ∧ False) ∧ p5) → p2)) ∨ p3) ∧ (False → p2)) ∧ (True → (((p4 ∧ (p3 ∧ p4)) ∨ True) ∧ p3))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_51937662969530190502346278097 : (((((p2 ∧ (p4 ∨ (p5 ∨ (p4 ∨ False)))) ∧ False) ∨ (True → ((p5 → p1) ∨ True))) ∨ (False ∧ ((p3 ∧ p5) → ((False ∨ p3) → p4)))) ∨ p4) := by
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
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_258035924697163102448409305270 : ((p4 ∨ p2) → (((p1 → ((p2 ∧ p3) ∧ (((p4 → p5) ∧ True) ∨ (False ∧ (p2 ∧ (p5 ∧ p3)))))) → ((p4 ∨ (p4 ∧ p5)) ∨ p1)) ∨ p2)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h2 =>
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Implications on the right can always be decomposed.
    intro h3
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- One of the premise coincides with the conclusion.
    exact h2
  case inr h4 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h4



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_114254530837919439997232763987 : (((p1 → ((p1 ∧ ((p4 → p1) ∨ True)) ∨ ((True ∧ ((p5 ∧ ((p2 → p5) ∧ False)) → p5)) ∧ False))) → ((True ∧ False) ∨ p5)) ∨ (p2 → True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_214788815006123496497629380170 : (((p1 ∨ False) ∨ (p2 ∧ p3)) ∨ (p1 → ((p2 ∨ True) ∧ (True ∨ (((p3 → ((p1 ∨ (p3 ∧ False)) ∧ p5)) → (p3 → (False ∧ p1))) ∧ p3))))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_111353869498853510342458690503 : (((p4 ∧ ((p2 ∨ p5) → (p5 → ((p2 ∨ (((p1 ∧ (p5 → (p3 ∨ p2))) → p2) ∧ (p1 ∧ (p4 ∨ p1)))) ∨ p1)))) ∧ False) ∨ (p2 → p2)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_60211699923613940609246939401 : (((True → False) → (((p4 → ((((p5 ∧ (False ∧ p1)) ∧ p3) ∨ p1) ∨ (False ∧ ((p4 ∨ True) → p5)))) ∧ (p3 ∨ p1)) ∧ (p1 ∧ True))) ∨ p3) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
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
  -- False on the left can always be used.
  apply False.elim h4
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h5 : True := by
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h6 := h1 h5
  -- False on the left can always be used.
  apply False.elim h6
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h7 : True := by
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h8 := h1 h7
  -- False on the left can always be used.
  apply False.elim h8
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_675768652534333217852166738305 : (((((p5 ∨ ((((p2 ∨ False) ∧ (((True → p1) ∧ False) → False)) ∨ p2) ∨ p1)) ∨ (True → (p3 ∨ True))) ∧ (((p1 → p4) ∨ p3) ∨ True)) ∨ p2) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
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
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_148249671086279124168002460848 : ((((True → (False ∧ p2)) → (p1 ∨ (p4 ∨ (p2 → ((p5 → (p5 ∧ p4)) ∧ p4))))) ∨ (p3 ∨ (p2 → p4))) ∨ ((p1 → (p2 ∨ True)) ∨ p2)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_523722121668576911262420507605 : (((True ∧ ((((((p1 → (p2 ∧ (p2 ∧ (p1 ∧ ((p2 ∨ p4) ∨ (p1 ∧ p2)))))) ∨ True) ∧ p5) → p1) ∨ (p2 → p1)) ∨ (p2 ∨ True))) ∧ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
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
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_265875734340732690341079768737 : (True ∧ (True → ((((((((((p1 ∨ p3) ∧ (p4 ∨ (p5 ∧ p2))) → p4) ∨ p4) → p3) ∧ False) ∧ (False ∧ (p1 → p3))) ∧ p1) ∨ p5) ∨ True))) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_249204618389502760796146077596 : ((p4 ∨ p3) ∨ ((p5 ∨ p3) → (((p1 ∨ ((True ∧ p3) ∨ (((p5 → True) → (((True ∨ p1) ∧ p2) ∨ p1)) ∧ p3))) ∧ (p3 ∨ p4)) ∨ True))) := by
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
theorem thm_5_vars_318855145357616981293882345828 : (p4 ∨ (((p5 ∧ ((p4 ∨ p4) ∧ (p5 ∧ (p3 → ((False → (p5 ∨ (p2 → (False ∨ (p2 ∧ p1))))) ∧ p5))))) ∨ True) ∨ (p4 → (p2 ∨ p1)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_248910444913525779214364982508 : ((p3 ∨ p5) ∨ (p3 ∨ ((((((p1 ∨ p2) ∨ ((p3 → ((p1 → p5) ∨ p1)) ∧ (False → p2))) ∨ ((p3 → p2) ∨ p1)) ∨ True) ∨ p5) ∨ p3))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
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
theorem thm_5_vars_322426092206551609565573578277 : (p5 ∨ ((((p5 ∨ False) ∧ ((p3 → p1) ∨ (p1 → p3))) → ((((p1 ∧ p4) ∨ (p2 ∨ False)) → (p4 ∧ p1)) ∨ ((p5 ∨ p1) ∧ p5))) ∨ p3)) := by
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
    -- Disjunctions on the left can always be decomposed.
    cases h3
    case inl h5 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Conjunctions on the right can always be decomposed.
      apply And.intro
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- One of the premise coincides with the conclusion.
      exact h4
      -- One of the premise coincides with the conclusion.
      exact h4
    case inr h6 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Conjunctions on the right can always be decomposed.
      apply And.intro
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- One of the premise coincides with the conclusion.
      exact h4
      -- One of the premise coincides with the conclusion.
      exact h4
  case inr h7 =>
    -- False on the left can always be used.
    apply False.elim h7



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_356621773587075009970834535573 : (p5 → ((((p3 → (p2 → p2)) → p3) ∧ (p4 ∧ p1)) ∨ ((p3 → (((((p5 ∧ False) ∧ p4) ∨ p5) ∧ (p1 ∧ p4)) → p4)) ∨ (p2 ∨ p5)))) := by
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
theorem thm_5_vars_346327303282506148368700115881 : (p3 → (((True ∨ (((p1 → p2) ∧ (p1 → (p2 ∧ (p1 → True)))) ∨ (((p5 ∨ p1) ∨ p4) ∨ p5))) → ((p4 ∨ True) ∧ p3)) ∨ (p2 ∧ True))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h2
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
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
      -- Conjunctions on the left can always be decomposed.
      let h6 := h5.left
      let h7 := h5.right
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
          -- Show the left disjunct based on <expert-advice>.
          apply Or.inl
          -- One of the premise coincides with the conclusion.
          exact h13
      case inr h14 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- True on the right can always be proven directly.
        apply True.intro
  -- Disjunctions on the left can always be decomposed.
  cases h2
  case inl h15 =>
    -- One of the premise coincides with the conclusion.
    exact h1
  case inr h16 =>
    -- Disjunctions on the left can always be decomposed.
    cases h16
    case inl h17 =>
      -- Conjunctions on the left can always be decomposed.
      let h18 := h17.left
      let h19 := h17.right
      -- One of the premise coincides with the conclusion.
      exact h1
    case inr h20 =>
      -- Disjunctions on the left can always be decomposed.
      cases h20
      case inl h21 =>
        -- Disjunctions on the left can always be decomposed.
        cases h21
        case inl h22 =>
          -- Disjunctions on the left can always be decomposed.
          cases h22
          case inl h23 =>
            -- One of the premise coincides with the conclusion.
            exact h1
          case inr h24 =>
            -- One of the premise coincides with the conclusion.
            exact h1
        case inr h25 =>
          -- One of the premise coincides with the conclusion.
          exact h1
      case inr h26 =>
        -- One of the premise coincides with the conclusion.
        exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_46015737507313296392296515833 : ((((((p2 → p3) ∨ ((p3 ∧ p4) → p5)) → ((((p5 → p1) ∨ ((p1 → p1) → p3)) → (p1 ∨ p3)) → p5)) ∧ False) ∧ (False ∨ p1)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_134302209677290087079093726088 : ((((p1 → p1) → (False ∨ (((((p2 ∨ (p3 → p5)) → (p1 → ((p3 ∧ False) ∧ p1))) ∨ p1) ∨ p3) ∧ False))) ∨ True) ∨ (p1 → (p4 ∨ p4))) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_172957153507113225496196740495 : ((p4 ∧ ((p5 ∨ (((p5 ∨ p4) ∧ (p4 → ((p1 ∧ p5) ∧ p2))) ∨ p2)) ∧ p4)) ∨ ((p2 ∨ ((p1 → (p2 → True)) ∨ True)) ∨ (True ∧ p5))) := by
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
theorem thm_5_vars_725819394041236031749617060740 : (((((p5 ∨ True) ∧ False) ∨ ((False ∧ (p3 ∨ (p3 → ((False ∧ (False → p1)) ∧ False)))) ∧ (((p4 ∧ False) ∧ ((p4 ∨ p5) ∨ False)) → p5))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_975034029077759581569756655076 : ((((p3 → True) → (((((p2 → p1) ∨ p3) → (True ∧ (((p4 → p3) ∧ ((p3 → ((p3 ∧ p5) ∨ p3)) ∨ p1)) ∧ p5))) ∨ True) → p5)) → p5) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h1
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h2 : (p3 → True) := by
    -- Implications on the right can always be decomposed.
    intro h3
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h4 := h1 h2
  -- We want to use the implication h4 based on <expert-advice>. So we show its premise.
  have h5 : ((((p2 → p1) ∨ p3) → (True ∧ (((p4 → p3) ∧ ((p3 → ((p3 ∧ p5) ∨ p3)) ∨ p1)) ∧ p5))) ∨ True) := by
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h4, we can now drive its conclusion.
  let h6 := h4 h5
  -- One of the premise coincides with the conclusion.
  exact h6
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_301580186327763684460850782316 : (False ∨ ((p3 → (p5 → p4)) ∨ (p5 → (((((((p5 ∨ p4) → ((p1 ∨ True) ∧ p5)) ∧ p5) ∨ p2) ∧ (p1 ∨ (p2 → p3))) → False) ∨ p5)))) := by
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
theorem thm_5_vars_114840151147027634805112636714 : ((((((p2 ∨ True) → (p1 ∧ p4)) ∨ (((p4 ∧ p1) → p5) → False)) ∧ p5) ∨ ((((p5 ∨ True) → True) ∧ False) ∧ (p2 ∧ p2))) ∨ (p4 ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_158419296611816543443194899745 : (((p3 ∧ p4) ∨ ((((p5 ∧ (p2 ∧ p1)) → p4) ∧ (p3 ∧ ((False ∧ True) ∨ (p5 ∨ p3)))) ∧ p3)) ∨ (True ∧ (((p5 ∨ p2) ∧ p4) → p4))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- True on the right can always be proven directly.
  apply True.intro
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
    -- One of the premise coincides with the conclusion.
    exact h3



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_178889379257003211140264020037 : (((p5 ∧ p4) ∧ (((False ∨ p1) ∨ False) → ((p2 → (p4 ∧ p2)) ∧ p5))) ∨ ((p2 ∨ ((True → p3) → p5)) → (p2 ∨ ((p1 ∧ p4) ∨ True)))) := by
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
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_187022629858202114533131645399 : (((p3 ∨ (False ∨ False)) → ((p5 ∧ (p5 ∨ p4)) ∧ (False ∧ p4))) → ((p3 → (((p4 → p1) ∧ p5) → p1)) ∨ ((p2 ∨ (p5 ∨ p3)) → True))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h2
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_257265736260517505076965379831 : ((p2 ∨ p3) → (((((p5 ∧ p5) → (p1 ∨ p2)) → (False ∧ ((True ∧ p5) → p4))) ∨ (False → p1)) → ((((p2 ∧ p5) → p5) ∧ p4) ∨ True))) := by
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
      -- True on the right can always be proven directly.
      apply True.intro
    case inr h5 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- True on the right can always be proven directly.
      apply True.intro
  case inr h6 =>
    -- Disjunctions on the left can always be decomposed.
    cases h1
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
theorem thm_5_vars_661327142612909267960888915758 : (((((((False ∨ ((p5 ∧ True) ∧ (p1 ∨ ((p2 → p5) ∨ (p2 ∧ p2))))) → (p5 ∧ p1)) → (p4 ∧ False)) → (p2 → p3)) → (p4 → p4)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_173539115043236011146616233072 : ((((p5 ∨ (((p4 ∨ p2) ∨ p2) ∨ p2)) → (p5 ∨ (p1 ∧ (p1 → p4)))) ∧ p4) → ((((p5 → (p3 → (p1 ∨ p1))) ∨ False) ∨ p4) ∨ True)) := by
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
theorem thm_5_vars_691600954638636134854114029243 : ((((p2 ∧ ((p5 ∨ (p2 → p5)) ∨ (p5 → (((p4 ∨ p5) ∨ (p3 ∧ p4)) ∨ True)))) → (((False ∨ (p2 ∧ False)) ∧ p1) ∨ (p2 ∨ False))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_113535603326184223129171249965 : ((((p4 → ((p5 ∨ (p2 → p1)) → p5)) → (True ∧ ((p1 → (p3 ∨ (p2 → p5))) ∨ ((p3 ∨ True) ∨ p3)))) ∨ (p1 ∨ p1)) ∨ (p1 → p3)) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
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
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_686866687328532871084304691080 : ((((True ∨ (((p2 ∧ ((p1 ∧ p2) ∧ (p1 → ((p5 ∨ False) ∧ (p5 → False))))) ∧ p3) ∨ p1)) → ((p5 ∨ p2) ∨ (p4 → (True ∧ False)))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_341008856954166244183752708695 : (p2 → ((p1 ∧ (((((p3 ∨ ((((p1 ∧ p3) ∨ True) → p3) ∧ p5)) ∨ (p1 ∨ p3)) ∧ p4) → (p1 ∧ p4)) ∧ (p1 → (p4 ∧ p1)))) ∨ True)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_319546475050443073721599013770 : (p4 ∨ (((((p1 ∨ p5) → False) ∨ p5) ∧ (False ∨ (p3 ∧ p3))) ∨ (p1 ∨ (((((p2 → (p1 ∧ p3)) ∧ (p3 ∨ False)) ∧ p5) ∧ p1) → p3)))) := by
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
  let h4 := h2.left
  let h5 := h2.right
  -- Conjunctions on the left can always be decomposed.
  let h6 := h4.left
  let h7 := h4.right
  -- Disjunctions on the left can always be decomposed.
  cases h7
  case inl h8 =>
    -- One of the premise coincides with the conclusion.
    exact h8
  case inr h9 =>
    -- False on the left can always be used.
    apply False.elim h9



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_47007070544839348811032342945 : (((((p3 → False) ∨ ((False ∨ (p3 ∨ (False → ((p2 → (p2 ∨ (True ∨ p2))) ∧ ((p3 → p1) ∨ p1))))) ∧ p2)) → p4) ∨ (p3 → p3)) ∨ p4) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_40179596805034759652011089938 : (((((p2 → (True ∨ (True ∨ False))) ∧ ((p5 → (p5 ∨ ((False ∨ (p4 ∨ (p2 ∨ p5))) ∧ p4))) → (p5 ∨ (p5 ∨ p2)))) ∧ False) ∨ p1) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_258721335086758762670162917052 : ((True → True) → ((p4 ∨ ((p5 → p2) ∨ (False ∧ (((((p3 → True) → False) ∨ p3) ∧ (False → True)) → p3)))) ∨ (((p2 ∨ p2) ∨ p5) ∨ True))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_64722492863918781211086675180 : ((p1 ∨ (p4 → ((((p5 ∧ (p3 → p3)) ∨ ((p2 ∨ p2) ∨ True)) → (False ∨ True)) ∨ ((((p1 ∨ False) ∨ (p1 → p4)) ∧ p5) ∧ p4)))) ∨ p5) := by
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
  -- Disjunctions on the left can always be decomposed.
  cases h2
  case inl h3 =>
    -- Conjunctions on the left can always be decomposed.
    let h4 := h3.left
    let h5 := h3.right
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro
  case inr h6 =>
    -- Disjunctions on the left can always be decomposed.
    cases h6
    case inl h7 =>
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
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- True on the right can always be proven directly.
      apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_119948063973046128275054637159 : ((((((p4 → False) ∧ ((p2 → (((p3 → p4) → p3) ∧ p2)) → (p5 → (False ∧ False)))) → p1) → ((False ∧ True) ∧ p2)) ∧ p4) → (p5 ∧ p1)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
  have h4 : (((p4 → False) ∧ ((p2 → (((p3 → p4) → p3) ∧ p2)) → (p5 → (False ∧ False)))) → p1) := by
    -- Implications on the right can always be decomposed.
    intro h5
    -- Conjunctions on the left can always be decomposed.
    let h6 := h5.left
    let h7 := h5.right
    -- We want to use the implication h6 based on <expert-advice>. So we show its premise.
    have h8 : p4 := by
      -- One of the premise coincides with the conclusion.
      exact h3
    -- We have shown the premise of h6, we can now drive its conclusion.
    let h9 := h6 h8
    -- False on the left can always be used.
    apply False.elim h9
  -- We have shown the premise of h2, we can now drive its conclusion.
  let h10 := h2 h4
  -- We need to get the left conjuct of h10 based on <expert-advice>.
  let h11 := h10.left
  -- We need to get the left conjuct of h11 based on <expert-advice>.
  let h12 := h11.left
  -- False on the left can always be used.
  apply False.elim h12
  -- Conjunctions on the left can always be decomposed.
  let h13 := h1.left
  let h14 := h1.right
  -- We want to use the implication h13 based on <expert-advice>. So we show its premise.
  have h15 : (((p4 → False) ∧ ((p2 → (((p3 → p4) → p3) ∧ p2)) → (p5 → (False ∧ False)))) → p1) := by
    -- Implications on the right can always be decomposed.
    intro h16
    -- Conjunctions on the left can always be decomposed.
    let h17 := h16.left
    let h18 := h16.right
    -- We want to use the implication h17 based on <expert-advice>. So we show its premise.
    have h19 : p4 := by
      -- One of the premise coincides with the conclusion.
      exact h14
    -- We have shown the premise of h17, we can now drive its conclusion.
    let h20 := h17 h19
    -- False on the left can always be used.
    apply False.elim h20
  -- We have shown the premise of h13, we can now drive its conclusion.
  let h21 := h13 h15
  -- We need to get the left conjuct of h21 based on <expert-advice>.
  let h22 := h21.left
  -- We need to get the left conjuct of h22 based on <expert-advice>.
  let h23 := h22.left
  -- False on the left can always be used.
  apply False.elim h23



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_607783915253466778117882040996 : (((((p2 ∨ (p4 ∨ ((p5 → p2) → ((p3 → ((p3 ∧ p4) → (p1 ∧ ((p2 ∧ p2) → False)))) ∨ (p5 ∧ (p4 ∧ True)))))) ∧ p2) ∨ p1) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_151960648839541469369658649650 : (((((False ∧ (p1 ∧ (p4 ∧ (True ∧ p2)))) ∨ p3) ∨ (True ∧ p1)) ∨ (p5 ∨ ((p3 ∨ p4) ∧ (p5 → True)))) → (((p1 ∧ p4) ∧ False) ∨ True)) := by
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
        -- Conjunctions on the left can always be decomposed.
        let h5 := h4.left
        let h6 := h4.right
        -- False on the left can always be used.
        apply False.elim h5
      case inr h7 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- True on the right can always be proven directly.
        apply True.intro
    case inr h8 =>
      -- Conjunctions on the left can always be decomposed.
      let h9 := h8.left
      let h10 := h8.right
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- True on the right can always be proven directly.
      apply True.intro
  case inr h11 =>
    -- Disjunctions on the left can always be decomposed.
    cases h11
    case inl h12 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- True on the right can always be proven directly.
      apply True.intro
    case inr h13 =>
      -- Conjunctions on the left can always be decomposed.
      let h14 := h13.left
      let h15 := h13.right
      -- Disjunctions on the left can always be decomposed.
      cases h14
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



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_45317105572033138474327077304 : (((p3 ∧ ((p4 → (((((p5 → ((p2 ∨ p4) → p2)) ∧ ((True ∨ p5) → p5)) ∧ p5) ∨ (p1 → True)) ∨ p5)) ∨ (True ∧ p5))) → p5) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_173485925708437392993236014792 : (((((p3 ∨ (p4 → ((True → p2) ∧ p5))) ∨ ((p3 → p1) → False)) → p2) ∧ p1) → (p3 ∨ (((p1 ∨ True) → p3) → (p3 ∨ (True → False))))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h4
  -- We want to use the implication h4 based on <expert-advice>. So we show its premise.
  have h5 : (p1 ∨ True) := by
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h4, we can now drive its conclusion.
  let h6 := h4 h5
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- One of the premise coincides with the conclusion.
  exact h6



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_51265404234059039013677262806 : ((((True ∨ True) → ((((p1 ∨ p1) ∧ ((p1 ∨ False) ∧ p5)) ∧ (p3 ∧ p4)) ∧ (p1 → p5))) ∨ ((p2 ∧ (p1 → p5)) ∧ (p5 → p4))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_41610778667663990897434450877 : ((((p2 ∧ ((p5 ∧ (False ∧ (p3 ∧ True))) ∧ p2)) ∨ (((p1 ∨ p5) → p4) ∨ (((False ∧ False) ∨ False) ∧ (p5 ∧ (p5 ∨ True))))) ∨ p2) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_191829801531974356625636343912 : ((p3 ∨ ((False ∨ (p1 ∨ ((p1 → True) → p2))) ∨ p1)) ∨ ((p2 ∨ ((True ∨ True) ∨ p4)) ∨ (p3 ∨ ((p1 → p1) ∧ ((p5 ∨ p5) ∧ False))))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_684877175684771092485106330490 : ((((True ∧ (p1 ∨ (True → ((p4 ∧ (p2 ∨ ((False ∨ True) ∧ (p4 → (p4 → p5))))) ∨ p3)))) ∨ ((p5 ∨ p3) ∨ ((True ∨ p1) ∧ p3))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_689431255040224230748040989946 : (((((((p4 ∨ p2) ∧ False) ∨ (p5 ∧ (p5 ∨ (p5 ∧ p1)))) ∧ ((False → False) → True)) ∨ (p1 → (False → (True ∧ ((p4 ∧ p3) ∧ p3))))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_43882201773779705314671679328 : ((((p1 ∧ (True ∧ (((p4 ∨ True) → False) ∧ (False ∨ (((True → p4) ∨ (p3 ∧ p4)) → (p5 ∧ (p4 ∨ p1))))))) ∧ (False → True)) → p3) ∨ p5) := by
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
  -- Conjunctions on the left can always be decomposed.
  let h6 := h5.left
  let h7 := h5.right
  -- Conjunctions on the left can always be decomposed.
  let h8 := h7.left
  let h9 := h7.right
  -- Disjunctions on the left can always be decomposed.
  cases h9
  case inl h10 =>
    -- False on the left can always be used.
    apply False.elim h10
  case inr h11 =>
    -- We want to use the implication h8 based on <expert-advice>. So we show its premise.
    have h12 : (p4 ∨ True) := by
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- True on the right can always be proven directly.
      apply True.intro
    -- We have shown the premise of h8, we can now drive its conclusion.
    let h13 := h8 h12
    -- False on the left can always be used.
    apply False.elim h13



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_207428599532207632107367698627 : (((p1 ∨ ((p2 ∨ p2) ∧ p3)) ∨ True) → (((p3 ∧ (True → p2)) ∨ False) ∨ (((((p1 ∧ p3) → p4) ∧ (p4 ∧ (False ∧ True))) → p4) ∨ p4))) := by
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
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- Implications on the right can always be decomposed.
      intro h4
      -- Conjunctions on the left can always be decomposed.
      let h5 := h4.left
      let h6 := h4.right
      -- Conjunctions on the left can always be decomposed.
      let h7 := h6.left
      let h8 := h6.right
      -- Conjunctions on the left can always be decomposed.
      let h9 := h8.left
      let h10 := h8.right
      -- False on the left can always be used.
      apply False.elim h9
    case inr h11 =>
      -- Conjunctions on the left can always be decomposed.
      let h12 := h11.left
      let h13 := h11.right
      -- Disjunctions on the left can always be decomposed.
      cases h12
      case inl h14 =>
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- Conjunctions on the right can always be decomposed.
        apply And.intro
        -- One of the premise coincides with the conclusion.
        exact h13
        -- Implications on the right can always be decomposed.
        intro h15
        -- One of the premise coincides with the conclusion.
        exact h14
      case inr h16 =>
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- Conjunctions on the right can always be decomposed.
        apply And.intro
        -- One of the premise coincides with the conclusion.
        exact h13
        -- Implications on the right can always be decomposed.
        intro h17
        -- One of the premise coincides with the conclusion.
        exact h16
  case inr h18 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Implications on the right can always be decomposed.
    intro h19
    -- Conjunctions on the left can always be decomposed.
    let h20 := h19.left
    let h21 := h19.right
    -- Conjunctions on the left can always be decomposed.
    let h22 := h21.left
    let h23 := h21.right
    -- Conjunctions on the left can always be decomposed.
    let h24 := h23.left
    let h25 := h23.right
    -- False on the left can always be used.
    apply False.elim h24



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_650619216879281309755442238248 : ((((((((p4 ∨ p3) → True) ∧ (p2 ∧ p5)) → (p1 ∨ p3)) ∧ ((True ∨ (True → False)) ∨ (((False → p2) ∧ False) ∨ p4))) ∧ (p5 ∨ p5)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_321712627636405521671435439740 : (p4 ∨ (p5 → ((((((p1 ∧ p5) → ((p2 ∧ (((True → p2) → p3) ∨ (True ∨ p3))) ∧ p3)) → p4) ∨ p5) ∨ ((p3 ∧ p2) ∧ True)) ∧ True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
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
theorem thm_5_vars_242548179858438998532215811463 : ((p3 → True) ∧ ((((((p3 → (p1 ∧ p2)) ∨ (p1 ∧ (p2 ∧ p2))) ∨ p5) ∨ (p3 ∨ ((p3 ∧ (p2 ∧ p4)) ∨ (p4 ∧ p4)))) ∨ True) ∨ p4)) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_67731853639242245328473265556 : ((p2 → (((True ∨ (p5 ∧ p2)) → (((p5 → False) ∧ ((True ∨ p2) ∧ (((p2 → p4) → (p3 ∨ p1)) → p2))) ∧ (p4 → p1))) ∧ p2)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_161419654032926647004547496498 : ((p2 ∧ ((False ∨ (p2 ∨ ((True ∨ p5) → (((p1 ∨ (p4 ∨ p3)) ∧ (p4 ∧ p3)) ∨ True)))) ∨ p5)) → (p2 → (p3 ∨ (p4 ∨ (True ∧ True))))) := by
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
      -- False on the left can always be used.
      apply False.elim h6
    case inr h7 =>
      -- Disjunctions on the left can always be decomposed.
      cases h7
      case inl h8 =>
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
      case inr h9 =>
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
  case inr h10 =>
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
theorem thm_5_vars_124419884118058494546403633798 : ((((((p4 ∨ False) ∧ False) ∨ (p3 → False)) ∨ True) → (False ∧ (((p3 → ((True → p1) ∧ p5)) → p5) ∧ ((p1 → p5) ∧ p4)))) → (False ∨ False)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h2 : ((((p4 ∨ False) ∧ False) ∨ (p3 → False)) ∨ True) := by
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h3 := h1 h2
  -- We need to get the left conjuct of h3 based on <expert-advice>.
  let h4 := h3.left
  -- False on the left can always be used.
  apply False.elim h4



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_179460025027102733269209616634 : ((p5 ∨ (p2 ∧ ((((False ∧ p5) ∧ (False ∧ p3)) ∨ True) → (p1 ∨ p1)))) ∨ (((p3 → (False ∧ p4)) ∨ (p4 → p3)) ∨ (p4 → (False → p3)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- False on the left can always be used.
  apply False.elim h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_138389041380618494106553780644 : ((p4 → (p3 ∧ (False ∨ (p4 ∧ (True → (((p2 → False) ∨ (True → ((p4 ∨ (p5 → (p1 → True))) ∧ p1))) ∨ False)))))) ∨ ((p1 → False) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_263390460272017185532399946019 : (True ∧ (((((True → ((True ∨ (p2 ∨ p1)) → p4)) → p2) → (((p2 ∧ p1) → p5) → (True → True))) → (p1 ∧ True)) ∨ (False ∨ (p5 → p5)))) := by
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
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_134372385579013190711647635776 : (((p2 ∨ (False ∨ ((p2 ∨ (((p4 ∨ p4) → p4) ∧ (False ∧ (p5 ∧ (p1 → (p4 → p3)))))) ∧ (False ∧ p5)))) ∨ True) ∨ (p1 ∨ (p1 → True))) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_42130635121835657878576839870 : ((((p2 ∨ True) → ((p4 ∨ (((p3 ∧ ((p4 ∨ p2) → p3)) ∨ p5) ∧ ((p4 ∧ (p1 → p3)) ∨ p3))) → ((p2 ∨ p4) ∧ p4))) ∨ p5) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_47448513389305504881424038023 : (((p3 ∧ (p2 ∨ ((False ∨ p4) → (True ∧ (p4 → (((p4 → p5) ∧ (((p1 ∨ (p4 ∧ False)) → p1) ∨ p5)) → p3)))))) ∨ (p4 ∨ True)) ∨ p3) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_116606942957958287782106193846 : (((True → p1) ∧ ((p2 ∨ ((((False ∧ (p1 → p5)) ∧ (p3 ∧ (p3 ∧ p2))) ∧ (p5 → True)) ∧ (p1 ∨ p2))) ∨ (p2 → p5))) ∨ (True → True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_753603954358754830846138564556 : (((False ∧ ((p5 ∨ ((((p2 ∧ (p3 ∨ (p5 → p1))) ∨ (False ∧ (False ∧ True))) ∧ False) → p2)) ∧ ((p1 ∨ p1) → ((p3 → False) ∨ p5)))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_673286321428578509783840735866 : (((((True ∨ (((True ∧ p4) ∧ (False ∧ p1)) → True)) ∨ ((p4 → True) ∧ (((False ∨ p3) ∧ (p2 ∧ p4)) → p5))) → ((p2 → p1) ∨ p1)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_600813216408868967812895148534 : ((((False ∧ (p1 ∧ (p4 ∧ (p1 ∨ (p2 ∧ (p4 ∧ ((p2 → (p2 ∨ (p1 ∨ False))) ∧ (p5 ∨ (((p2 ∧ p2) ∧ p4) ∧ p4))))))))) ∧ False) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_113075566725586778752815599557 : (((p3 ∨ (False → ((((p4 → (p2 → p3)) ∨ (False ∨ ((False ∧ p2) ∨ False))) ∨ ((p4 ∨ (p4 ∧ False)) ∧ True)) ∧ p2))) → False) ∨ (True ∨ p4)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_135409797527055110759646397723 : ((((p4 ∨ (p4 ∧ p3)) ∧ ((True ∨ True) → ((False ∧ p1) → (True → ((False ∨ p1) ∧ p3))))) ∨ ((p5 → p1) → p3)) ∨ ((True → False) → p5)) := by
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
theorem thm_5_vars_60464811112661898790574937742 : (((p5 → p3) → ((p4 ∧ ((True ∨ (p3 → p3)) ∧ (p5 ∧ (((True → p4) ∧ ((p3 ∧ (True ∨ p4)) ∧ True)) ∧ p3)))) ∧ (p1 ∧ False))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_672666152688368209676976927039 : (((((((p5 → p1) ∧ (p1 ∧ False)) ∨ ((p1 ∧ p5) → (((False ∧ True) ∨ True) ∧ (p1 → p4)))) ∨ (True → p5)) → ((True → False) ∧ p1)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_165905133009056041588038914394 : (((p4 ∨ (p4 ∨ True)) → (((p1 → p5) ∨ (((False ∨ p4) ∧ p1) ∧ p2)) ∧ (False ∨ True))) ∨ ((p3 ∧ (True → p3)) → ((True ∨ p3) ∧ True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
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
theorem thm_5_vars_53414143364460461708037340764 : ((((((False → p3) → False) → (p2 ∧ p2)) ∧ ((False ∨ True) → p5)) → ((((True ∨ (True ∧ (p3 → p3))) → (p3 → True)) ∧ p4) → p2)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_520431103430276545645356596777 : ((((p4 ∨ p1) → (p3 → ((((p3 ∨ p4) → False) ∧ p1) ∨ (False → (((False ∧ (False ∨ (False ∧ (p1 ∨ p5)))) ∨ p3) → (False → p3)))))) ∧ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h3 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h4
    -- Implications on the right can always be decomposed.
    intro h5
    -- Implications on the right can always be decomposed.
    intro h6
    -- False on the left can always be used.
    apply False.elim h6
  case inr h7 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h8
    -- Implications on the right can always be decomposed.
    intro h9
    -- Implications on the right can always be decomposed.
    intro h10
    -- False on the left can always be used.
    apply False.elim h10
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_785136800767845501135751602235 : (((p4 ∨ (((((True → (p2 ∧ (p4 ∨ ((((p1 ∨ p2) → p2) → False) ∧ p3)))) → p4) ∧ (p1 → p1)) ∨ ((p1 → p2) ∨ p5)) ∧ p1)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_190897867148986001233040721630 : (((False ∨ ((True ∨ (True ∨ True)) ∧ p5)) → (p5 → p4)) ∨ ((((p5 ∨ p3) ∨ ((p2 ∧ ((p1 → (p4 → False)) ∧ p2)) ∧ p5)) ∨ True) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_842500858236991703271691412201 : (((((((p2 → (p1 ∨ (False ∨ (p1 ∧ p1)))) ∨ ((p3 → True) → False)) → True) → ((p3 ∧ ((p1 ∨ (p4 → p2)) ∧ p1)) ∧ p2)) ∨ p1) → p1) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h1
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h2 =>
    -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
    have h3 : (((p2 → (p1 ∨ (False ∨ (p1 ∧ p1)))) ∨ ((p3 → True) → False)) → True) := by
      -- Implications on the right can always be decomposed.
      intro h4
      -- True on the right can always be proven directly.
      apply True.intro
    -- We have shown the premise of h2, we can now drive its conclusion.
    let h5 := h2 h3
    -- We need to get the left conjuct of h5 based on <expert-advice>.
    let h6 := h5.left
    -- We need to get the right conjuct of h6 based on <expert-advice>.
    let h7 := h6.right
    -- We need to get the right conjuct of h7 based on <expert-advice>.
    let h8 := h7.right
    -- One of the premise coincides with the conclusion.
    exact h8
  case inr h9 =>
    -- One of the premise coincides with the conclusion.
    exact h9
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_173520941963137269532672663343 : ((((p4 → ((False → ((p2 ∧ p1) ∧ p3)) ∧ p2)) ∧ ((p2 → p1) ∧ p1)) ∧ p1) → ((((False → p2) ∧ p4) → (p4 ∧ False)) ∨ (True ∨ p5))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- Conjunctions on the left can always be decomposed.
  let h4 := h2.left
  let h5 := h2.right
  -- Conjunctions on the left can always be decomposed.
  let h6 := h5.left
  let h7 := h5.right
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_339478854468945181518494615469 : (p1 → (False ∨ ((p3 ∨ (((p5 ∨ False) ∨ ((p4 ∧ (p5 → p2)) ∧ (True → (p1 ∧ p5)))) → (((False ∨ (True → p2)) → p3) → p5))) ∧ p1))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h2
  -- Implications on the right can always be decomposed.
  intro h3
  -- Disjunctions on the left can always be decomposed.
  cases h2
  case inl h4 =>
    -- Disjunctions on the left can always be decomposed.
    cases h4
    case inl h5 =>
      -- One of the premise coincides with the conclusion.
      exact h5
    case inr h6 =>
      -- False on the left can always be used.
      apply False.elim h6
  case inr h7 =>
    -- Conjunctions on the left can always be decomposed.
    let h8 := h7.left
    let h9 := h7.right
    -- Conjunctions on the left can always be decomposed.
    let h10 := h8.left
    let h11 := h8.right
    -- We want to use the implication h9 based on <expert-advice>. So we show its premise.
    have h12 : True := by
      -- True on the right can always be proven directly.
      apply True.intro
    -- We have shown the premise of h9, we can now drive its conclusion.
    let h13 := h9 h12
    -- We need to get the right conjuct of h13 based on <expert-advice>.
    let h14 := h13.right
    -- One of the premise coincides with the conclusion.
    exact h14
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_147320812274480620132997400916 : ((((p4 → (p2 ∧ ((((((False ∨ True) ∨ False) → False) ∧ p1) ∧ True) ∨ (p5 → (False ∨ True))))) → p5) ∨ True) ∨ (((p2 → p5) → True) ∧ False)) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_205853180644310196161920585823 : (((p3 → p3) → (p4 ∨ (p3 ∧ p1))) ∨ ((False ∧ (False → p2)) ∨ ((((p1 ∨ (p3 → p3)) ∨ (True → True)) ∧ True) ∨ ((p2 ∧ False) → True)))) := by
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
theorem thm_5_vars_43955819977592002130946436477 : (((((p5 ∨ p5) → (((True ∧ (p4 → ((p5 ∨ (p2 → (p5 ∨ ((p2 → False) → p4)))) ∧ p3))) ∨ True) ∨ p3)) ∨ (p2 → p4)) → p4) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_66367993783039903782118021690 : ((p5 ∨ (p1 ∨ ((p2 ∨ p1) → ((True → ((True ∧ False) ∧ (p4 ∨ (p5 ∨ ((True → p3) ∨ ((p3 ∧ p4) → p1)))))) → (p2 ∨ False))))) ∨ False) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
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
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- One of the premise coincides with the conclusion.
    exact h3
  case inr h4 =>
    -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
    have h5 : True := by
      -- True on the right can always be proven directly.
      apply True.intro
    -- We have shown the premise of h2, we can now drive its conclusion.
    let h6 := h2 h5
    -- We need to get the left conjuct of h6 based on <expert-advice>.
    let h7 := h6.left
    -- We need to get the right conjuct of h7 based on <expert-advice>.
    let h8 := h7.right
    -- False on the left can always be used.
    apply False.elim h8



