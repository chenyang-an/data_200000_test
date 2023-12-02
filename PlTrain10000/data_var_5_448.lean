variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_114080507558532329234089126105 : ((((p4 ∧ (p4 ∧ True)) ∨ (((p1 → p5) → (True ∧ ((p3 → (p5 → False)) ∨ (p4 ∧ p1)))) → p4)) ∨ ((p4 → p1) ∨ p4)) ∨ (p4 → p4)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_978582376135578089339432643983 : (((True ∧ (True → (p1 ∧ ((True → (((((p1 → p4) ∧ False) → (((p4 → p1) ∧ p3) ∧ False)) ∨ p3) ∧ ((p5 ∨ False) → p2))) ∧ p3)))) → p3) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- We want to use the implication h3 based on <expert-advice>. So we show its premise.
  have h4 : True := by
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h3, we can now drive its conclusion.
  let h5 := h3 h4
  -- We need to get the right conjuct of h5 based on <expert-advice>.
  let h6 := h5.right
  -- We need to get the right conjuct of h6 based on <expert-advice>.
  let h7 := h6.right
  -- One of the premise coincides with the conclusion.
  exact h7
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_114176964570383950376755387473 : ((((((((p1 ∨ (p2 → ((p4 ∧ p3) ∧ p1))) ∨ p3) ∧ (p3 → p2)) ∨ True) → p1) → (p3 → p1)) → ((False ∧ p1) ∨ p2)) ∨ (True → True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_809335840047252057715538284061 : (((p5 → ((p5 ∧ ((p4 ∨ ((p4 → p2) → (((p2 ∨ p4) → (p3 ∨ ((p1 ∧ p4) ∧ p2))) → False))) ∧ (p5 ∨ (p2 → p5)))) ∨ p4)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_699437203699578254100604218 : ((((p2 ∧ (p5 ∨ ((False ∧ (p2 → True)) ∧ False))) ∧ True) ∧ (p3 ∧ ((False → (p3 → ((p5 → False) → p2))) → (True → True)))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_697762873954666049831196312249 : ((((p2 → ((p4 ∨ False) → ((((p1 ∧ p1) ∧ p5) ∨ p2) ∨ p3))) ∧ ((((True → False) → True) ∧ p1) ∧ (p4 → ((False ∨ p1) → p3)))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_158747979132728405251078987955 : ((p4 ∧ (((((((p1 ∧ (p4 ∨ p1)) ∧ p3) ∨ p3) → p4) ∧ ((False ∧ p1) → True)) ∧ p1) → p2)) ∨ (((False → (p1 → True)) ∨ False) ∨ p4)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_206448254629021690209313599189 : ((p4 ∨ ((False ∨ p4) ∧ (p3 → p3))) ∨ (((False → False) → ((p1 ∨ (((p5 → p1) ∨ p3) → (False ∧ True))) ∨ ((p2 ∨ p1) → p1))) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_322296814585920051464852748413 : (p5 ∨ ((((p2 ∨ ((p5 ∧ (p3 ∧ p3)) → p3)) ∨ ((p4 → ((((p5 → p2) ∨ p2) ∧ (p1 ∧ (False ∧ p2))) ∧ p4)) → p4)) → p4) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_301949798671960228729014811189 : (False ∨ ((p3 ∨ p1) → (p2 ∨ ((p5 ∨ True) ∨ (((p2 ∧ ((p5 ∨ (False ∨ p2)) ∧ True)) ∨ p1) ∧ (((False ∧ p5) ∨ True) → (False → p5))))))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h2 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro
  case inr h3 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_37372505412569326345360974640 : (((((p4 → (p5 ∨ (((p4 ∨ (p5 ∨ (p5 ∧ (False → (p5 → p1))))) ∧ (p2 ∧ p2)) ∧ ((p4 → p3) → p2)))) ∨ p1) ∨ True) ∧ True) ∨ p1) := by
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
theorem thm_5_vars_59245312739531229140120046154 : (((p2 ∨ p3) ∨ ((((p4 ∨ (True → ((True → (p1 → ((p4 ∨ p5) ∧ p1))) → True))) → p1) → p5) → ((p2 ∨ p3) ∨ (p3 → p2)))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_113239142697219783399256348786 : ((((True → (((p3 ∨ (False → p1)) → True) → (True → ((p3 ∧ p1) ∨ (p1 ∧ ((p5 → True) ∧ p5)))))) → p5) ∧ (False ∨ p5)) ∨ (False → True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_53382634646962796621002767693 : ((((((True ∧ p5) ∨ p1) → (False ∨ ((p4 ∨ True) → p1))) → False) → ((p3 ∧ True) → (p1 ∧ ((((p5 ∧ True) → p1) ∧ p1) ∧ False)))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_200107022395928482673258688544 : (((p1 ∧ (True → False)) ∧ ((p3 ∨ p3) ∨ p3)) → (((p1 ∨ (p3 ∨ (p5 ∧ True))) → p5) ∧ (((p5 ∨ (True ∧ p1)) ∨ (p2 → False)) → p2))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h2
  -- Disjunctions on the left can always be decomposed.
  cases h2
  case inl h3 =>
    -- Conjunctions on the left can always be decomposed.
    let h4 := h1.left
    let h5 := h1.right
    -- Conjunctions on the left can always be decomposed.
    let h6 := h4.left
    let h7 := h4.right
    -- Disjunctions on the left can always be decomposed.
    cases h5
    case inl h8 =>
      -- Disjunctions on the left can always be decomposed.
      cases h8
      case inl h9 =>
        -- We want to use the implication h7 based on <expert-advice>. So we show its premise.
        have h10 : True := by
          -- True on the right can always be proven directly.
          apply True.intro
        -- We have shown the premise of h7, we can now drive its conclusion.
        let h11 := h7 h10
        -- False on the left can always be used.
        apply False.elim h11
      case inr h12 =>
        -- We want to use the implication h7 based on <expert-advice>. So we show its premise.
        have h13 : True := by
          -- True on the right can always be proven directly.
          apply True.intro
        -- We have shown the premise of h7, we can now drive its conclusion.
        let h14 := h7 h13
        -- False on the left can always be used.
        apply False.elim h14
    case inr h15 =>
      -- We want to use the implication h7 based on <expert-advice>. So we show its premise.
      have h16 : True := by
        -- True on the right can always be proven directly.
        apply True.intro
      -- We have shown the premise of h7, we can now drive its conclusion.
      let h17 := h7 h16
      -- False on the left can always be used.
      apply False.elim h17
  case inr h18 =>
    -- Disjunctions on the left can always be decomposed.
    cases h18
    case inl h19 =>
      -- Conjunctions on the left can always be decomposed.
      let h20 := h1.left
      let h21 := h1.right
      -- Conjunctions on the left can always be decomposed.
      let h22 := h20.left
      let h23 := h20.right
      -- Disjunctions on the left can always be decomposed.
      cases h21
      case inl h24 =>
        -- Disjunctions on the left can always be decomposed.
        cases h24
        case inl h25 =>
          -- We want to use the implication h23 based on <expert-advice>. So we show its premise.
          have h26 : True := by
            -- True on the right can always be proven directly.
            apply True.intro
          -- We have shown the premise of h23, we can now drive its conclusion.
          let h27 := h23 h26
          -- False on the left can always be used.
          apply False.elim h27
        case inr h28 =>
          -- We want to use the implication h23 based on <expert-advice>. So we show its premise.
          have h29 : True := by
            -- True on the right can always be proven directly.
            apply True.intro
          -- We have shown the premise of h23, we can now drive its conclusion.
          let h30 := h23 h29
          -- False on the left can always be used.
          apply False.elim h30
      case inr h31 =>
        -- We want to use the implication h23 based on <expert-advice>. So we show its premise.
        have h32 : True := by
          -- True on the right can always be proven directly.
          apply True.intro
        -- We have shown the premise of h23, we can now drive its conclusion.
        let h33 := h23 h32
        -- False on the left can always be used.
        apply False.elim h33
    case inr h34 =>
      -- Conjunctions on the left can always be decomposed.
      let h35 := h34.left
      let h36 := h34.right
      -- Conjunctions on the left can always be decomposed.
      let h37 := h1.left
      let h38 := h1.right
      -- Conjunctions on the left can always be decomposed.
      let h39 := h37.left
      let h40 := h37.right
      -- Disjunctions on the left can always be decomposed.
      cases h38
      case inl h41 =>
        -- Disjunctions on the left can always be decomposed.
        cases h41
        case inl h42 =>
          -- One of the premise coincides with the conclusion.
          exact h35
        case inr h43 =>
          -- One of the premise coincides with the conclusion.
          exact h35
      case inr h44 =>
        -- One of the premise coincides with the conclusion.
        exact h35
  -- Implications on the right can always be decomposed.
  intro h45
  -- Disjunctions on the left can always be decomposed.
  cases h45
  case inl h46 =>
    -- Disjunctions on the left can always be decomposed.
    cases h46
    case inl h47 =>
      -- Conjunctions on the left can always be decomposed.
      let h48 := h1.left
      let h49 := h1.right
      -- Conjunctions on the left can always be decomposed.
      let h50 := h48.left
      let h51 := h48.right
      -- Disjunctions on the left can always be decomposed.
      cases h49
      case inl h52 =>
        -- Disjunctions on the left can always be decomposed.
        cases h52
        case inl h53 =>
          -- We want to use the implication h51 based on <expert-advice>. So we show its premise.
          have h54 : True := by
            -- True on the right can always be proven directly.
            apply True.intro
          -- We have shown the premise of h51, we can now drive its conclusion.
          let h55 := h51 h54
          -- False on the left can always be used.
          apply False.elim h55
        case inr h56 =>
          -- We want to use the implication h51 based on <expert-advice>. So we show its premise.
          have h57 : True := by
            -- True on the right can always be proven directly.
            apply True.intro
          -- We have shown the premise of h51, we can now drive its conclusion.
          let h58 := h51 h57
          -- False on the left can always be used.
          apply False.elim h58
      case inr h59 =>
        -- We want to use the implication h51 based on <expert-advice>. So we show its premise.
        have h60 : True := by
          -- True on the right can always be proven directly.
          apply True.intro
        -- We have shown the premise of h51, we can now drive its conclusion.
        let h61 := h51 h60
        -- False on the left can always be used.
        apply False.elim h61
    case inr h62 =>
      -- Conjunctions on the left can always be decomposed.
      let h63 := h62.left
      let h64 := h62.right
      -- Conjunctions on the left can always be decomposed.
      let h65 := h1.left
      let h66 := h1.right
      -- Conjunctions on the left can always be decomposed.
      let h67 := h65.left
      let h68 := h65.right
      -- Disjunctions on the left can always be decomposed.
      cases h66
      case inl h69 =>
        -- Disjunctions on the left can always be decomposed.
        cases h69
        case inl h70 =>
          -- We want to use the implication h68 based on <expert-advice>. So we show its premise.
          have h71 : True := by
            -- True on the right can always be proven directly.
            apply True.intro
          -- We have shown the premise of h68, we can now drive its conclusion.
          let h72 := h68 h71
          -- False on the left can always be used.
          apply False.elim h72
        case inr h73 =>
          -- We want to use the implication h68 based on <expert-advice>. So we show its premise.
          have h74 : True := by
            -- True on the right can always be proven directly.
            apply True.intro
          -- We have shown the premise of h68, we can now drive its conclusion.
          let h75 := h68 h74
          -- False on the left can always be used.
          apply False.elim h75
      case inr h76 =>
        -- We want to use the implication h68 based on <expert-advice>. So we show its premise.
        have h77 : True := by
          -- True on the right can always be proven directly.
          apply True.intro
        -- We have shown the premise of h68, we can now drive its conclusion.
        let h78 := h68 h77
        -- False on the left can always be used.
        apply False.elim h78
  case inr h79 =>
    -- Conjunctions on the left can always be decomposed.
    let h80 := h1.left
    let h81 := h1.right
    -- Conjunctions on the left can always be decomposed.
    let h82 := h80.left
    let h83 := h80.right
    -- Disjunctions on the left can always be decomposed.
    cases h81
    case inl h84 =>
      -- Disjunctions on the left can always be decomposed.
      cases h84
      case inl h85 =>
        -- We want to use the implication h83 based on <expert-advice>. So we show its premise.
        have h86 : True := by
          -- True on the right can always be proven directly.
          apply True.intro
        -- We have shown the premise of h83, we can now drive its conclusion.
        let h87 := h83 h86
        -- False on the left can always be used.
        apply False.elim h87
      case inr h88 =>
        -- We want to use the implication h83 based on <expert-advice>. So we show its premise.
        have h89 : True := by
          -- True on the right can always be proven directly.
          apply True.intro
        -- We have shown the premise of h83, we can now drive its conclusion.
        let h90 := h83 h89
        -- False on the left can always be used.
        apply False.elim h90
    case inr h91 =>
      -- We want to use the implication h83 based on <expert-advice>. So we show its premise.
      have h92 : True := by
        -- True on the right can always be proven directly.
        apply True.intro
      -- We have shown the premise of h83, we can now drive its conclusion.
      let h93 := h83 h92
      -- False on the left can always be used.
      apply False.elim h93



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_140559693111518126099163749316 : (((((True ∧ True) ∨ p3) ∧ ((True → (((p3 ∨ p1) ∧ False) ∧ p5)) → (p1 → True))) ∨ (p1 ∧ ((p3 ∨ p2) ∧ p1))) → ((p4 → p3) ∨ True)) := by
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
  case inr h9 =>
    -- Conjunctions on the left can always be decomposed.
    let h10 := h9.left
    let h11 := h9.right
    -- Conjunctions on the left can always be decomposed.
    let h12 := h11.left
    let h13 := h11.right
    -- Disjunctions on the left can always be decomposed.
    cases h12
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



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_231086285132240469290712620981 : (((False ∨ p1) ∨ p3) → ((((((((p4 → p4) ∨ p3) ∨ p3) ∨ p1) → p5) → (((((True ∧ p4) → True) ∨ False) → p1) ∧ p2)) ∨ p4) ∨ True)) := by
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
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_66819407611169041063771103876 : ((True → (True → (((False → p2) → (False ∨ ((True → p3) ∧ ((((p2 ∧ (p2 → False)) → p1) ∧ p1) ∧ p3)))) ∨ (False ∧ (False → p3))))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_618179485461872400084932555530 : (((((p4 → ((p4 ∨ False) ∧ p2)) ∧ (p2 ∨ (p4 ∨ (((p1 ∧ ((False ∨ True) → p3)) → p2) ∨ (((p3 → False) ∨ p1) ∨ p5))))) ∨ p2) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_52117562714742022930749491341 : (((((((p2 ∧ p1) ∧ (p1 ∨ p3)) → True) → (p2 → ((False → True) ∨ p4))) → p4) → (((p4 ∧ (p2 ∨ True)) ∨ (p4 ∨ p1)) ∨ p3)) ∨ p5) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h2 : ((((p2 ∧ p1) ∧ (p1 ∨ p3)) → True) → (p2 → ((False → True) ∨ p4))) := by
    -- Implications on the right can always be decomposed.
    intro h3
    -- Implications on the right can always be decomposed.
    intro h4
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Implications on the right can always be decomposed.
    intro h5
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h6 := h1 h2
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- One of the premise coincides with the conclusion.
  exact h6



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_174960701882455625302106231837 : ((True ∧ ((p4 ∨ ((False ∨ p1) → (True ∨ True))) ∧ ((p1 ∨ p5) → (p3 → True)))) → (p4 ∨ (True ∧ ((((True ∧ p4) → p3) ∧ False) ∨ True)))) := by
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
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- One of the premise coincides with the conclusion.
    exact h6
  case inr h7 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Conjunctions on the right can always be decomposed.
    apply And.intro
    -- True on the right can always be proven directly.
    apply True.intro
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_44490604074135535028960199442 : (((((((True → (p1 ∨ False)) ∧ p2) ∨ (p1 → p2)) → p5) ∧ (p4 → (p5 → ((False ∨ (p2 ∨ p2)) ∧ ((p1 → p1) ∨ False))))) → p1) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_190234161484723204199556418843 : ((((((p1 ∨ p5) ∧ (p2 → True)) ∧ False) ∧ False) ∨ p4) ∨ (((False ∧ p5) → (p5 → p2)) → (p2 → (p4 → (p2 ∨ ((p1 → p4) → True)))))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Implications on the right can always be decomposed.
  intro h3
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- One of the premise coincides with the conclusion.
  exact h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_231705187519750553565476770382 : (((p2 ∧ True) → p3) → ((p5 → ((p2 ∨ p4) ∨ (False ∧ False))) ∨ ((((False ∧ p5) ∧ (False → p3)) → p3) ∧ (p5 → (p3 ∨ (p1 → p5)))))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h2
  -- Conjunctions on the left can always be decomposed.
  let h3 := h2.left
  let h4 := h2.right
  -- Conjunctions on the left can always be decomposed.
  let h5 := h3.left
  let h6 := h3.right
  -- False on the left can always be used.
  apply False.elim h5
  -- Implications on the right can always be decomposed.
  intro h7
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h8
  -- One of the premise coincides with the conclusion.
  exact h7



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_342393856661078882832083134209 : (p2 → (((False ∨ (p1 → (p2 → False))) ∨ (p5 → ((p3 ∧ (False → (p1 ∧ p2))) → False))) ∨ ((False ∧ (False ∨ ((p5 ∨ p1) ∨ p4))) ∨ True))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_124999341225915023500746776900 : ((((True → p5) ∧ p5) ∧ (((p5 ∨ p1) ∨ ((False → (p3 ∧ (((True ∧ p5) ∨ p4) → p2))) ∧ (p1 ∧ p5))) → (p4 ∨ p2))) → (p2 ∨ p5)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- Conjunctions on the left can always be decomposed.
  let h4 := h2.left
  let h5 := h2.right
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h5



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_354931479511056673880897626048 : (p5 → ((p3 ∨ (p3 ∨ ((p4 ∧ p3) ∧ (((False ∧ ((((p2 → (p4 ∨ (p2 ∧ (p3 ∧ p1)))) ∨ False) → p5) ∧ p5)) ∧ p1) ∨ True)))) ∨ True)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_587989060750603885109474520041 : ((((((p1 ∨ (True ∨ (p5 ∧ ((p5 → (p4 ∨ (True → ((p3 ∧ p1) ∧ (False ∨ True))))) ∧ p1)))) → (p1 ∨ (p1 ∨ p1))) ∨ p1) ∧ p5) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_646117971218115029280474763061 : ((((True → (p4 → (p1 ∧ ((((((True ∧ p5) → (True ∨ True)) ∧ (p2 → ((True ∧ p3) → (p4 ∧ False)))) ∨ True) ∨ True) ∧ p2)))) → False) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_231602076575376885893955299088 : (((True ∧ p2) → p1) → (((p3 → (((((((False → (p2 → p5)) ∨ p1) → p5) ∨ True) ∨ (p1 ∧ p2)) ∧ (True ∧ False)) ∧ p3)) ∧ p3) → p4)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Conjunctions on the left can always be decomposed.
  let h3 := h2.left
  let h4 := h2.right
  -- We want to use the implication h3 based on <expert-advice>. So we show its premise.
  have h5 : p3 := by
    -- One of the premise coincides with the conclusion.
    exact h4
  -- We have shown the premise of h3, we can now drive its conclusion.
  let h6 := h3 h5
  -- We need to get the left conjuct of h6 based on <expert-advice>.
  let h7 := h6.left
  -- We need to get the right conjuct of h7 based on <expert-advice>.
  let h8 := h7.right
  -- We need to get the right conjuct of h8 based on <expert-advice>.
  let h9 := h8.right
  -- False on the left can always be used.
  apply False.elim h9



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_202204496433031135256556897526 : ((((p5 → p4) → (p5 ∨ p4)) → True) ∧ ((p2 ∧ (True → (p2 ∧ ((p5 ∨ (p1 → (p3 → True))) ∧ ((p4 ∨ (True → p2)) ∧ p3))))) ∨ True)) := by
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
theorem thm_5_vars_111868546335470760568589496597 : (((((p3 ∧ ((((False ∧ (p3 ∧ p3)) ∧ True) ∨ (p1 → p3)) ∨ False)) ∧ (p1 → p5)) ∨ (((p5 ∨ p4) → False) ∧ p4)) ∨ True) ∨ (p1 ∧ p5)) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_114426051270096712728680434482 : (((p1 ∧ (p1 → ((((((((False → True) ∧ p3) → True) ∨ True) ∧ p2) ∧ p1) ∧ p1) → False))) ∨ ((p1 → (False → p4)) ∨ p4)) ∨ (p1 ∧ p5)) := by
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
  -- False on the left can always be used.
  apply False.elim h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_725703522766880214484780224169 : (((((False ∨ p2) ∧ p3) ∨ ((p5 ∧ p1) → (((p5 → True) → (False ∧ p5)) ∨ (True ∨ (True ∨ ((p4 ∧ p3) ∧ (True ∧ (p1 ∧ p4)))))))) ∨ p4) ∧ True) := by
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
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_313107813942665977508073827633 : (p3 ∨ ((((((False ∨ (p4 ∧ (p1 → (p4 ∧ (p4 ∧ False))))) ∨ (False ∨ (p5 ∧ p5))) ∧ (p1 ∨ True)) ∧ p2) ∨ ((False → p4) ∨ True)) ∨ p4)) := by
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
theorem thm_5_vars_719897845971259444917758676409 : ((((p4 → (False ∨ (p3 ∧ p3))) ∨ (((p5 → (((p3 ∨ p3) → (p4 ∨ p4)) → False)) ∨ True) ∨ ((False ∨ (p2 ∨ p4)) ∨ (True ∧ True)))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_126603931274402121179213010952 : ((p3 ∧ (((p4 ∨ p2) ∨ ((p5 ∧ p2) ∨ (False ∨ p4))) ∧ (((p2 ∨ p3) ∨ (True ∨ p3)) ∧ (p2 ∨ (p4 ∨ (p4 → False)))))) → (False ∨ p3)) := by
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
    cases h6
    case inl h7 =>
      -- Conjunctions on the left can always be decomposed.
      let h8 := h5.left
      let h9 := h5.right
      -- Disjunctions on the left can always be decomposed.
      cases h8
      case inl h10 =>
        -- Disjunctions on the left can always be decomposed.
        cases h10
        case inl h11 =>
          -- Disjunctions on the left can always be decomposed.
          cases h9
          case inl h12 =>
            -- Show the right disjunct based on <expert-advice>.
            apply Or.inr
            -- One of the premise coincides with the conclusion.
            exact h2
          case inr h13 =>
            -- Disjunctions on the left can always be decomposed.
            cases h13
            case inl h14 =>
              -- Show the right disjunct based on <expert-advice>.
              apply Or.inr
              -- One of the premise coincides with the conclusion.
              exact h2
            case inr h15 =>
              -- Show the right disjunct based on <expert-advice>.
              apply Or.inr
              -- One of the premise coincides with the conclusion.
              exact h2
        case inr h16 =>
          -- Disjunctions on the left can always be decomposed.
          cases h9
          case inl h17 =>
            -- Show the right disjunct based on <expert-advice>.
            apply Or.inr
            -- One of the premise coincides with the conclusion.
            exact h16
          case inr h18 =>
            -- Disjunctions on the left can always be decomposed.
            cases h18
            case inl h19 =>
              -- Show the right disjunct based on <expert-advice>.
              apply Or.inr
              -- One of the premise coincides with the conclusion.
              exact h16
            case inr h20 =>
              -- Show the right disjunct based on <expert-advice>.
              apply Or.inr
              -- One of the premise coincides with the conclusion.
              exact h16
      case inr h21 =>
        -- Disjunctions on the left can always be decomposed.
        cases h21
        case inl h22 =>
          -- Disjunctions on the left can always be decomposed.
          cases h9
          case inl h23 =>
            -- Show the right disjunct based on <expert-advice>.
            apply Or.inr
            -- One of the premise coincides with the conclusion.
            exact h2
          case inr h24 =>
            -- Disjunctions on the left can always be decomposed.
            cases h24
            case inl h25 =>
              -- Show the right disjunct based on <expert-advice>.
              apply Or.inr
              -- One of the premise coincides with the conclusion.
              exact h2
            case inr h26 =>
              -- Show the right disjunct based on <expert-advice>.
              apply Or.inr
              -- One of the premise coincides with the conclusion.
              exact h2
        case inr h27 =>
          -- Disjunctions on the left can always be decomposed.
          cases h9
          case inl h28 =>
            -- Show the right disjunct based on <expert-advice>.
            apply Or.inr
            -- One of the premise coincides with the conclusion.
            exact h27
          case inr h29 =>
            -- Disjunctions on the left can always be decomposed.
            cases h29
            case inl h30 =>
              -- Show the right disjunct based on <expert-advice>.
              apply Or.inr
              -- One of the premise coincides with the conclusion.
              exact h27
            case inr h31 =>
              -- Show the right disjunct based on <expert-advice>.
              apply Or.inr
              -- One of the premise coincides with the conclusion.
              exact h27
    case inr h32 =>
      -- Conjunctions on the left can always be decomposed.
      let h33 := h5.left
      let h34 := h5.right
      -- Disjunctions on the left can always be decomposed.
      cases h33
      case inl h35 =>
        -- Disjunctions on the left can always be decomposed.
        cases h35
        case inl h36 =>
          -- Disjunctions on the left can always be decomposed.
          cases h34
          case inl h37 =>
            -- Show the right disjunct based on <expert-advice>.
            apply Or.inr
            -- One of the premise coincides with the conclusion.
            exact h2
          case inr h38 =>
            -- Disjunctions on the left can always be decomposed.
            cases h38
            case inl h39 =>
              -- Show the right disjunct based on <expert-advice>.
              apply Or.inr
              -- One of the premise coincides with the conclusion.
              exact h2
            case inr h40 =>
              -- Show the right disjunct based on <expert-advice>.
              apply Or.inr
              -- One of the premise coincides with the conclusion.
              exact h2
        case inr h41 =>
          -- Disjunctions on the left can always be decomposed.
          cases h34
          case inl h42 =>
            -- Show the right disjunct based on <expert-advice>.
            apply Or.inr
            -- One of the premise coincides with the conclusion.
            exact h41
          case inr h43 =>
            -- Disjunctions on the left can always be decomposed.
            cases h43
            case inl h44 =>
              -- Show the right disjunct based on <expert-advice>.
              apply Or.inr
              -- One of the premise coincides with the conclusion.
              exact h41
            case inr h45 =>
              -- Show the right disjunct based on <expert-advice>.
              apply Or.inr
              -- One of the premise coincides with the conclusion.
              exact h41
      case inr h46 =>
        -- Disjunctions on the left can always be decomposed.
        cases h46
        case inl h47 =>
          -- Disjunctions on the left can always be decomposed.
          cases h34
          case inl h48 =>
            -- Show the right disjunct based on <expert-advice>.
            apply Or.inr
            -- One of the premise coincides with the conclusion.
            exact h2
          case inr h49 =>
            -- Disjunctions on the left can always be decomposed.
            cases h49
            case inl h50 =>
              -- Show the right disjunct based on <expert-advice>.
              apply Or.inr
              -- One of the premise coincides with the conclusion.
              exact h2
            case inr h51 =>
              -- Show the right disjunct based on <expert-advice>.
              apply Or.inr
              -- One of the premise coincides with the conclusion.
              exact h2
        case inr h52 =>
          -- Disjunctions on the left can always be decomposed.
          cases h34
          case inl h53 =>
            -- Show the right disjunct based on <expert-advice>.
            apply Or.inr
            -- One of the premise coincides with the conclusion.
            exact h52
          case inr h54 =>
            -- Disjunctions on the left can always be decomposed.
            cases h54
            case inl h55 =>
              -- Show the right disjunct based on <expert-advice>.
              apply Or.inr
              -- One of the premise coincides with the conclusion.
              exact h52
            case inr h56 =>
              -- Show the right disjunct based on <expert-advice>.
              apply Or.inr
              -- One of the premise coincides with the conclusion.
              exact h52
  case inr h57 =>
    -- Disjunctions on the left can always be decomposed.
    cases h57
    case inl h58 =>
      -- Conjunctions on the left can always be decomposed.
      let h59 := h58.left
      let h60 := h58.right
      -- Conjunctions on the left can always be decomposed.
      let h61 := h5.left
      let h62 := h5.right
      -- Disjunctions on the left can always be decomposed.
      cases h61
      case inl h63 =>
        -- Disjunctions on the left can always be decomposed.
        cases h63
        case inl h64 =>
          -- Disjunctions on the left can always be decomposed.
          cases h62
          case inl h65 =>
            -- Show the right disjunct based on <expert-advice>.
            apply Or.inr
            -- One of the premise coincides with the conclusion.
            exact h2
          case inr h66 =>
            -- Disjunctions on the left can always be decomposed.
            cases h66
            case inl h67 =>
              -- Show the right disjunct based on <expert-advice>.
              apply Or.inr
              -- One of the premise coincides with the conclusion.
              exact h2
            case inr h68 =>
              -- Show the right disjunct based on <expert-advice>.
              apply Or.inr
              -- One of the premise coincides with the conclusion.
              exact h2
        case inr h69 =>
          -- Disjunctions on the left can always be decomposed.
          cases h62
          case inl h70 =>
            -- Show the right disjunct based on <expert-advice>.
            apply Or.inr
            -- One of the premise coincides with the conclusion.
            exact h69
          case inr h71 =>
            -- Disjunctions on the left can always be decomposed.
            cases h71
            case inl h72 =>
              -- Show the right disjunct based on <expert-advice>.
              apply Or.inr
              -- One of the premise coincides with the conclusion.
              exact h69
            case inr h73 =>
              -- Show the right disjunct based on <expert-advice>.
              apply Or.inr
              -- One of the premise coincides with the conclusion.
              exact h69
      case inr h74 =>
        -- Disjunctions on the left can always be decomposed.
        cases h74
        case inl h75 =>
          -- Disjunctions on the left can always be decomposed.
          cases h62
          case inl h76 =>
            -- Show the right disjunct based on <expert-advice>.
            apply Or.inr
            -- One of the premise coincides with the conclusion.
            exact h2
          case inr h77 =>
            -- Disjunctions on the left can always be decomposed.
            cases h77
            case inl h78 =>
              -- Show the right disjunct based on <expert-advice>.
              apply Or.inr
              -- One of the premise coincides with the conclusion.
              exact h2
            case inr h79 =>
              -- Show the right disjunct based on <expert-advice>.
              apply Or.inr
              -- One of the premise coincides with the conclusion.
              exact h2
        case inr h80 =>
          -- Disjunctions on the left can always be decomposed.
          cases h62
          case inl h81 =>
            -- Show the right disjunct based on <expert-advice>.
            apply Or.inr
            -- One of the premise coincides with the conclusion.
            exact h80
          case inr h82 =>
            -- Disjunctions on the left can always be decomposed.
            cases h82
            case inl h83 =>
              -- Show the right disjunct based on <expert-advice>.
              apply Or.inr
              -- One of the premise coincides with the conclusion.
              exact h80
            case inr h84 =>
              -- Show the right disjunct based on <expert-advice>.
              apply Or.inr
              -- One of the premise coincides with the conclusion.
              exact h80
    case inr h85 =>
      -- Disjunctions on the left can always be decomposed.
      cases h85
      case inl h86 =>
        -- False on the left can always be used.
        apply False.elim h86
      case inr h87 =>
        -- Conjunctions on the left can always be decomposed.
        let h88 := h5.left
        let h89 := h5.right
        -- Disjunctions on the left can always be decomposed.
        cases h88
        case inl h90 =>
          -- Disjunctions on the left can always be decomposed.
          cases h90
          case inl h91 =>
            -- Disjunctions on the left can always be decomposed.
            cases h89
            case inl h92 =>
              -- Show the right disjunct based on <expert-advice>.
              apply Or.inr
              -- One of the premise coincides with the conclusion.
              exact h2
            case inr h93 =>
              -- Disjunctions on the left can always be decomposed.
              cases h93
              case inl h94 =>
                -- Show the right disjunct based on <expert-advice>.
                apply Or.inr
                -- One of the premise coincides with the conclusion.
                exact h2
              case inr h95 =>
                -- Show the right disjunct based on <expert-advice>.
                apply Or.inr
                -- One of the premise coincides with the conclusion.
                exact h2
          case inr h96 =>
            -- Disjunctions on the left can always be decomposed.
            cases h89
            case inl h97 =>
              -- Show the right disjunct based on <expert-advice>.
              apply Or.inr
              -- One of the premise coincides with the conclusion.
              exact h96
            case inr h98 =>
              -- Disjunctions on the left can always be decomposed.
              cases h98
              case inl h99 =>
                -- Show the right disjunct based on <expert-advice>.
                apply Or.inr
                -- One of the premise coincides with the conclusion.
                exact h96
              case inr h100 =>
                -- Show the right disjunct based on <expert-advice>.
                apply Or.inr
                -- One of the premise coincides with the conclusion.
                exact h96
        case inr h101 =>
          -- Disjunctions on the left can always be decomposed.
          cases h101
          case inl h102 =>
            -- Disjunctions on the left can always be decomposed.
            cases h89
            case inl h103 =>
              -- Show the right disjunct based on <expert-advice>.
              apply Or.inr
              -- One of the premise coincides with the conclusion.
              exact h2
            case inr h104 =>
              -- Disjunctions on the left can always be decomposed.
              cases h104
              case inl h105 =>
                -- Show the right disjunct based on <expert-advice>.
                apply Or.inr
                -- One of the premise coincides with the conclusion.
                exact h2
              case inr h106 =>
                -- Show the right disjunct based on <expert-advice>.
                apply Or.inr
                -- One of the premise coincides with the conclusion.
                exact h2
          case inr h107 =>
            -- Disjunctions on the left can always be decomposed.
            cases h89
            case inl h108 =>
              -- Show the right disjunct based on <expert-advice>.
              apply Or.inr
              -- One of the premise coincides with the conclusion.
              exact h107
            case inr h109 =>
              -- Disjunctions on the left can always be decomposed.
              cases h109
              case inl h110 =>
                -- Show the right disjunct based on <expert-advice>.
                apply Or.inr
                -- One of the premise coincides with the conclusion.
                exact h107
              case inr h111 =>
                -- Show the right disjunct based on <expert-advice>.
                apply Or.inr
                -- One of the premise coincides with the conclusion.
                exact h107



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_187511832137997772694709365371 : ((p1 ∨ ((True ∧ (((p2 ∨ p4) ∨ (True ∨ True)) ∨ True)) → p4)) → ((p1 ∨ (((((p5 ∨ (True ∧ p4)) ∧ p3) ∨ False) → p1) ∨ True)) ∨ p5)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h2 =>
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- One of the premise coincides with the conclusion.
    exact h2
  case inr h3 =>
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_727580932772808036980538140268 : ((((p5 ∧ (p2 ∧ p3)) ∨ (True → (((p2 ∨ p2) → False) ∨ (((True ∨ (p3 ∨ True)) → p4) ∨ (p4 → (((p4 ∨ False) ∧ p4) ∨ p4)))))) ∨ p2) ∧ True) := by
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
  -- Implications on the right can always be decomposed.
  intro h2
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h2
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_233784158559110925595155093621 : ((p3 ∨ (p5 ∨ p1)) → ((True → ((p1 ∧ p1) ∧ False)) ∨ ((((False ∧ (p4 ∧ (True → p1))) → True) ∧ p5) ∨ (True → (True ∨ (True → True)))))) := by
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
    -- True on the right can always be proven directly.
    apply True.intro
  case inr h4 =>
    -- Disjunctions on the left can always be decomposed.
    cases h4
    case inl h5 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- Conjunctions on the right can always be decomposed.
      apply And.intro
      -- Implications on the right can always be decomposed.
      intro h6
      -- True on the right can always be proven directly.
      apply True.intro
      -- One of the premise coincides with the conclusion.
      exact h5
    case inr h7 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Implications on the right can always be decomposed.
      intro h8
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- True on the right can always be proven directly.
      apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_800434438104967360277859456964 : (((p2 → ((p5 ∨ ((((p3 ∨ p1) ∨ p5) ∨ ((True ∨ True) ∨ (((True ∨ True) → p1) → p5))) ∧ (((p2 ∨ p3) ∧ p4) ∨ p5))) ∨ p4)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_637320744557799119348482619633 : (((((p1 ∧ ((((p2 ∨ False) → True) ∨ p5) → ((p5 ∨ p1) ∧ p3))) → (((p4 ∧ p3) → p1) → ((p4 ∧ p1) → (p4 → p1)))) → p3) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_654010845824866086793174902173 : (((((False ∨ (((p2 ∨ ((p2 ∨ (p1 ∨ (p1 ∨ p3))) ∨ p1)) ∨ p5) ∧ (False ∨ (p4 ∧ (p1 ∨ (p5 ∨ p3)))))) ∧ p3) ∨ (False → True)) ∨ p3) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_45357184561084426184620308157 : (((p4 ∧ (((p3 ∧ p3) ∨ ((False ∧ p5) ∨ (True ∨ (((True ∧ p4) ∧ ((p1 ∨ p2) ∨ (p4 → p4))) ∧ p4)))) → (p3 ∨ True))) → p3) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_356175046198136345112980546544 : (p5 → ((p5 → ((((p1 ∨ (p3 ∧ p2)) ∧ (((p1 ∧ p3) ∨ (False → p4)) ∧ p3)) ∨ True) → False)) ∨ (False ∨ (((p4 → p5) ∧ False) → p2)))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h2
  -- Conjunctions on the left can always be decomposed.
  let h3 := h2.left
  let h4 := h2.right
  -- False on the left can always be used.
  apply False.elim h4



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_42135760530905467474650763099 : ((((p3 ∨ p2) → ((p1 ∨ (True → ((((False ∨ (p5 → (((p1 → p4) ∨ p1) ∨ p4))) ∧ p2) → (True ∧ p3)) ∨ p2))) ∨ p3)) ∨ p2) ∨ False) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
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
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h4
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h3



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_115758505920076419193542023510 : (((True ∨ (((False ∧ p3) ∧ True) → p1)) → (((p3 ∨ p5) ∧ (p5 → p2)) → (p3 ∨ ((p2 ∨ p4) → ((p2 → p1) ∨ p2))))) ∨ (p2 ∧ p3)) := by
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
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- One of the premise coincides with the conclusion.
      exact h5
    case inr h7 =>
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- One of the premise coincides with the conclusion.
      exact h5
  case inr h8 =>
    -- Disjunctions on the left can always be decomposed.
    cases h1
    case inl h9 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Implications on the right can always be decomposed.
      intro h10
      -- Disjunctions on the left can always be decomposed.
      cases h10
      case inl h11 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- One of the premise coincides with the conclusion.
        exact h11
      case inr h12 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- We want to use the implication h4 based on <expert-advice>. So we show its premise.
        have h13 : p5 := by
          -- One of the premise coincides with the conclusion.
          exact h8
        -- We have shown the premise of h4, we can now drive its conclusion.
        let h14 := h4 h13
        -- One of the premise coincides with the conclusion.
        exact h14
    case inr h15 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Implications on the right can always be decomposed.
      intro h16
      -- Disjunctions on the left can always be decomposed.
      cases h16
      case inl h17 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- One of the premise coincides with the conclusion.
        exact h17
      case inr h18 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- We want to use the implication h4 based on <expert-advice>. So we show its premise.
        have h19 : p5 := by
          -- One of the premise coincides with the conclusion.
          exact h8
        -- We have shown the premise of h4, we can now drive its conclusion.
        let h20 := h4 h19
        -- One of the premise coincides with the conclusion.
        exact h20



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_644296160125492375425815890790 : ((((False ∨ ((True ∨ ((((p1 ∨ ((True ∨ True) ∨ p2)) → (p3 → p2)) ∨ (p3 ∧ (True ∧ p5))) ∧ p4)) ∧ (True ∧ (p2 → p5)))) → p1) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_317032467965238595831323999949 : (p3 ∨ (p4 → ((((((p2 ∧ ((False → False) → ((False ∨ ((True → p3) → (p5 → (p2 → p4)))) ∧ p2))) ∧ True) → p1) → p1) ∧ p1) ∨ p4))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_47939294742699567525458214403 : (((((p5 → ((p1 ∧ (((p1 ∨ p4) → (p2 → p5)) ∨ p4)) ∨ ((p5 → p5) ∧ p3))) → p4) ∨ ((p1 ∨ p2) ∧ p3)) → (p1 ∨ p5)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_41764395642139247263427070970 : (((((False → p1) → (True ∧ False)) ∨ (((p3 ∧ p3) → p1) → ((False → p3) → ((True ∨ ((p5 ∨ p1) → p1)) ∧ (p5 ∧ p2))))) ∨ True) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_202522956322399300741065416983 : ((((p4 ∨ p2) → p4) ∨ (True ∨ p4)) ∧ (False ∨ (((p5 ∧ (False ∨ (p5 → False))) → (False ∨ (p3 ∧ (p1 ∨ ((p3 ∧ False) → p3))))) ∨ p2))) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro
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
    -- False on the left can always be used.
    apply False.elim h4
  case inr h5 =>
    -- We want to use the implication h5 based on <expert-advice>. So we show its premise.
    have h6 : p5 := by
      -- One of the premise coincides with the conclusion.
      exact h2
    -- We have shown the premise of h5, we can now drive its conclusion.
    let h7 := h5 h6
    -- False on the left can always be used.
    apply False.elim h7



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_130453500793789466959194933182 : ((((p3 ∧ p4) ∧ (((p1 ∧ p3) ∨ (False ∨ False)) ∨ ((p4 ∨ (True ∧ p4)) ∨ (p4 → p4)))) ∨ ((p2 ∨ p2) → p2)) ∧ (p1 → (p2 → p1))) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
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
    -- One of the premise coincides with the conclusion.
    exact h3
  -- Implications on the right can always be decomposed.
  intro h4
  -- Implications on the right can always be decomposed.
  intro h5
  -- One of the premise coincides with the conclusion.
  exact h4



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_347640653113496156337701438535 : (p3 → (((p3 → (p2 ∧ p4)) ∧ p2) → (((False ∨ ((True → True) → ((False ∧ p3) → ((p5 ∧ False) → p3)))) → ((p1 ∧ p5) ∨ p2)) ∨ True))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Conjunctions on the left can always be decomposed.
  let h3 := h2.left
  let h4 := h2.right
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_263491313698579684000105390652 : (True ∧ ((p3 ∨ ((False ∨ False) → (((((((p3 ∨ p1) ∧ p5) → p2) → ((p5 ∧ True) ∨ True)) → p2) ∨ p4) → p2))) → (p1 ∨ (p2 ∨ True)))) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- True on the right can always be proven directly.
  apply True.intro
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
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_147941536568518043194097576652 : ((((False ∨ p4) ∧ ((((True ∨ (p5 → ((True → (p5 → p5)) → p3))) ∨ p1) → p3) ∨ p1)) ∧ (p5 ∨ False)) ∨ (((False ∧ p1) → False) ∨ False)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- False on the left can always be used.
  apply False.elim h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_245344199601189740619478722900 : ((p2 ∧ p3) ∨ ((((p2 ∨ (p5 ∨ p1)) ∧ p3) ∨ ((((p5 → ((((p2 ∧ True) ∧ p4) → (p4 ∧ p3)) ∧ False)) ∧ p5) → p1) ∨ False)) ∨ p3)) := by
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
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
  have h4 : p5 := by
    -- One of the premise coincides with the conclusion.
    exact h3
  -- We have shown the premise of h2, we can now drive its conclusion.
  let h5 := h2 h4
  -- We need to get the right conjuct of h5 based on <expert-advice>.
  let h6 := h5.right
  -- False on the left can always be used.
  apply False.elim h6



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_647622881675999990033322403312 : ((((p5 → ((p5 ∨ ((False ∨ (p1 → (p4 ∧ (p1 → (p4 ∧ True))))) → (p1 → p1))) ∧ (p4 ∨ (True → ((p2 → True) ∨ p2))))) → False) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_167220655898264745064044701770 : (((p3 ∨ (p3 ∨ (p5 ∨ ((False ∨ (True ∧ p4)) ∨ (True ∧ ((p3 ∧ True) ∨ p3)))))) ∨ p4) → (p1 ∨ (p5 → (((p5 ∨ p4) ∨ True) → True)))) := by
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
      -- True on the right can always be proven directly.
      apply True.intro
    case inr h6 =>
      -- Disjunctions on the left can always be decomposed.
      cases h6
      case inl h7 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- Implications on the right can always be decomposed.
        intro h8
        -- Implications on the right can always be decomposed.
        intro h9
        -- True on the right can always be proven directly.
        apply True.intro
      case inr h10 =>
        -- Disjunctions on the left can always be decomposed.
        cases h10
        case inl h11 =>
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- Implications on the right can always be decomposed.
          intro h12
          -- Implications on the right can always be decomposed.
          intro h13
          -- True on the right can always be proven directly.
          apply True.intro
        case inr h14 =>
          -- Disjunctions on the left can always be decomposed.
          cases h14
          case inl h15 =>
            -- Disjunctions on the left can always be decomposed.
            cases h15
            case inl h16 =>
              -- False on the left can always be used.
              apply False.elim h16
            case inr h17 =>
              -- Conjunctions on the left can always be decomposed.
              let h18 := h17.left
              let h19 := h17.right
              -- Show the right disjunct based on <expert-advice>.
              apply Or.inr
              -- Implications on the right can always be decomposed.
              intro h20
              -- Implications on the right can always be decomposed.
              intro h21
              -- True on the right can always be proven directly.
              apply True.intro
          case inr h22 =>
            -- Conjunctions on the left can always be decomposed.
            let h23 := h22.left
            let h24 := h22.right
            -- Disjunctions on the left can always be decomposed.
            cases h24
            case inl h25 =>
              -- Conjunctions on the left can always be decomposed.
              let h26 := h25.left
              let h27 := h25.right
              -- Show the right disjunct based on <expert-advice>.
              apply Or.inr
              -- Implications on the right can always be decomposed.
              intro h28
              -- Implications on the right can always be decomposed.
              intro h29
              -- True on the right can always be proven directly.
              apply True.intro
            case inr h30 =>
              -- Show the right disjunct based on <expert-advice>.
              apply Or.inr
              -- Implications on the right can always be decomposed.
              intro h31
              -- Implications on the right can always be decomposed.
              intro h32
              -- True on the right can always be proven directly.
              apply True.intro
  case inr h33 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h34
    -- Implications on the right can always be decomposed.
    intro h35
    -- True on the right can always be proven directly.
    apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_42658183810311213815112496126 : (((p4 ∨ ((((p1 → p4) ∨ (p5 ∨ (True ∧ (p1 ∧ p3)))) ∧ (((p5 ∨ (p1 → p4)) → p3) ∨ p5)) ∨ (p2 → (False → True)))) ∨ False) ∨ p1) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
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
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_345342353793432844766091780816 : (p3 → (((p3 ∧ (((p4 → True) ∧ True) → ((True ∧ (((((p1 ∧ p5) ∨ (True ∧ True)) ∨ (p3 ∨ True)) ∧ p1) ∨ p4)) ∧ p3))) ∧ False) ∨ True)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_336218605363239104107093789157 : (p1 → (((((False ∧ ((((p5 → ((p2 ∨ True) ∧ (False → False))) → True) ∨ p3) ∧ False)) ∧ False) ∨ (p2 ∨ p2)) ∧ ((p3 ∧ p4) → p3)) ∨ True)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_221709506030406252583030305202 : (((False ∧ False) → True) ∧ (((p2 ∧ (p2 ∧ p3)) ∨ ((p3 ∧ False) ∨ (p5 ∧ (((p2 ∨ p3) ∨ True) ∧ ((p5 → True) ∨ p4))))) ∨ (p3 → True))) := by
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
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_158686424264475608774391822102 : ((p2 ∧ ((((True ∧ False) ∧ p2) ∨ p3) ∨ ((p3 → (p5 ∨ False)) → (True ∧ ((p1 ∨ False) ∨ True))))) ∨ ((p1 → (False ∨ True)) → (True → True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_263993752326716754100466058798 : (True ∧ ((p3 ∨ ((p2 → p2) ∧ ((p3 ∨ ((p1 ∧ p5) → p3)) → p2))) ∨ (((False ∧ p1) ∨ p5) ∨ (p5 → (p4 ∨ ((True ∨ p3) → p5)))))) := by
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



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_52969829115798371812738643318 : ((((((False ∧ (p4 ∨ (p1 → p4))) → False) → (True ∧ p1)) → p5) ∧ (True ∧ (p3 ∧ (((True → p2) → ((p1 ∧ False) → p1)) → p4)))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_210173537273807687136461575419 : ((((p2 ∨ False) ∨ p3) ∨ True) ∧ ((p3 ∨ (True ∧ (p3 ∧ p4))) → (True → (((((p1 ∨ (p4 ∨ p3)) → False) ∧ (p5 ∧ p2)) → p1) ∧ True)))) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h3
  -- Conjunctions on the left can always be decomposed.
  let h4 := h3.left
  let h5 := h3.right
  -- Conjunctions on the left can always be decomposed.
  let h6 := h5.left
  let h7 := h5.right
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h8 =>
    -- We want to use the implication h4 based on <expert-advice>. So we show its premise.
    have h9 : (p1 ∨ (p4 ∨ p3)) := by
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- One of the premise coincides with the conclusion.
      exact h8
    -- We have shown the premise of h4, we can now drive its conclusion.
    let h10 := h4 h9
    -- False on the left can always be used.
    apply False.elim h10
  case inr h11 =>
    -- Conjunctions on the left can always be decomposed.
    let h12 := h11.left
    let h13 := h11.right
    -- Conjunctions on the left can always be decomposed.
    let h14 := h13.left
    let h15 := h13.right
    -- We want to use the implication h4 based on <expert-advice>. So we show its premise.
    have h16 : (p1 ∨ (p4 ∨ p3)) := by
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- One of the premise coincides with the conclusion.
      exact h15
    -- We have shown the premise of h4, we can now drive its conclusion.
    let h17 := h4 h16
    -- False on the left can always be used.
    apply False.elim h17
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_321816290571191139997887500355 : (p5 ∨ (((((((p5 ∨ p5) → (True ∧ p5)) ∨ p1) → (p1 → ((False ∧ p2) ∧ (True ∧ ((True ∧ p1) → (p2 ∨ False)))))) ∨ True) ∨ p2) ∧ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
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
theorem thm_5_vars_42128979458539778100828270375 : ((((p1 ∨ p3) → (((p2 ∧ p2) → (p1 → (((((p2 ∧ p3) → True) ∧ (p4 → ((p4 → False) ∧ False))) → False) ∨ p1))) → False)) ∨ False) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_702644086710822235211226749734 : ((((((((True ∨ p3) ∨ True) ∧ p2) ∨ False) ∧ (p1 ∧ p4)) ∨ (True ∧ (p5 ∨ (((False → (p3 ∧ (False ∨ p4))) ∧ (False → p1)) ∨ p2)))) ∨ p3) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- False on the left can always be used.
  apply False.elim h1
  -- False on the left can always be used.
  apply False.elim h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- False on the left can always be used.
  apply False.elim h2
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_244070401586143262573382808386 : ((True ∧ p3) ∨ ((p1 ∨ ((((((p5 ∨ False) ∧ p4) → (False → (p1 ∧ False))) ∨ p2) ∨ p1) → ((False ∨ (p3 ∧ p5)) ∨ (True ∨ False)))) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_146901707735421485253441596807 : ((((((p4 ∨ (((p5 → ((p5 ∨ (p4 ∨ False)) ∧ True)) → p3) ∧ (p1 ∨ True))) → p4) ∧ p4) ∧ p5) ∧ p3) ∨ (p2 ∨ (p1 → (p4 → True)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_39997491671442708999410577392 : (((p5 → ((p2 ∧ (((p4 ∧ ((p1 → (p4 ∨ ((True ∨ p5) ∧ p1))) → (False ∨ True))) → p5) → p3)) ∨ ((p2 ∧ p1) ∨ False))) ∧ False) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_25316796159781118989600891273 : ((((p2 → p1) ∨ p1) → ((((p2 → p3) → (True ∧ (p2 ∨ (((p5 ∧ (p2 ∨ (False ∧ p5))) ∧ p5) ∨ p1)))) → p2) → (p1 → p1))) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Implications on the right can always be decomposed.
  intro h3
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h4 =>
    -- One of the premise coincides with the conclusion.
    exact h3
  case inr h5 =>
    -- One of the premise coincides with the conclusion.
    exact h5
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_134273615747069002334738407807 : ((((p2 ∨ False) ∧ (((p1 ∧ p4) ∧ ((((p3 ∧ True) ∧ p3) ∧ p3) ∧ p2)) ∨ (((True → p2) → p1) ∨ p3))) ∨ p3) ∨ ((p4 ∧ False) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_134190322406830617392427864551 : (((((False ∧ p5) ∨ (p4 ∧ ((p2 ∨ (p2 → True)) → (False ∨ p2)))) → (((p3 ∨ (p3 → p2)) → p3) ∧ p5)) ∨ False) ∨ ((p5 ∧ False) → p5)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- False on the left can always be used.
  apply False.elim h3



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_62986145191095960787010341396 : ((p4 ∧ (p5 ∨ ((p1 → (True ∧ (((False ∧ False) → (p3 ∨ p5)) → (((p3 ∨ False) ∧ True) → (True → ((p3 ∧ p5) ∧ True)))))) ∧ p1))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_233956298505388297573286066274 : ((p5 ∨ (False ∧ p5)) → (p3 ∨ ((p4 ∨ (p1 ∧ (p2 → (p1 ∨ (p4 ∧ p2))))) ∨ (((p4 ∧ (p3 ∧ p2)) → p1) ∨ (p4 ∨ (p5 ∨ p3)))))) := by
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
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- One of the premise coincides with the conclusion.
    exact h2
  case inr h3 =>
    -- Conjunctions on the left can always be decomposed.
    let h4 := h3.left
    let h5 := h3.right
    -- False on the left can always be used.
    apply False.elim h4



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_315118715339665966217929221660 : (p3 ∨ ((((p2 ∧ p2) ∧ p4) ∧ (False → False)) ∨ ((p4 ∨ p2) → (p2 ∨ (p3 → ((((p1 → ((False ∨ p4) → p5)) ∧ p5) ∧ p5) ∨ p3)))))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
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
theorem thm_5_vars_178064517900492352537684705206 : (((((True → (p1 ∧ (p2 ∧ True))) ∧ ((p2 → True) ∧ p5)) ∨ False) → p3) ∨ (((True ∨ p1) ∧ p1) → ((((p2 ∧ False) ∨ False) ∧ p1) → False))) := by
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
    -- Conjunctions on the left can always be decomposed.
    let h6 := h5.left
    let h7 := h5.right
    -- False on the left can always be used.
    apply False.elim h7
  case inr h8 =>
    -- False on the left can always be used.
    apply False.elim h8



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_66307789506389069971868974536 : ((p5 ∨ ((p2 ∨ p1) → (((((p5 ∨ (((p3 → p2) ∨ p5) ∧ ((p3 ∧ True) ∨ p5))) ∨ False) ∧ ((False ∨ True) ∨ False)) ∧ p1) ∧ p2))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_595744672956552340871974884924 : ((((((p4 ∨ (((p3 ∧ p1) → (p2 → True)) ∨ False)) → p5) ∧ (((False ∧ ((p2 → True) → p1)) ∨ p2) ∧ (p5 → (False ∨ p2)))) ∧ p2) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_61922223492269268134012828570 : ((p2 ∧ (((((False ∧ p1) ∧ p2) → (True → p5)) ∨ ((p3 ∧ p3) ∧ (False ∨ (((p3 → p5) → p1) ∧ p1)))) → ((False ∧ p2) ∨ True))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_172419259857283216084113207006 : ((((p2 ∧ False) ∧ (p2 → p4)) ∧ (False ∨ ((p5 → (True ∨ p3)) → (p5 ∧ p2)))) ∨ ((p1 ∨ (p3 → (False → p5))) ∨ (p3 ∨ (p1 → p3)))) := by
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
  -- False on the left can always be used.
  apply False.elim h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_339995196904166883140244481838 : (p1 → (p1 → (((p1 ∧ (p3 → p4)) → p3) ∨ ((p2 → ((((True → (p5 ∧ p4)) ∧ p1) → (False ∨ p4)) ∧ (p5 → p3))) ∨ (p1 ∨ False))))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_350569792527043327988079614309 : (p4 → (((((p1 ∧ p3) ∨ (True → (((False → True) ∧ False) → p3))) ∨ p3) → (((False → p5) ∧ (p4 ∧ False)) ∧ (p4 → (p4 ∧ False)))) → p3)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
  have h3 : (((p1 ∧ p3) ∨ (True → (((False → True) ∧ False) → p3))) ∨ p3) := by
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h4
    -- Implications on the right can always be decomposed.
    intro h5
    -- Conjunctions on the left can always be decomposed.
    let h6 := h5.left
    let h7 := h5.right
    -- False on the left can always be used.
    apply False.elim h7
  -- We have shown the premise of h2, we can now drive its conclusion.
  let h8 := h2 h3
  -- We need to get the left conjuct of h8 based on <expert-advice>.
  let h9 := h8.left
  -- We need to get the right conjuct of h9 based on <expert-advice>.
  let h10 := h9.right
  -- We need to get the right conjuct of h10 based on <expert-advice>.
  let h11 := h10.right
  -- False on the left can always be used.
  apply False.elim h11



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_94825359540740192475106511623 : ((p3 ∧ ((p3 → p1) ∧ ((p5 → p5) → ((p4 ∨ p5) ∨ (((p5 → p5) → p4) → (p1 ∨ (((p2 → (False ∧ p1)) → False) → p5))))))) → p1) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- Conjunctions on the left can always be decomposed.
  let h4 := h3.left
  let h5 := h3.right
  -- We want to use the implication h4 based on <expert-advice>. So we show its premise.
  have h6 : p3 := by
    -- One of the premise coincides with the conclusion.
    exact h2
  -- We have shown the premise of h4, we can now drive its conclusion.
  let h7 := h4 h6
  -- One of the premise coincides with the conclusion.
  exact h7



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_16887284779414538558268699997 : (((True ∧ (((((((p5 ∧ ((p5 → False) ∧ (p1 ∧ False))) ∧ p2) ∨ (p1 ∨ p3)) ∨ p3) → p5) ∨ False) ∨ p2)) ∨ (True → (False → True))) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_2648388612592602654108815807 : ((((p2 ∨ p3) ∨ (p4 ∨ p4)) ∨ p5) ∨ (p3 → ((((p4 ∧ p5) ∨ p5) ∧ (((p2 → ((p1 ∨ p1) ∨ p2)) → False) ∨ p5)) ∨ p3))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_256819050518613318453466216461 : ((p1 ∨ p3) → ((((p3 ∧ (p2 → (((p3 ∧ (p2 → (False ∨ p3))) ∨ (True → p5)) ∨ ((False ∨ p2) ∨ p1)))) ∨ (p2 ∨ p5)) ∧ p3) ∨ True)) := by
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
theorem thm_5_vars_324423385906045348872309162280 : (p5 ∨ ((p1 → (False ∧ (False ∧ (p3 ∨ False)))) → ((((p4 ∨ True) → p4) ∨ (p4 → (p5 ∨ True))) ∨ ((p4 ∧ ((True ∨ p5) ∧ p5)) ∧ p1)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
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
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_115958130537589751799082850424 : (((p3 → ((p5 ∧ p5) ∨ False)) ∨ (p4 ∨ (p4 → ((p4 ∨ p1) → (p2 ∨ (p5 ∧ (((p5 ∧ p4) ∧ (p3 → p4)) ∨ p3))))))) ∨ (p2 → p2)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_986389110632188017522088479634 : (((p2 ∧ (((True → p2) ∨ (((True ∧ True) ∧ p5) → p5)) → ((p1 ∨ p2) ∧ ((((p3 ∨ (p3 ∧ p2)) ∨ (p2 ∧ True)) → p3) ∧ False)))) → False) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- We want to use the implication h3 based on <expert-advice>. So we show its premise.
  have h4 : ((True → p2) ∨ (((True ∧ True) ∧ p5) → p5)) := by
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Implications on the right can always be decomposed.
    intro h5
    -- One of the premise coincides with the conclusion.
    exact h2
  -- We have shown the premise of h3, we can now drive its conclusion.
  let h6 := h3 h4
  -- We need to get the right conjuct of h6 based on <expert-advice>.
  let h7 := h6.right
  -- We need to get the right conjuct of h7 based on <expert-advice>.
  let h8 := h7.right
  -- False on the left can always be used.
  apply False.elim h8
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_136213455168324695263847946711 : (((((p5 → (p4 ∧ p1)) ∧ p1) ∧ p5) ∨ (((p3 → (True → (p5 ∧ ((True ∧ p3) ∧ False)))) ∧ (False → p3)) → p1)) ∨ (p1 → (p5 → p5))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- One of the premise coincides with the conclusion.
  exact h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_165380550337013309133496317101 : ((((p4 ∧ (False ∨ (p4 → (True ∨ False)))) ∨ (p4 ∧ (True → False))) ∨ (p2 ∧ (p4 ∧ p4))) ∨ (p2 → (False → (p5 ∧ ((True ∨ p4) → p3))))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- False on the left can always be used.
  apply False.elim h2
  -- Implications on the right can always be decomposed.
  intro h3
  -- Disjunctions on the left can always be decomposed.
  cases h3
  case inl h4 =>
    -- False on the left can always be used.
    apply False.elim h2
  case inr h5 =>
    -- False on the left can always be used.
    apply False.elim h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_654131651375122810541504559497 : (((((((p4 → ((False ∨ False) → False)) → (((((p4 ∧ p2) → p4) ∧ p3) ∧ ((False ∨ p1) ∧ p3)) ∨ p5)) ∧ False) ∨ True) ∨ (p3 ∨ True)) ∨ p4) ∧ True) := by
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
theorem thm_5_vars_46929542285113502746746026398 : (((((True → p1) ∨ (((((p3 ∧ p3) ∨ True) ∨ p1) ∨ ((False ∧ p5) → (p5 → ((True ∨ p3) → p4)))) → p2)) ∨ p5) ∨ (p5 → True)) ∨ False) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_115417097202379187143167400613 : (((((((True ∧ False) ∧ p4) ∧ p3) → p3) ∧ p3) ∨ (((((p2 ∨ (p5 ∨ p1)) → p5) → ((False → p3) ∧ p1)) ∧ p5) ∨ p5)) ∨ (False → p3)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_52949169139104274896849300759 : (((((True ∨ (p1 ∨ ((p3 → p1) ∨ p2))) → (p2 ∨ p1)) ∨ True) ∧ (((p1 ∨ ((True ∨ (p4 ∨ p5)) ∧ (False ∧ False))) ∨ p2) ∨ p5)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_775925110036971097714773195024 : (((False ∨ (p1 → ((p4 ∨ (((p2 ∧ True) ∨ (p3 ∨ True)) → (((p2 → False) → (False ∧ p4)) → p3))) ∨ ((p2 → p1) ∨ (p1 ∧ p5))))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



