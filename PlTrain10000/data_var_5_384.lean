variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_42618254682122170337335013779 : (((p3 ∨ (((((p4 → True) ∨ p3) ∧ (p5 → p4)) ∨ ((False ∨ ((True ∧ p2) ∨ (False → p2))) → p5)) ∧ ((True → p3) ∧ p5))) ∨ True) ∨ p2) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_647924963561227169820949718618 : ((((((p1 → ((((p2 → ((((p1 ∧ False) → True) ∧ p3) → p1)) ∨ (p5 → p4)) ∨ (True ∨ False)) ∧ p2)) → False) ∧ p1) ∧ (p2 ∧ p3)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_68808371949775353166055459110 : ((p4 → (((False → (p1 ∨ False)) ∧ True) → ((p2 → ((p2 → p3) → (((((p5 ∧ p1) → (p1 → False)) ∨ p3) ∨ p2) ∧ False))) ∨ True))) ∨ p1) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
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
theorem thm_5_vars_726314308923852693774768044517 : (((((p3 ∨ False) ∨ p5) ∨ ((p4 ∨ (p4 ∨ (p3 → (p1 ∨ ((False → True) ∨ True))))) ∨ (p1 ∧ ((p2 ∨ p2) → ((p2 ∨ p5) ∨ p3))))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_626843988953391461195903915641 : ((((p5 → (((p5 ∧ p1) → p4) → (((p1 ∧ (((p3 → p2) → p1) → (False ∨ p5))) ∨ p4) ∧ (((p5 → p5) → True) → p4)))) ∨ p4) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_717806876528190146691801936121 : ((((((p1 → p1) → p4) ∧ p2) ∨ (p3 ∨ ((((((((p5 ∨ p1) → p4) → (True ∧ p2)) ∨ p3) ∧ p4) ∨ (p1 ∧ p2)) ∨ True) ∨ p2))) ∨ p3) ∧ True) := by
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
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_431290698244379604317243897557 : ((((False ∧ ((((True ∨ ((True → (True ∨ (p4 ∨ (p5 → p4)))) ∧ p1)) ∧ ((p2 ∧ (p2 ∧ p2)) ∧ p1)) ∧ p4) → p5)) ∨ (False → p5)) ∧ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
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
theorem thm_5_vars_42653941322457351214429194774 : (((p4 ∨ ((False → (p2 ∨ ((((p4 ∧ (p5 → False)) ∨ (((p1 ∧ p4) ∧ p5) → True)) → p5) ∨ ((False ∨ False) ∧ p1)))) → False)) ∨ True) ∨ p1) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_711151697444306025738170677477 : ((((p1 ∧ (p4 → (p3 ∧ (p1 ∨ p5)))) ∧ (False ∧ (p5 ∨ (((p3 ∧ (p2 → (p5 → True))) → ((p1 ∧ True) → p1)) ∧ (p2 ∧ p5))))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_55301375220543530141537507242 : (((p4 ∧ (p5 ∨ (p1 ∨ (p2 → p1)))) ∨ ((p4 → p2) → (p1 → ((False ∧ True) ∨ (((p1 ∨ p5) → (p3 ∧ p2)) ∨ (p4 → p4)))))) ∨ p5) := by
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
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h3
  -- One of the premise coincides with the conclusion.
  exact h3



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_718743078084313608322572791264 : (((((False ∧ False) ∨ (p5 → p3)) ∨ (True ∧ ((p1 → ((p5 ∨ p5) ∧ (p1 → ((True ∧ True) → p3)))) ∨ (p3 → ((p4 ∧ p1) ∧ True))))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_135532486697804947678677869072 : ((((p3 ∧ (True ∧ ((p2 ∨ True) → (p1 → ((p3 → p2) ∨ True))))) ∧ (False ∧ p1)) ∧ (p2 ∧ ((p2 → p1) ∧ True))) ∨ (p1 → (p3 ∨ p1))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_149256347317089866572176145884 : (((p3 ∨ p3) ∨ ((((((False → p5) ∧ p3) ∧ p1) ∨ True) → p3) ∨ (True → (p2 → ((p1 ∧ True) ∧ p4))))) ∨ (((p2 ∧ p1) ∧ True) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_179109355073819584782311562133 : ((False ∧ (p3 ∧ ((((False → p4) → p5) → ((p1 ∧ p5) → p5)) → p3))) ∨ (p3 ∨ (False ∨ (((p3 ∧ p1) ∨ False) → ((True → True) ∨ p3))))) := by
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
    -- Conjunctions on the left can always be decomposed.
    let h3 := h2.left
    let h4 := h2.right
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h3
  case inr h5 =>
    -- False on the left can always be used.
    apply False.elim h5



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_141147771764693211047893125937 : ((((p2 → (False ∨ True)) ∨ (True ∨ p3)) ∧ (p4 ∧ ((p5 ∨ ((p3 ∧ (p1 ∨ True)) → ((False → p3) → p4))) → p5))) → (p5 ∧ (p5 ∧ p5))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- Disjunctions on the left can always be decomposed.
  cases h2
  case inl h4 =>
    -- Conjunctions on the left can always be decomposed.
    let h5 := h3.left
    let h6 := h3.right
    -- We want to use the implication h6 based on <expert-advice>. So we show its premise.
    have h7 : (p5 ∨ ((p3 ∧ (p1 ∨ True)) → ((False → p3) → p4))) := by
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Implications on the right can always be decomposed.
      intro h8
      -- Implications on the right can always be decomposed.
      intro h9
      -- Conjunctions on the left can always be decomposed.
      let h10 := h8.left
      let h11 := h8.right
      -- Disjunctions on the left can always be decomposed.
      cases h11
      case inl h12 =>
        -- One of the premise coincides with the conclusion.
        exact h5
      case inr h13 =>
        -- One of the premise coincides with the conclusion.
        exact h5
    -- We have shown the premise of h6, we can now drive its conclusion.
    let h14 := h6 h7
    -- One of the premise coincides with the conclusion.
    exact h14
  case inr h15 =>
    -- Disjunctions on the left can always be decomposed.
    cases h15
    case inl h16 =>
      -- Conjunctions on the left can always be decomposed.
      let h17 := h3.left
      let h18 := h3.right
      -- We want to use the implication h18 based on <expert-advice>. So we show its premise.
      have h19 : (p5 ∨ ((p3 ∧ (p1 ∨ True)) → ((False → p3) → p4))) := by
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- Implications on the right can always be decomposed.
        intro h20
        -- Implications on the right can always be decomposed.
        intro h21
        -- Conjunctions on the left can always be decomposed.
        let h22 := h20.left
        let h23 := h20.right
        -- Disjunctions on the left can always be decomposed.
        cases h23
        case inl h24 =>
          -- One of the premise coincides with the conclusion.
          exact h17
        case inr h25 =>
          -- One of the premise coincides with the conclusion.
          exact h17
      -- We have shown the premise of h18, we can now drive its conclusion.
      let h26 := h18 h19
      -- One of the premise coincides with the conclusion.
      exact h26
    case inr h27 =>
      -- Conjunctions on the left can always be decomposed.
      let h28 := h3.left
      let h29 := h3.right
      -- We want to use the implication h29 based on <expert-advice>. So we show its premise.
      have h30 : (p5 ∨ ((p3 ∧ (p1 ∨ True)) → ((False → p3) → p4))) := by
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- Implications on the right can always be decomposed.
        intro h31
        -- Implications on the right can always be decomposed.
        intro h32
        -- Conjunctions on the left can always be decomposed.
        let h33 := h31.left
        let h34 := h31.right
        -- Disjunctions on the left can always be decomposed.
        cases h34
        case inl h35 =>
          -- One of the premise coincides with the conclusion.
          exact h28
        case inr h36 =>
          -- One of the premise coincides with the conclusion.
          exact h28
      -- We have shown the premise of h29, we can now drive its conclusion.
      let h37 := h29 h30
      -- One of the premise coincides with the conclusion.
      exact h37
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Conjunctions on the left can always be decomposed.
  let h38 := h1.left
  let h39 := h1.right
  -- Disjunctions on the left can always be decomposed.
  cases h38
  case inl h40 =>
    -- Conjunctions on the left can always be decomposed.
    let h41 := h39.left
    let h42 := h39.right
    -- We want to use the implication h42 based on <expert-advice>. So we show its premise.
    have h43 : (p5 ∨ ((p3 ∧ (p1 ∨ True)) → ((False → p3) → p4))) := by
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Implications on the right can always be decomposed.
      intro h44
      -- Implications on the right can always be decomposed.
      intro h45
      -- Conjunctions on the left can always be decomposed.
      let h46 := h44.left
      let h47 := h44.right
      -- Disjunctions on the left can always be decomposed.
      cases h47
      case inl h48 =>
        -- One of the premise coincides with the conclusion.
        exact h41
      case inr h49 =>
        -- One of the premise coincides with the conclusion.
        exact h41
    -- We have shown the premise of h42, we can now drive its conclusion.
    let h50 := h42 h43
    -- One of the premise coincides with the conclusion.
    exact h50
  case inr h51 =>
    -- Disjunctions on the left can always be decomposed.
    cases h51
    case inl h52 =>
      -- Conjunctions on the left can always be decomposed.
      let h53 := h39.left
      let h54 := h39.right
      -- We want to use the implication h54 based on <expert-advice>. So we show its premise.
      have h55 : (p5 ∨ ((p3 ∧ (p1 ∨ True)) → ((False → p3) → p4))) := by
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- Implications on the right can always be decomposed.
        intro h56
        -- Implications on the right can always be decomposed.
        intro h57
        -- Conjunctions on the left can always be decomposed.
        let h58 := h56.left
        let h59 := h56.right
        -- Disjunctions on the left can always be decomposed.
        cases h59
        case inl h60 =>
          -- One of the premise coincides with the conclusion.
          exact h53
        case inr h61 =>
          -- One of the premise coincides with the conclusion.
          exact h53
      -- We have shown the premise of h54, we can now drive its conclusion.
      let h62 := h54 h55
      -- One of the premise coincides with the conclusion.
      exact h62
    case inr h63 =>
      -- Conjunctions on the left can always be decomposed.
      let h64 := h39.left
      let h65 := h39.right
      -- We want to use the implication h65 based on <expert-advice>. So we show its premise.
      have h66 : (p5 ∨ ((p3 ∧ (p1 ∨ True)) → ((False → p3) → p4))) := by
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- Implications on the right can always be decomposed.
        intro h67
        -- Implications on the right can always be decomposed.
        intro h68
        -- Conjunctions on the left can always be decomposed.
        let h69 := h67.left
        let h70 := h67.right
        -- Disjunctions on the left can always be decomposed.
        cases h70
        case inl h71 =>
          -- One of the premise coincides with the conclusion.
          exact h64
        case inr h72 =>
          -- One of the premise coincides with the conclusion.
          exact h64
      -- We have shown the premise of h65, we can now drive its conclusion.
      let h73 := h65 h66
      -- One of the premise coincides with the conclusion.
      exact h73
  -- Conjunctions on the left can always be decomposed.
  let h74 := h1.left
  let h75 := h1.right
  -- Disjunctions on the left can always be decomposed.
  cases h74
  case inl h76 =>
    -- Conjunctions on the left can always be decomposed.
    let h77 := h75.left
    let h78 := h75.right
    -- We want to use the implication h78 based on <expert-advice>. So we show its premise.
    have h79 : (p5 ∨ ((p3 ∧ (p1 ∨ True)) → ((False → p3) → p4))) := by
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Implications on the right can always be decomposed.
      intro h80
      -- Implications on the right can always be decomposed.
      intro h81
      -- Conjunctions on the left can always be decomposed.
      let h82 := h80.left
      let h83 := h80.right
      -- Disjunctions on the left can always be decomposed.
      cases h83
      case inl h84 =>
        -- One of the premise coincides with the conclusion.
        exact h77
      case inr h85 =>
        -- One of the premise coincides with the conclusion.
        exact h77
    -- We have shown the premise of h78, we can now drive its conclusion.
    let h86 := h78 h79
    -- One of the premise coincides with the conclusion.
    exact h86
  case inr h87 =>
    -- Disjunctions on the left can always be decomposed.
    cases h87
    case inl h88 =>
      -- Conjunctions on the left can always be decomposed.
      let h89 := h75.left
      let h90 := h75.right
      -- We want to use the implication h90 based on <expert-advice>. So we show its premise.
      have h91 : (p5 ∨ ((p3 ∧ (p1 ∨ True)) → ((False → p3) → p4))) := by
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- Implications on the right can always be decomposed.
        intro h92
        -- Implications on the right can always be decomposed.
        intro h93
        -- Conjunctions on the left can always be decomposed.
        let h94 := h92.left
        let h95 := h92.right
        -- Disjunctions on the left can always be decomposed.
        cases h95
        case inl h96 =>
          -- One of the premise coincides with the conclusion.
          exact h89
        case inr h97 =>
          -- One of the premise coincides with the conclusion.
          exact h89
      -- We have shown the premise of h90, we can now drive its conclusion.
      let h98 := h90 h91
      -- One of the premise coincides with the conclusion.
      exact h98
    case inr h99 =>
      -- Conjunctions on the left can always be decomposed.
      let h100 := h75.left
      let h101 := h75.right
      -- We want to use the implication h101 based on <expert-advice>. So we show its premise.
      have h102 : (p5 ∨ ((p3 ∧ (p1 ∨ True)) → ((False → p3) → p4))) := by
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- Implications on the right can always be decomposed.
        intro h103
        -- Implications on the right can always be decomposed.
        intro h104
        -- Conjunctions on the left can always be decomposed.
        let h105 := h103.left
        let h106 := h103.right
        -- Disjunctions on the left can always be decomposed.
        cases h106
        case inl h107 =>
          -- One of the premise coincides with the conclusion.
          exact h100
        case inr h108 =>
          -- One of the premise coincides with the conclusion.
          exact h100
      -- We have shown the premise of h101, we can now drive its conclusion.
      let h109 := h101 h102
      -- One of the premise coincides with the conclusion.
      exact h109



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_208613406108954169264016305408 : (((p5 → p4) → ((True → p1) → p3)) → ((p3 ∧ p1) ∨ (((((p2 ∧ True) ∨ p5) ∧ (p1 → p2)) ∧ (p5 → p5)) ∨ (True ∨ (p5 ∧ p2))))) := by
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
theorem thm_5_vars_57631287965750101300544374278 : ((((p3 ∧ p3) ∨ True) → ((False ∨ (p1 ∨ p4)) ∨ (((p4 ∧ (p4 → p3)) ∨ (True ∨ (p4 ∨ (p5 ∧ p4)))) ∨ ((True → False) ∨ p5)))) ∨ p1) := by
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
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- True on the right can always be proven directly.
    apply True.intro
  case inr h5 =>
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
theorem thm_5_vars_345528514394584164575833062816 : (p3 → ((((((p5 ∨ p3) → p5) → False) ∨ ((p2 ∧ True) ∧ p4)) ∨ ((((((True → p3) ∧ True) ∧ True) → p4) ∨ p4) → (True ∧ p3))) ∨ p3)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_136272156750973333911332186194 : ((((p2 ∨ ((True → p2) → True)) → p2) → (p5 ∧ (p3 ∧ (p1 → (((p3 ∨ True) ∧ ((p2 → True) → p3)) ∧ True))))) ∨ ((p5 ∨ True) ∨ p1)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_113330025370553307848453796518 : ((((p1 ∧ p3) ∨ (p3 → (((((p5 → True) ∨ p2) ∨ (((p1 → p1) ∨ p1) ∧ p4)) ∨ p4) ∨ (p4 ∨ p5)))) ∧ (False ∨ p1)) ∨ (p2 ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_51230695910478082622877144774 : ((((p4 ∨ ((p2 ∧ p1) ∨ False)) ∨ ((p5 ∧ (p3 ∨ (p1 ∨ (p4 ∧ False)))) ∨ (False → p4))) ∨ (p1 → (((True ∨ True) → p5) ∨ p2))) ∨ False) := by
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
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_352592150533508821684104610967 : (p4 → ((False → p4) ∧ (p5 → ((((p4 ∨ ((((True ∨ p2) ∨ p5) ∧ (True → p5)) ∨ ((p2 → True) ∧ (p3 ∧ p1)))) → p2) ∧ p3) ∨ p5)))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h2
  -- False on the left can always be used.
  apply False.elim h2
  -- Implications on the right can always be decomposed.
  intro h3
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h3



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_55600766875835532942692737692 : (((True → ((p3 ∧ (p3 ∧ p1)) → p3)) → (p2 → (p4 ∨ (False ∧ ((p2 → ((p1 ∧ p2) → False)) ∧ (True ∨ ((p5 ∨ p5) ∨ False))))))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_41229609861095693664637598098 : ((((((True ∨ p3) ∨ p3) → ((p1 ∨ (((p2 → (p4 ∧ p4)) → p5) ∨ True)) ∧ (p2 ∨ p4))) ∧ (((False → p5) → p2) ∨ p5)) ∨ p5) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_40716111674267526676454098265 : (((((((p1 → True) ∨ (p3 ∨ (p3 ∧ False))) ∧ p3) ∨ ((p5 → (((p1 → False) ∧ (p3 ∧ (True → p4))) ∨ False)) → p1)) → p1) ∨ True) ∨ False) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_180839509116857773139855796408 : ((((p1 ∨ False) ∧ p4) ∨ (p3 ∧ (p4 ∨ (p5 ∧ (True ∧ (p1 ∨ True)))))) → (p3 → (((p1 ∨ p4) ∨ p3) ∧ (p4 ∨ ((False ∨ p5) ∧ p5))))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h3 =>
    -- Conjunctions on the left can always be decomposed.
    let h4 := h3.left
    let h5 := h3.right
    -- Disjunctions on the left can always be decomposed.
    cases h4
    case inl h6 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- One of the premise coincides with the conclusion.
      exact h2
    case inr h7 =>
      -- False on the left can always be used.
      apply False.elim h7
  case inr h8 =>
    -- Conjunctions on the left can always be decomposed.
    let h9 := h8.left
    let h10 := h8.right
    -- Disjunctions on the left can always be decomposed.
    cases h10
    case inl h11 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- One of the premise coincides with the conclusion.
      exact h9
    case inr h12 =>
      -- Conjunctions on the left can always be decomposed.
      let h13 := h12.left
      let h14 := h12.right
      -- Conjunctions on the left can always be decomposed.
      let h15 := h14.left
      let h16 := h14.right
      -- Disjunctions on the left can always be decomposed.
      cases h16
      case inl h17 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- One of the premise coincides with the conclusion.
        exact h9
      case inr h18 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- One of the premise coincides with the conclusion.
        exact h9
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h19 =>
    -- Conjunctions on the left can always be decomposed.
    let h20 := h19.left
    let h21 := h19.right
    -- Disjunctions on the left can always be decomposed.
    cases h20
    case inl h22 =>
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- One of the premise coincides with the conclusion.
      exact h21
    case inr h23 =>
      -- False on the left can always be used.
      apply False.elim h23
  case inr h24 =>
    -- Conjunctions on the left can always be decomposed.
    let h25 := h24.left
    let h26 := h24.right
    -- Disjunctions on the left can always be decomposed.
    cases h26
    case inl h27 =>
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- One of the premise coincides with the conclusion.
      exact h27
    case inr h28 =>
      -- Conjunctions on the left can always be decomposed.
      let h29 := h28.left
      let h30 := h28.right
      -- Conjunctions on the left can always be decomposed.
      let h31 := h30.left
      let h32 := h30.right
      -- Disjunctions on the left can always be decomposed.
      cases h32
      case inl h33 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- Conjunctions on the right can always be decomposed.
        apply And.intro
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- One of the premise coincides with the conclusion.
        exact h29
        -- One of the premise coincides with the conclusion.
        exact h29
      case inr h34 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- Conjunctions on the right can always be decomposed.
        apply And.intro
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- One of the premise coincides with the conclusion.
        exact h29
        -- One of the premise coincides with the conclusion.
        exact h29



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_255502447622832473321870460676 : ((p5 ∧ p2) → (((((True → p3) ∧ p4) ∧ False) ∨ ((p3 ∨ ((p1 ∨ ((p5 ∧ p2) ∧ p3)) ∧ p4)) ∨ p4)) ∨ ((True ∨ p4) ∨ (p5 ∨ p1)))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_115977089572913359496540153218 : (((((False → p4) ∧ True) ∨ p1) → (p4 → (p4 ∧ (p1 ∨ (((p1 ∧ p1) ∧ ((p1 ∨ (p4 → (True → p2))) → p5)) → p4))))) ∨ (p3 ∨ p3)) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h3 =>
    -- Conjunctions on the left can always be decomposed.
    let h4 := h3.left
    let h5 := h3.right
    -- One of the premise coincides with the conclusion.
    exact h2
  case inr h6 =>
    -- One of the premise coincides with the conclusion.
    exact h2
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h7 =>
    -- Conjunctions on the left can always be decomposed.
    let h8 := h7.left
    let h9 := h7.right
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h10
    -- Conjunctions on the left can always be decomposed.
    let h11 := h10.left
    let h12 := h10.right
    -- Conjunctions on the left can always be decomposed.
    let h13 := h11.left
    let h14 := h11.right
    -- One of the premise coincides with the conclusion.
    exact h2
  case inr h15 =>
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- One of the premise coincides with the conclusion.
    exact h15



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_351756301001883167954274710733 : (p4 → (((((p4 → (p3 ∨ (p1 → p2))) ∧ (p4 → p5)) ∨ False) ∧ (False → p5)) → ((((p3 ∧ ((p3 ∨ p2) ∨ p2)) → p2) ∧ True) ∨ p5))) := by
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
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- We want to use the implication h7 based on <expert-advice>. So we show its premise.
    have h8 : p4 := by
      -- One of the premise coincides with the conclusion.
      exact h1
    -- We have shown the premise of h7, we can now drive its conclusion.
    let h9 := h7 h8
    -- One of the premise coincides with the conclusion.
    exact h9
  case inr h10 =>
    -- False on the left can always be used.
    apply False.elim h10



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_699191077672348283384184108825 : ((((p2 → ((p2 ∨ (p3 ∧ ((p2 → p4) → p4))) → (p5 ∨ p5))) ∨ ((((p1 → (p4 → p3)) → (p3 ∨ p5)) ∧ (True ∨ True)) → p3)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_76278867103687461852320510544 : (((((((p4 ∧ p4) ∧ ((p1 → (p3 ∨ ((p5 → p5) → ((False ∧ (False ∨ p3)) → p3)))) → p4)) → p5) → p4) ∨ (True ∨ p5)) → p1) → p1) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h2 : (((((p4 ∧ p4) ∧ ((p1 → (p3 ∨ ((p5 → p5) → ((False ∧ (False ∨ p3)) → p3)))) → p4)) → p5) → p4) ∨ (True ∨ p5)) := by
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h3 := h1 h2
  -- One of the premise coincides with the conclusion.
  exact h3



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_165434682552638673343878168596 : (((p5 ∧ (True → (p5 → ((p5 → (True → (False ∨ p5))) → p4)))) → (p3 ∧ (p3 ∨ p1))) ∨ (True ∨ ((p1 ∨ (True ∧ (p5 ∨ p5))) ∧ p2))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_767498547352505773940235439213 : (((p5 ∧ (((p1 ∧ ((True → p5) ∧ (p2 ∧ ((p3 ∨ (True ∧ (False ∧ (((p1 ∨ p4) ∧ True) ∨ (p5 ∧ p1))))) ∧ p3)))) ∨ p1) ∨ p3)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_343398373239125867399868159297 : (p2 → ((p3 ∧ False) ∨ ((((((p2 ∨ (p4 → p4)) ∧ p3) → p5) ∨ (p2 → (p4 → ((p2 ∨ ((p2 ∨ p3) ∧ p5)) → p3)))) → p1) ∨ p2))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_186973996394844742049183778596 : (((True ∨ (p3 ∨ p1)) ∨ ((p5 → p5) → (p2 → (p1 ∧ p3)))) → (False ∨ (p3 → (False ∨ (p3 → (((True ∨ True) ∨ p5) ∨ (True ∨ True))))))) := by
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
      -- Implications on the right can always be decomposed.
      intro h5
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
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
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- Implications on the right can always be decomposed.
        intro h9
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- True on the right can always be proven directly.
        apply True.intro
      case inr h10 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- Implications on the right can always be decomposed.
        intro h11
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- Implications on the right can always be decomposed.
        intro h12
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- True on the right can always be proven directly.
        apply True.intro
  case inr h13 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h14
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h15
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- True on the right can always be proven directly.
    apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_680149145949893767784625595971 : (((((p3 → (False → ((((p3 ∧ p4) → (p1 ∧ p2)) → (p1 ∧ (p1 ∧ True))) ∧ p3))) ∧ (p4 → p5)) → (p1 ∨ (p1 ∧ (p4 → p3)))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_322539703307836959863746637467 : (p5 ∨ ((p5 ∧ (((p1 ∨ p4) ∨ ((((True ∨ (p4 ∨ False)) ∧ p2) ∧ (p1 ∨ p3)) → False)) → (p1 ∨ (p1 → ((p2 → p3) ∧ True))))) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_179419501266093116237675412403 : ((p4 ∨ (((p5 ∧ (p2 ∧ p5)) ∨ ((p3 ∨ False) ∧ p2)) ∨ (True → True))) ∨ (((((False ∧ True) ∧ ((True ∧ p5) ∧ p4)) → False) ∧ False) ∧ p1)) := by
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



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_695341742139902377058001992508 : (((((True ∨ (p2 ∧ ((p4 ∧ (True ∨ False)) → ((p5 → p5) ∧ p3)))) → p3) → (((p4 → (p1 ∧ ((p4 → p3) ∨ p4))) → p4) ∨ p3)) ∨ False) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h2 : (True ∨ (p2 ∧ ((p4 ∧ (True ∨ False)) → ((p5 → p5) ∧ p3)))) := by
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h3 := h1 h2
  -- One of the premise coincides with the conclusion.
  exact h3
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_614021228336256814789710168118 : ((((((p3 ∧ False) ∧ ((((p4 ∨ (p5 ∧ p2)) ∧ ((p4 ∧ p4) → (p3 ∨ (p2 ∨ p3)))) → p3) ∧ p1)) ∨ ((p1 ∧ p3) ∧ False)) ∨ p4) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_113000903637605904500074226879 : (((p4 ∧ (((p3 ∧ (((p5 ∧ p1) ∨ p2) → p5)) → ((((False → (True ∨ False)) → False) ∧ p2) → (p4 → p1))) ∨ p4)) → False) ∨ (p4 → True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_319661013178864599239633551725 : (p4 ∨ (((p1 ∧ (p4 ∧ (p5 ∨ (p1 → True)))) ∧ p2) → (((p2 ∨ False) ∨ (p1 ∨ p1)) ∧ (p4 ∧ (((p3 → p4) → (p4 ∧ False)) ∨ p4))))) := by
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
  -- Disjunctions on the left can always be decomposed.
  cases h7
  case inl h8 =>
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- One of the premise coincides with the conclusion.
    exact h3
  case inr h9 =>
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- One of the premise coincides with the conclusion.
    exact h3
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Conjunctions on the left can always be decomposed.
  let h10 := h1.left
  let h11 := h1.right
  -- Conjunctions on the left can always be decomposed.
  let h12 := h10.left
  let h13 := h10.right
  -- Conjunctions on the left can always be decomposed.
  let h14 := h13.left
  let h15 := h13.right
  -- Disjunctions on the left can always be decomposed.
  cases h15
  case inl h16 =>
    -- One of the premise coincides with the conclusion.
    exact h14
  case inr h17 =>
    -- One of the premise coincides with the conclusion.
    exact h14
  -- Conjunctions on the left can always be decomposed.
  let h18 := h1.left
  let h19 := h1.right
  -- Conjunctions on the left can always be decomposed.
  let h20 := h18.left
  let h21 := h18.right
  -- Conjunctions on the left can always be decomposed.
  let h22 := h21.left
  let h23 := h21.right
  -- Disjunctions on the left can always be decomposed.
  cases h23
  case inl h24 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h22
  case inr h25 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h22



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_157669566272922710477333052116 : ((((p3 ∨ (((p4 → False) → p5) ∧ p2)) ∨ (((False ∧ p5) ∨ p4) ∨ p4)) ∨ (p2 → (True ∨ True))) ∨ ((p2 ∧ ((p3 ∧ p2) ∨ p2)) ∨ p2)) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_42882194210278509166547359490 : (((p3 → ((p3 ∧ ((((p1 → p3) → ((((p1 ∨ ((False ∧ p1) → p3)) ∧ p4) ∧ True) ∨ p5)) ∧ p2) ∨ (True ∨ p3))) ∧ p4)) ∨ True) ∨ p2) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_646817055490299419833953758213 : ((((p2 → (((p4 ∧ (((p2 ∨ p4) ∨ p4) ∨ True)) ∧ p5) ∨ ((p2 ∧ ((p5 → p2) → (p5 ∨ False))) → (True ∧ (True ∧ p5))))) → False) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_316420263165571541459507330446 : (p3 ∨ (p1 ∨ (((((p3 ∨ (p1 ∧ p4)) ∨ p1) ∨ ((p1 ∨ ((p4 ∨ False) ∨ (True ∧ ((True → (p1 → True)) ∨ p4)))) ∨ p5)) ∨ p2) ∧ True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
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
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_147985198292164543911497138284 : (((((p1 ∨ (p5 ∨ ((((p3 ∧ p3) ∧ p5) ∨ p5) ∧ ((p4 ∧ True) ∨ p4)))) ∧ p1) ∨ p4) ∨ (False → p1)) ∨ (False → (False ∧ (False → True)))) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_234286162626487178982785130517 : ((False → (p3 → p3)) → (((p1 ∧ p5) ∧ ((p5 → (p4 ∧ (True ∨ True))) ∧ p4)) → (((((p2 ∧ True) → (False → p1)) ∧ p1) → True) → p4))) := by
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
  -- Conjunctions on the left can always be decomposed.
  let h8 := h5.left
  let h9 := h5.right
  -- One of the premise coincides with the conclusion.
  exact h9



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_191480316350924697257024091235 : ((True ∧ (((p5 ∧ p2) ∨ (p2 → p3)) → (p5 ∧ p1))) ∨ (((((p4 ∨ p3) → p4) → (True ∧ p4)) → True) ∧ ((p3 ∨ (p2 ∧ True)) ∨ True))) := by
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
theorem thm_5_vars_807447545450469002575647195506 : (((p4 → ((((p5 ∧ False) ∨ True) → ((p3 → False) ∨ p1)) ∨ ((p3 ∨ (p2 ∨ (p3 ∨ (((p1 → p1) ∧ (p2 → True)) → True)))) ∨ p2))) ∨ p4) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
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
  intro h2
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_64424819720320168213271393268 : ((p1 ∨ (((p1 ∧ ((False ∧ ((False → (p3 ∧ (p1 ∨ ((p2 ∨ p5) ∨ p2)))) ∨ p3)) ∧ ((p4 ∧ True) ∨ p5))) ∧ p1) ∧ (p2 ∨ False))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_652368220307071033437833831712 : ((((p4 ∧ ((((False ∧ (p1 → False)) ∧ p1) ∧ p1) ∧ (False ∨ ((((p1 → ((False ∨ p2) → p4)) → p4) ∧ p4) ∧ p4)))) ∧ (False ∧ False)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_4118996490499934220606515796 : (p3 ∨ ((p5 ∨ False) ∨ (((False ∧ (False ∨ (p5 ∨ True))) ∨ (False ∨ p1)) ∨ ((True → (False ∧ p2)) ∨ (p4 ∨ (False ∨ (p2 → p2))))))) := by
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
  -- Implications on the right can always be decomposed.
  intro h1
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_116671349094794471638652890224 : (((p5 → False) ∧ (((((p2 ∧ (True ∨ p1)) → p4) ∧ p5) → (p5 → (p4 ∨ (((p4 ∨ True) ∨ True) → (p5 ∧ False))))) → p2)) ∨ (True ∨ p3)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_637054533187076637356571762740 : (((((False → (((p2 → ((p1 ∧ p5) ∨ p4)) ∨ True) → (p5 ∨ p5))) ∧ (p2 ∨ ((p2 ∨ (p5 → p4)) → (p1 → (True ∧ False))))) → p2) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_46123840495252515362727226552 : ((((p2 → (((p1 ∧ p2) ∨ ((True ∨ False) → (p4 ∨ p1))) ∧ (p3 → (p1 ∨ ((p3 ∧ p3) ∧ (p2 → True)))))) ∨ p5) ∧ (True ∧ True)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_244891592045076337718620112878 : ((p1 ∧ p2) ∨ ((p3 → p1) ∨ ((p5 → (((False ∧ (((p1 ∨ (p2 ∨ False)) → p4) → (p5 → p4))) ∨ p1) ∨ (True ∧ False))) ∨ (p1 ∨ True)))) := by
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
theorem thm_5_vars_661139720686342000322946382222 : (((((((((p2 → (p2 ∧ True)) ∧ (((False → p1) ∧ (p4 ∧ p2)) ∨ True)) ∨ True) ∧ (p4 ∨ p5)) ∨ p2) ∨ (p5 ∨ p3)) → (p5 ∨ True)) ∨ p4) ∧ True) := by
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
      -- Conjunctions on the left can always be decomposed.
      let h4 := h3.left
      let h5 := h3.right
      -- Disjunctions on the left can always be decomposed.
      cases h4
      case inl h6 =>
        -- Conjunctions on the left can always be decomposed.
        let h7 := h6.left
        let h8 := h6.right
        -- Disjunctions on the left can always be decomposed.
        cases h8
        case inl h9 =>
          -- Conjunctions on the left can always be decomposed.
          let h10 := h9.left
          let h11 := h9.right
          -- Conjunctions on the left can always be decomposed.
          let h12 := h11.left
          let h13 := h11.right
          -- Disjunctions on the left can always be decomposed.
          cases h5
          case inl h14 =>
            -- Show the right disjunct based on <expert-advice>.
            apply Or.inr
            -- True on the right can always be proven directly.
            apply True.intro
          case inr h15 =>
            -- Show the left disjunct based on <expert-advice>.
            apply Or.inl
            -- One of the premise coincides with the conclusion.
            exact h15
        case inr h16 =>
          -- Disjunctions on the left can always be decomposed.
          cases h5
          case inl h17 =>
            -- Show the right disjunct based on <expert-advice>.
            apply Or.inr
            -- True on the right can always be proven directly.
            apply True.intro
          case inr h18 =>
            -- Show the left disjunct based on <expert-advice>.
            apply Or.inl
            -- One of the premise coincides with the conclusion.
            exact h18
      case inr h19 =>
        -- Disjunctions on the left can always be decomposed.
        cases h5
        case inl h20 =>
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- True on the right can always be proven directly.
          apply True.intro
        case inr h21 =>
          -- Show the left disjunct based on <expert-advice>.
          apply Or.inl
          -- One of the premise coincides with the conclusion.
          exact h21
    case inr h22 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- True on the right can always be proven directly.
      apply True.intro
  case inr h23 =>
    -- Disjunctions on the left can always be decomposed.
    cases h23
    case inl h24 =>
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- One of the premise coincides with the conclusion.
      exact h24
    case inr h25 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- True on the right can always be proven directly.
      apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_156912230622119895333346171789 : ((((((True ∧ True) ∨ (((((p3 ∨ p2) ∨ p4) ∧ p4) ∨ False) ∨ True)) ∨ (True → False)) → False) ∨ p2) ∨ ((True → ((p3 ∧ p4) ∨ True)) ∧ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
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



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_147625910978213603232178442482 : (((((p4 ∨ ((False → p3) ∨ (True ∧ ((((False → (p5 ∧ p1)) ∨ p2) → False) → p2)))) → p5) → p5) → False) ∨ (True ∨ ((True → p4) → p4))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_217188016603357287928147716680 : ((((False ∨ p2) → p5) ∨ p4) → ((False ∨ ((p4 ∨ True) ∧ (p4 ∧ (p1 ∨ ((False ∨ (p1 ∧ p5)) ∧ (True ∨ (p4 ∧ p4))))))) ∨ (True ∨ True))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h2 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- True on the right can always be proven directly.
    apply True.intro
  case inr h3 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- True on the right can always be proven directly.
    apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_593805215757978088290089179628 : (((((True → (((p1 → p2) ∨ (p3 ∧ (p2 ∧ ((p5 ∨ True) ∧ p1)))) ∨ (False ∧ (p2 ∧ True)))) ∧ (p3 → ((p4 ∨ p1) ∨ p3))) ∧ p3) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_39362543907512195308469743303 : (((p3 ∧ ((True ∧ (True ∧ (((False ∨ p2) → (p1 ∨ p3)) → ((((True ∧ (p3 ∨ True)) → p2) ∧ (False ∧ p5)) → p3)))) → False)) ∧ True) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_136305127949658166658352134510 : (((((False → True) → False) ∧ p5) ∧ (((p4 → ((((p2 ∧ (p1 ∨ p1)) → p4) → (False ∨ True)) ∧ True)) → True) ∧ p3)) ∨ (True ∨ (False ∨ p1))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_38457398696922961265125994091 : ((((((p4 → (p4 ∧ (p1 ∧ (False → p2)))) → p3) ∧ (p4 ∧ (True ∨ False))) → (((p3 → p3) ∨ ((True ∧ p2) → p3)) → False)) ∧ p5) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_319470103751423717917319337694 : (p4 ∨ ((p3 ∨ ((p3 → (p1 → (False ∨ ((p2 ∨ p5) ∨ True)))) ∧ True)) ∨ ((((((p5 ∧ p3) ∨ p3) ∧ p4) ∨ p2) → (False ∨ p1)) → p4))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
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
theorem thm_5_vars_148598566708485329366915650078 : (((p4 ∧ ((False ∨ ((False ∧ p2) ∧ p2)) ∧ (p1 → True))) ∨ ((False ∨ (p2 ∨ (p1 ∧ (p3 ∨ p2)))) → p3)) ∨ (((p2 ∧ True) ∨ p2) → True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_40471330015113756600851536401 : ((((((p1 ∨ p1) → p3) → ((False ∨ (((True → (False → (p4 ∨ (p5 → p2)))) ∧ (p4 → p1)) ∨ (True ∧ False))) → False)) ∨ p5) ∨ p2) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_57719352620826305351531807547 : ((((True ∨ p2) → p5) → (((p5 ∧ (False → ((p5 → p1) ∧ (((p4 → (p3 ∧ (p5 → (True ∨ p5)))) ∨ True) ∧ p4)))) ∨ p3) → False)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_209257028990639104673406421497 : ((p5 ∨ (True ∨ (True ∨ (False → p4)))) → (((p5 ∧ ((p2 ∧ ((p1 → (False ∨ True)) → p3)) ∨ ((p2 → p3) ∧ p4))) ∨ (p3 → p3)) ∨ p3)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h2 =>
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
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
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Implications on the right can always be decomposed.
      intro h6
      -- One of the premise coincides with the conclusion.
      exact h6
    case inr h7 =>
      -- Disjunctions on the left can always be decomposed.
      cases h7
      case inl h8 =>
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- Implications on the right can always be decomposed.
        intro h9
        -- One of the premise coincides with the conclusion.
        exact h9
      case inr h10 =>
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- Implications on the right can always be decomposed.
        intro h11
        -- One of the premise coincides with the conclusion.
        exact h11



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_180712747338708360961036697601 : ((((False ∨ p4) ∨ (p4 ∧ True)) ∧ ((p1 ∧ p5) → (p2 ∨ (p5 ∧ p3)))) → ((p4 → (p2 ∧ ((True ∧ p3) ∧ True))) ∨ (p4 ∧ (p5 → True)))) := by
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
      -- False on the left can always be used.
      apply False.elim h5
    case inr h6 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Conjunctions on the right can always be decomposed.
      apply And.intro
      -- One of the premise coincides with the conclusion.
      exact h6
      -- Implications on the right can always be decomposed.
      intro h7
      -- True on the right can always be proven directly.
      apply True.intro
  case inr h8 =>
    -- Conjunctions on the left can always be decomposed.
    let h9 := h8.left
    let h10 := h8.right
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Conjunctions on the right can always be decomposed.
    apply And.intro
    -- One of the premise coincides with the conclusion.
    exact h9
    -- Implications on the right can always be decomposed.
    intro h11
    -- True on the right can always be proven directly.
    apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_862788064104483911157790600294 : (((((True → ((((p5 → False) ∨ p4) → (p2 ∨ (p5 ∨ p5))) ∧ ((False ∨ p5) ∧ True))) ∨ (False → (p4 ∨ (p2 ∧ (p3 ∨ False))))) → p2) → p2) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h1
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h2 : ((True → ((((p5 → False) ∨ p4) → (p2 ∨ (p5 ∨ p5))) ∧ ((False ∨ p5) ∧ True))) ∨ (False → (p4 ∨ (p2 ∧ (p3 ∨ False))))) := by
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h3
    -- False on the left can always be used.
    apply False.elim h3
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h4 := h1 h2
  -- One of the premise coincides with the conclusion.
  exact h4
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_50190281743059721560420907387 : (((((True ∨ p3) → (False ∧ (((False → p2) → (p2 → (((True → p5) ∧ True) ∧ p3))) → True))) ∧ p3) ∨ ((p3 ∨ False) ∨ (False → False))) ∨ p1) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_158810459267650100699885858632 : ((p5 ∧ (p3 ∨ (((((False ∨ False) ∧ (p2 ∨ True)) ∧ True) ∧ p1) ∨ ((p2 ∨ (p4 ∧ p4)) ∨ p2)))) ∨ ((p5 ∨ (False → True)) ∨ (False → p2))) := by
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
theorem thm_5_vars_781180091843186871844782812920 : (((p2 ∨ ((True ∨ p1) → ((p1 ∨ p3) → ((p5 ∨ p3) ∨ ((((p1 ∨ p4) ∧ p4) ∨ (p1 ∨ (p5 ∧ ((p2 ∧ False) → p3)))) ∧ p1))))) ∨ p4) ∧ True) := by
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
  -- Disjunctions on the left can always be decomposed.
  cases h2
  case inl h3 =>
    -- Disjunctions on the left can always be decomposed.
    cases h1
    case inl h4 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Conjunctions on the right can always be decomposed.
      apply And.intro
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- One of the premise coincides with the conclusion.
      exact h3
      -- One of the premise coincides with the conclusion.
      exact h3
    case inr h5 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Conjunctions on the right can always be decomposed.
      apply And.intro
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- One of the premise coincides with the conclusion.
      exact h5
      -- One of the premise coincides with the conclusion.
      exact h5
  case inr h6 =>
    -- Disjunctions on the left can always be decomposed.
    cases h1
    case inl h7 =>
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- One of the premise coincides with the conclusion.
      exact h6
    case inr h8 =>
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- One of the premise coincides with the conclusion.
      exact h6
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_135714300752730515950398307771 : (((False ∨ (((p1 ∨ p2) ∧ p4) → ((((True ∧ p1) → False) ∨ p3) ∨ True))) ∧ (True → (p4 ∨ (p1 → (p5 ∧ p3))))) ∨ (True ∧ (True ∧ True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_637724857432225196109741705979 : (((((((p3 ∨ (p3 ∨ p3)) ∧ True) → (True ∨ (p3 ∧ p5))) → ((True ∨ p3) ∧ ((((p3 ∨ True) ∧ (p4 ∨ p1)) → p5) ∧ p2))) → p3) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_123434064118234016114346510283 : (((((False ∨ True) → False) → (p3 ∧ ((p4 ∧ (((p3 → (p3 → p5)) ∨ True) ∧ False)) ∧ False))) → (((p2 ∨ p4) → p4) ∧ p2)) → (p2 ∨ p4)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h2 : (((False ∨ True) → False) → (p3 ∧ ((p4 ∧ (((p3 → (p3 → p5)) ∨ True) ∧ False)) ∧ False))) := by
    -- Implications on the right can always be decomposed.
    intro h3
    -- Conjunctions on the right can always be decomposed.
    apply And.intro
    -- We want to use the implication h3 based on <expert-advice>. So we show its premise.
    have h4 : (False ∨ True) := by
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- True on the right can always be proven directly.
      apply True.intro
    -- We have shown the premise of h3, we can now drive its conclusion.
    let h5 := h3 h4
    -- False on the left can always be used.
    apply False.elim h5
    -- Conjunctions on the right can always be decomposed.
    apply And.intro
    -- Conjunctions on the right can always be decomposed.
    apply And.intro
    -- We want to use the implication h3 based on <expert-advice>. So we show its premise.
    have h6 : (False ∨ True) := by
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- True on the right can always be proven directly.
      apply True.intro
    -- We have shown the premise of h3, we can now drive its conclusion.
    let h7 := h3 h6
    -- False on the left can always be used.
    apply False.elim h7
    -- Conjunctions on the right can always be decomposed.
    apply And.intro
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro
    -- We want to use the implication h3 based on <expert-advice>. So we show its premise.
    have h8 : (False ∨ True) := by
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- True on the right can always be proven directly.
      apply True.intro
    -- We have shown the premise of h3, we can now drive its conclusion.
    let h9 := h3 h8
    -- False on the left can always be used.
    apply False.elim h9
    -- We want to use the implication h3 based on <expert-advice>. So we show its premise.
    have h10 : (False ∨ True) := by
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- True on the right can always be proven directly.
      apply True.intro
    -- We have shown the premise of h3, we can now drive its conclusion.
    let h11 := h3 h10
    -- False on the left can always be used.
    apply False.elim h11
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h12 := h1 h2
  -- We need to get the right conjuct of h12 based on <expert-advice>.
  let h13 := h12.right
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- One of the premise coincides with the conclusion.
  exact h13



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_42283078976225629083459089417 : (((p1 ∧ (p1 ∨ (p3 ∨ ((p3 → False) ∨ (p5 ∨ ((p5 → (False → p4)) ∨ (p4 ∧ ((p3 ∧ False) ∧ ((True ∨ p3) ∨ p4))))))))) ∨ True) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_49243624716361034087747972325 : ((((p5 ∨ p3) → (p1 → ((p1 ∧ (p4 ∧ (((False ∧ (((False ∧ p2) → p5) ∨ False)) → p5) ∧ p5))) ∧ p5))) ∨ (p1 ∧ (p3 ∨ p2))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_154819836667591415441363413234 : ((((True ∨ (p1 ∨ ((p5 → True) → p1))) → ((p3 → p5) ∧ ((p1 ∨ False) ∧ False))) → (p3 ∧ p2)) ∧ (p2 → (((p1 → p1) → p5) → True))) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h2 : (True ∨ (p1 ∨ ((p5 → True) → p1))) := by
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h3 := h1 h2
  -- We need to get the right conjuct of h3 based on <expert-advice>.
  let h4 := h3.right
  -- We need to get the right conjuct of h4 based on <expert-advice>.
  let h5 := h4.right
  -- False on the left can always be used.
  apply False.elim h5
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h6 : (True ∨ (p1 ∨ ((p5 → True) → p1))) := by
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h7 := h1 h6
  -- We need to get the right conjuct of h7 based on <expert-advice>.
  let h8 := h7.right
  -- We need to get the right conjuct of h8 based on <expert-advice>.
  let h9 := h8.right
  -- False on the left can always be used.
  apply False.elim h9
  -- Implications on the right can always be decomposed.
  intro h10
  -- Implications on the right can always be decomposed.
  intro h11
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_39655236649791887326968876572 : (((p3 ∨ ((p3 → p2) ∨ (((False ∨ False) ∧ ((p3 → True) ∧ (p4 ∨ p2))) ∨ (((True ∨ ((False → p2) → True)) → p1) ∨ p1)))) ∧ p5) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_184251713639148607439606502907 : ((((p4 ∨ (((p4 → True) → p1) ∨ (False ∧ p2))) → p4) → p2) ∨ (((False ∧ p1) → ((True → p3) ∧ (p1 → ((p2 ∧ p3) ∨ p2)))) ∨ p1)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h2
  -- Conjunctions on the left can always be decomposed.
  let h3 := h1.left
  let h4 := h1.right
  -- False on the left can always be used.
  apply False.elim h3
  -- Implications on the right can always be decomposed.
  intro h5
  -- Conjunctions on the left can always be decomposed.
  let h6 := h1.left
  let h7 := h1.right
  -- False on the left can always be used.
  apply False.elim h6



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_149947636156841510752277966254 : ((p3 ∨ (p5 ∨ (p5 → (p3 ∨ ((False ∧ p4) ∧ (True → (True ∨ ((p3 → (p4 ∧ (p1 ∨ p1))) → True)))))))) ∨ ((True ∨ (p2 ∧ p1)) ∨ p3)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_197002664675944057064845418169 : (((((p4 ∧ p5) ∨ p3) ∧ (False ∧ False)) ∨ True) ∨ ((((p4 → (p4 ∨ p1)) ∨ (True ∧ True)) ∨ p1) → ((((p1 ∨ p4) → p5) ∨ p2) ∧ True))) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_57777571382960366293106917615 : (((True ∧ (p1 → p4)) → ((p3 → p3) → (p5 ∨ ((True → p1) ∨ (True ∧ (p5 ∨ (p2 ∨ ((True → p3) → (True → (False → p4)))))))))) ∨ False) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Conjunctions on the left can always be decomposed.
  let h3 := h1.left
  let h4 := h1.right
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
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h5
  -- Implications on the right can always be decomposed.
  intro h6
  -- Implications on the right can always be decomposed.
  intro h7
  -- False on the left can always be used.
  apply False.elim h7



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_38040006690953643492227792926 : (((((True ∨ ((p5 → (p2 → (p1 ∨ ((p3 ∨ (p3 ∧ p1)) → ((p1 → p4) ∧ False))))) → (p5 → p2))) ∨ False) → (p1 ∧ p4)) ∧ p1) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_321733681566932301193378168072 : (p4 ∨ (p5 → ((p3 ∧ (((True → (((p3 ∨ p1) ∧ ((p5 → True) ∧ p2)) ∨ p4)) ∨ ((p1 ∧ p5) ∨ p1)) ∨ p1)) ∨ (p1 → (p4 ∨ True))))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h2
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_159610296950154354301598502301 : (((((p5 ∧ (((p5 ∧ (p2 → p1)) → p4) → (False ∧ False))) ∧ ((True ∨ p1) → p1)) ∧ p4) ∨ False) → (p1 → (True → ((p4 → False) ∧ False)))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Implications on the right can always be decomposed.
  intro h3
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h4
  -- Disjunctions on the left can always be decomposed.
  cases h1
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
    -- We want to use the implication h11 based on <expert-advice>. So we show its premise.
    have h12 : ((p5 ∧ (p2 → p1)) → p4) := by
      -- Implications on the right can always be decomposed.
      intro h13
      -- Conjunctions on the left can always be decomposed.
      let h14 := h13.left
      let h15 := h13.right
      -- One of the premise coincides with the conclusion.
      exact h7
    -- We have shown the premise of h11, we can now drive its conclusion.
    let h16 := h11 h12
    -- We need to get the left conjuct of h16 based on <expert-advice>.
    let h17 := h16.left
    -- False on the left can always be used.
    apply False.elim h17
  case inr h18 =>
    -- False on the left can always be used.
    apply False.elim h18
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h19 =>
    -- Conjunctions on the left can always be decomposed.
    let h20 := h19.left
    let h21 := h19.right
    -- Conjunctions on the left can always be decomposed.
    let h22 := h20.left
    let h23 := h20.right
    -- Conjunctions on the left can always be decomposed.
    let h24 := h22.left
    let h25 := h22.right
    -- We want to use the implication h25 based on <expert-advice>. So we show its premise.
    have h26 : ((p5 ∧ (p2 → p1)) → p4) := by
      -- Implications on the right can always be decomposed.
      intro h27
      -- Conjunctions on the left can always be decomposed.
      let h28 := h27.left
      let h29 := h27.right
      -- One of the premise coincides with the conclusion.
      exact h21
    -- We have shown the premise of h25, we can now drive its conclusion.
    let h30 := h25 h26
    -- We need to get the left conjuct of h30 based on <expert-advice>.
    let h31 := h30.left
    -- False on the left can always be used.
    apply False.elim h31
  case inr h32 =>
    -- False on the left can always be used.
    apply False.elim h32



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_676779410508039063761203163300 : ((((p1 ∨ ((p5 ∨ (p2 ∧ ((False ∨ True) → (True → (((p5 → False) → p3) → (False ∧ p3)))))) → p5)) ∧ (((False → p2) ∧ p3) → True)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_171790192568721470168216454108 : (((((False ∨ ((p2 ∧ (p4 ∨ p2)) ∨ (p3 ∧ p3))) → p3) → (p2 → True)) → p5) ∨ ((p4 ∨ (True → (p1 ∨ True))) ∨ (p3 → (True ∧ p4)))) := by
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
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_198731738744781402988121493847 : ((p5 ∨ (p3 ∨ ((p4 → (p4 ∧ p5)) ∧ p4))) ∨ (p4 → (((p2 ∨ True) ∨ (((((False → p1) → p5) → p3) → p3) ∨ (p3 ∧ False))) ∨ p3))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_184609982144161256153669632906 : ((((((False ∧ p1) → p1) ∨ True) → p2) ∧ ((p5 ∧ p5) → False)) ∨ (((p2 ∨ (False ∧ p1)) → p5) → (False ∨ (p4 ∨ (True → (False → p2)))))) := by
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
  -- Implications on the right can always be decomposed.
  intro h3
  -- False on the left can always be used.
  apply False.elim h3



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_680509492497077468546027443198 : (((((((True → False) ∨ p2) → ((p4 → (True → True)) ∨ p4)) ∨ ((((True ∨ False) ∨ p2) ∧ p1) ∨ False)) → (p2 ∨ (p3 ∧ (p1 → p4)))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_666459419488599062103164119425 : (((((False → ((p1 ∧ p3) → (p2 ∧ ((p4 → (p3 → False)) ∨ ((p2 → p4) → p3))))) → ((p4 ∨ p5) → p1)) ∧ ((p4 ∧ p2) ∨ p5)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_51113285141908943602013310214 : (((((((p5 ∨ (p3 ∨ (p3 ∧ p4))) ∨ True) ∧ ((p2 ∧ (p5 → True)) ∧ p2)) ∨ True) ∨ p3) ∨ (((p1 ∨ True) ∨ p5) ∧ (p1 ∨ p2))) ∨ p2) := by
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



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_345318410996955873710948734803 : (p3 → ((((p2 ∨ ((p2 ∨ ((p3 ∨ p3) ∧ ((False ∨ ((p4 ∧ (False → p2)) ∨ p3)) ∧ p4))) → ((p3 ∨ True) → p5))) ∨ True) ∧ p5) ∨ True)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_323846546890773880675164796928 : (p5 ∨ ((p3 ∨ (((True ∧ (True ∧ ((False ∧ p1) → p5))) ∨ (p3 → p1)) ∧ (p4 ∨ (p1 → p5)))) → ((((p2 → p4) ∧ True) ∧ True) ∨ True))) := by
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
    -- Conjunctions on the left can always be decomposed.
    let h4 := h3.left
    let h5 := h3.right
    -- Disjunctions on the left can always be decomposed.
    cases h4
    case inl h6 =>
      -- Conjunctions on the left can always be decomposed.
      let h7 := h6.left
      let h8 := h6.right
      -- Conjunctions on the left can always be decomposed.
      let h9 := h8.left
      let h10 := h8.right
      -- Disjunctions on the left can always be decomposed.
      cases h5
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
      -- Disjunctions on the left can always be decomposed.
      cases h5
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
theorem thm_5_vars_318791810048107552546367613258 : (p4 ∨ (((((False ∧ p3) ∨ (((((p2 ∧ True) ∨ p5) ∨ (True ∨ p2)) → (p3 ∨ p5)) → (True ∨ p1))) → False) → p2) ∧ ((True → p2) ∨ True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h1
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h2 : ((False ∧ p3) ∨ (((((p2 ∧ True) ∨ p5) ∨ (True ∨ p2)) → (p3 ∨ p5)) → (True ∨ p1))) := by
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h3
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h4 := h1 h2
  -- False on the left can always be used.
  apply False.elim h4
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_147207056781778377437611741138 : (((p1 → ((p4 ∨ ((p4 ∧ (True ∨ (p1 ∨ p2))) ∧ (p1 ∨ (p3 ∧ (True → p4))))) ∧ (p4 → True))) ∧ p1) ∨ (p1 ∨ ((p2 → p2) ∨ p3))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- One of the premise coincides with the conclusion.
  exact h1



