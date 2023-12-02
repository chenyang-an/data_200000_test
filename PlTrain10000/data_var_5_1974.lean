variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_806169347729679090329178471374 : (((p4 → (((((((p3 → (p3 ∧ (((p2 ∧ p5) ∧ True) ∧ ((p1 → True) → (p5 → p5))))) → p4) → p1) → True) → p2) ∨ p1) ∨ p4)) ∨ p2) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_39520449484000063845045556070 : (((False ∨ ((p1 ∨ (p5 → (((p3 → (False ∧ ((p3 ∧ p3) ∧ (((p1 ∧ False) → p1) → p3)))) ∧ p2) ∨ (p4 ∧ p5)))) → False)) ∧ p3) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_765793709702251461629827451694 : (((p4 ∧ ((p1 ∨ (p3 → ((p5 ∨ p3) → (False ∨ p4)))) ∨ (((p2 ∨ (p2 ∨ ((p5 ∨ (p5 ∨ False)) → (p4 → False)))) ∧ p1) → p3))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_56456162913801713389883075811 : ((((p3 → p1) ∨ (p5 ∨ p1)) → ((((False ∨ True) ∨ (False ∨ (True → p3))) ∨ False) → ((p1 ∧ (False ∧ ((p5 ∨ p1) → p3))) ∨ True))) ∨ p3) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
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
      -- Disjunctions on the left can always be decomposed.
      cases h4
      case inl h5 =>
        -- False on the left can always be used.
        apply False.elim h5
      case inr h6 =>
        -- Disjunctions on the left can always be decomposed.
        cases h1
        case inl h7 =>
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- True on the right can always be proven directly.
          apply True.intro
        case inr h8 =>
          -- Disjunctions on the left can always be decomposed.
          cases h8
          case inl h9 =>
            -- Show the right disjunct based on <expert-advice>.
            apply Or.inr
            -- True on the right can always be proven directly.
            apply True.intro
          case inr h10 =>
            -- Show the right disjunct based on <expert-advice>.
            apply Or.inr
            -- True on the right can always be proven directly.
            apply True.intro
    case inr h11 =>
      -- Disjunctions on the left can always be decomposed.
      cases h11
      case inl h12 =>
        -- False on the left can always be used.
        apply False.elim h12
      case inr h13 =>
        -- Disjunctions on the left can always be decomposed.
        cases h1
        case inl h14 =>
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
  case inr h18 =>
    -- False on the left can always be used.
    apply False.elim h18



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_810749891028883779342468021671 : (((p5 → ((True → (p4 → p1)) → ((p2 ∨ (True ∧ (((p4 → p1) → (p2 ∨ ((True → (False → (p2 ∨ p5))) ∧ False))) ∨ p5))) ∨ True))) ∨ p1) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_314839444271128817628506655805 : (p3 ∨ (((True ∧ False) ∧ ((p2 ∧ True) → (((p3 → True) → p4) ∧ p1))) ∨ ((p2 → ((True ∧ (p3 ∨ ((False ∧ p1) ∧ p3))) ∨ p2)) ∨ p4))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_120187436333474417221034933296 : ((((p4 ∨ p1) ∨ ((True ∨ ((p2 → (p2 ∧ (p4 ∨ p3))) ∨ (p5 → ((True → False) ∧ (p3 → (p4 ∧ p3)))))) ∨ p3)) ∧ p2) → (p1 ∨ True)) := by
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
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- True on the right can always be proven directly.
      apply True.intro
    case inr h6 =>
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- One of the premise coincides with the conclusion.
      exact h6
  case inr h7 =>
    -- Disjunctions on the left can always be decomposed.
    cases h7
    case inl h8 =>
      -- Disjunctions on the left can always be decomposed.
      cases h8
      case inl h9 =>
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



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_230011496666268099991705669938 : (((p1 ∧ True) ∧ p2) → (((((p2 ∨ p4) → p1) ∧ (p1 → p2)) → (((p3 ∨ (True ∨ False)) ∨ (p5 ∧ p5)) → (p4 ∧ (False ∨ True)))) ∨ p2)) := by
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
  exact h3



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_40713387255952506256595132482 : (((((p2 ∨ ((p4 ∨ (False ∧ ((p4 ∨ p4) ∧ p2))) ∨ p4)) → (p1 ∨ (p2 → ((False ∧ p1) ∧ (p1 → (p3 ∨ p1)))))) → p3) ∨ False) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_753921873801975883353540969351 : (((False ∧ (((p2 ∧ ((True ∨ False) → p1)) ∨ p2) ∧ ((p5 → (((True ∧ p3) → (p3 ∨ p4)) ∧ p2)) → (((p2 ∧ False) ∨ p3) ∨ p2)))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_319087347298461766237749790882 : (p4 ∨ (((True ∧ (((True ∨ ((p5 ∧ (p1 ∧ p4)) ∨ p4)) ∧ p4) ∧ (p5 ∨ True))) ∧ ((p3 ∨ True) ∧ p1)) → ((p5 ∨ (True ∨ p2)) ∧ p4))) := by
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
  -- Conjunctions on the left can always be decomposed.
  let h8 := h6.left
  let h9 := h6.right
  -- Disjunctions on the left can always be decomposed.
  cases h8
  case inl h10 =>
    -- Disjunctions on the left can always be decomposed.
    cases h7
    case inl h11 =>
      -- Conjunctions on the left can always be decomposed.
      let h12 := h3.left
      let h13 := h3.right
      -- Disjunctions on the left can always be decomposed.
      cases h12
      case inl h14 =>
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- One of the premise coincides with the conclusion.
        exact h11
      case inr h15 =>
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- One of the premise coincides with the conclusion.
        exact h11
    case inr h16 =>
      -- Conjunctions on the left can always be decomposed.
      let h17 := h3.left
      let h18 := h3.right
      -- Disjunctions on the left can always be decomposed.
      cases h17
      case inl h19 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- True on the right can always be proven directly.
        apply True.intro
      case inr h20 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- True on the right can always be proven directly.
        apply True.intro
  case inr h21 =>
    -- Disjunctions on the left can always be decomposed.
    cases h21
    case inl h22 =>
      -- Conjunctions on the left can always be decomposed.
      let h23 := h22.left
      let h24 := h22.right
      -- Conjunctions on the left can always be decomposed.
      let h25 := h24.left
      let h26 := h24.right
      -- Disjunctions on the left can always be decomposed.
      cases h7
      case inl h27 =>
        -- Conjunctions on the left can always be decomposed.
        let h28 := h3.left
        let h29 := h3.right
        -- Disjunctions on the left can always be decomposed.
        cases h28
        case inl h30 =>
          -- Show the left disjunct based on <expert-advice>.
          apply Or.inl
          -- One of the premise coincides with the conclusion.
          exact h27
        case inr h31 =>
          -- Show the left disjunct based on <expert-advice>.
          apply Or.inl
          -- One of the premise coincides with the conclusion.
          exact h27
      case inr h32 =>
        -- Conjunctions on the left can always be decomposed.
        let h33 := h3.left
        let h34 := h3.right
        -- Disjunctions on the left can always be decomposed.
        cases h33
        case inl h35 =>
          -- Show the left disjunct based on <expert-advice>.
          apply Or.inl
          -- One of the premise coincides with the conclusion.
          exact h23
        case inr h36 =>
          -- Show the left disjunct based on <expert-advice>.
          apply Or.inl
          -- One of the premise coincides with the conclusion.
          exact h23
    case inr h37 =>
      -- Disjunctions on the left can always be decomposed.
      cases h7
      case inl h38 =>
        -- Conjunctions on the left can always be decomposed.
        let h39 := h3.left
        let h40 := h3.right
        -- Disjunctions on the left can always be decomposed.
        cases h39
        case inl h41 =>
          -- Show the left disjunct based on <expert-advice>.
          apply Or.inl
          -- One of the premise coincides with the conclusion.
          exact h38
        case inr h42 =>
          -- Show the left disjunct based on <expert-advice>.
          apply Or.inl
          -- One of the premise coincides with the conclusion.
          exact h38
      case inr h43 =>
        -- Conjunctions on the left can always be decomposed.
        let h44 := h3.left
        let h45 := h3.right
        -- Disjunctions on the left can always be decomposed.
        cases h44
        case inl h46 =>
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- Show the left disjunct based on <expert-advice>.
          apply Or.inl
          -- True on the right can always be proven directly.
          apply True.intro
        case inr h47 =>
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- Show the left disjunct based on <expert-advice>.
          apply Or.inl
          -- True on the right can always be proven directly.
          apply True.intro
  -- Conjunctions on the left can always be decomposed.
  let h48 := h1.left
  let h49 := h1.right
  -- Conjunctions on the left can always be decomposed.
  let h50 := h48.left
  let h51 := h48.right
  -- Conjunctions on the left can always be decomposed.
  let h52 := h51.left
  let h53 := h51.right
  -- Conjunctions on the left can always be decomposed.
  let h54 := h52.left
  let h55 := h52.right
  -- Disjunctions on the left can always be decomposed.
  cases h54
  case inl h56 =>
    -- Disjunctions on the left can always be decomposed.
    cases h53
    case inl h57 =>
      -- Conjunctions on the left can always be decomposed.
      let h58 := h49.left
      let h59 := h49.right
      -- Disjunctions on the left can always be decomposed.
      cases h58
      case inl h60 =>
        -- One of the premise coincides with the conclusion.
        exact h55
      case inr h61 =>
        -- One of the premise coincides with the conclusion.
        exact h55
    case inr h62 =>
      -- Conjunctions on the left can always be decomposed.
      let h63 := h49.left
      let h64 := h49.right
      -- Disjunctions on the left can always be decomposed.
      cases h63
      case inl h65 =>
        -- One of the premise coincides with the conclusion.
        exact h55
      case inr h66 =>
        -- One of the premise coincides with the conclusion.
        exact h55
  case inr h67 =>
    -- Disjunctions on the left can always be decomposed.
    cases h67
    case inl h68 =>
      -- Conjunctions on the left can always be decomposed.
      let h69 := h68.left
      let h70 := h68.right
      -- Conjunctions on the left can always be decomposed.
      let h71 := h70.left
      let h72 := h70.right
      -- Disjunctions on the left can always be decomposed.
      cases h53
      case inl h73 =>
        -- Conjunctions on the left can always be decomposed.
        let h74 := h49.left
        let h75 := h49.right
        -- Disjunctions on the left can always be decomposed.
        cases h74
        case inl h76 =>
          -- One of the premise coincides with the conclusion.
          exact h55
        case inr h77 =>
          -- One of the premise coincides with the conclusion.
          exact h55
      case inr h78 =>
        -- Conjunctions on the left can always be decomposed.
        let h79 := h49.left
        let h80 := h49.right
        -- Disjunctions on the left can always be decomposed.
        cases h79
        case inl h81 =>
          -- One of the premise coincides with the conclusion.
          exact h55
        case inr h82 =>
          -- One of the premise coincides with the conclusion.
          exact h55
    case inr h83 =>
      -- Disjunctions on the left can always be decomposed.
      cases h53
      case inl h84 =>
        -- Conjunctions on the left can always be decomposed.
        let h85 := h49.left
        let h86 := h49.right
        -- Disjunctions on the left can always be decomposed.
        cases h85
        case inl h87 =>
          -- One of the premise coincides with the conclusion.
          exact h55
        case inr h88 =>
          -- One of the premise coincides with the conclusion.
          exact h55
      case inr h89 =>
        -- Conjunctions on the left can always be decomposed.
        let h90 := h49.left
        let h91 := h49.right
        -- Disjunctions on the left can always be decomposed.
        cases h90
        case inl h92 =>
          -- One of the premise coincides with the conclusion.
          exact h55
        case inr h93 =>
          -- One of the premise coincides with the conclusion.
          exact h55



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_112470969429924349014924904359 : (((((((p5 ∨ p3) ∨ p4) ∨ p2) → (p5 → ((True ∨ (((p1 ∧ p2) → True) ∧ ((p3 → False) → p3))) ∧ p1))) ∨ p5) → False) ∨ (p2 → True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_194777462705984167420106250369 : (((p4 ∨ (p1 → ((False ∧ p2) ∨ True))) ∨ p1) ∧ ((p5 ∧ (True → (p2 ∧ True))) → ((False ∧ ((p2 ∨ p4) → (p4 → True))) ∨ (True → p2)))) := by
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
  -- Implications on the right can always be decomposed.
  intro h2
  -- Conjunctions on the left can always be decomposed.
  let h3 := h2.left
  let h4 := h2.right
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h5
  -- We want to use the implication h4 based on <expert-advice>. So we show its premise.
  have h6 : True := by
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h4, we can now drive its conclusion.
  let h7 := h4 h6
  -- We need to get the left conjuct of h7 based on <expert-advice>.
  let h8 := h7.left
  -- One of the premise coincides with the conclusion.
  exact h8



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_224717918252124279467941349356 : ((p3 → (p3 → True)) ∧ (((True ∧ ((p2 ∧ (p4 ∨ (p1 ∧ (p4 ∧ (p4 ∧ ((p2 ∨ False) → False)))))) ∨ p4)) ∨ True) ∨ (p1 → (p5 → False)))) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- True on the right can always be proven directly.
  apply True.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_135790013338830187390040033977 : (((((p2 ∧ (p5 ∨ p4)) → False) ∨ (((True → (p1 → False)) ∨ p4) → p1)) → (((p3 ∧ (p2 → False)) ∧ p3) ∧ p4)) ∨ ((True → False) → True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_40025877649162172149758308079 : ((((((False ∧ (((True ∧ ((p3 ∧ (True ∧ p2)) ∨ False)) → p4) ∧ (False ∧ (((p4 ∧ p2) ∧ p1) ∧ True)))) ∨ False) ∧ p2) ∧ p3) ∨ p4) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_720006240816889927687805442242 : ((((((True ∧ False) ∨ p5) ∧ True) → ((p4 ∧ True) ∧ (((p3 ∧ p1) → (True ∨ ((True → p4) → (((p5 ∧ p1) ∨ p3) ∧ True)))) → False))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_133856583462609812488745298014 : (((p1 ∧ ((p3 ∧ ((((p4 → ((p1 → (p5 → True)) → p3)) ∧ True) ∨ (p3 ∨ p1)) ∨ True)) ∨ (True ∧ True))) ∧ p3) ∨ ((False → p2) ∨ False)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_619852133587393204561394655751 : (((((p4 ∨ False) ∧ ((p4 → (p5 ∧ (((p1 → (p3 ∨ (False ∧ (p4 ∨ p3)))) → (p3 ∨ (p5 → (p2 ∧ p5)))) ∧ p2))) ∨ p3)) ∨ True) ∨ p1) ∧ True) := by
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
theorem thm_5_vars_614521221073739706135279494939 : (((((((p4 ∨ False) ∧ ((p4 → ((p1 ∨ (False ∧ True)) ∧ p3)) → p2)) ∧ (True → (True → p2))) ∧ (((p3 ∨ True) → p3) ∧ False)) ∨ p2) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_49482446656203540071841782768 : ((((((False ∨ (False → p1)) ∧ (p1 ∨ ((False ∨ (False → p4)) ∧ (p1 ∧ p4)))) ∧ (True ∨ (p1 ∨ p1))) → p2) → ((p3 ∨ p5) → p4)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_180644272766548699010890970026 : ((((True → (p4 ∨ p2)) ∨ (False → False)) ∨ ((p4 ∨ (p4 ∨ p4)) → p5)) → (((p3 ∧ (p1 → p4)) ∨ p5) ∨ (False ∨ (False → (p2 ∨ p1))))) := by
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
      -- False on the left can always be used.
      apply False.elim h6
  case inr h7 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h8
    -- False on the left can always be used.
    apply False.elim h8



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_776494057366926959239671879002 : (((p1 ∨ ((((True → p3) ∧ ((p2 ∨ (p2 ∨ (p1 → p4))) ∨ (p5 ∨ (p2 → (False → p2))))) ∧ (((p1 → p2) ∧ False) ∧ p1)) ∨ True)) ∨ p2) ∧ True) := by
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
theorem thm_5_vars_56959549685025766110130637503 : (((p2 ∨ (p4 ∨ False)) ∧ (((p1 ∧ (((p1 ∨ (p3 → p1)) → (p3 ∨ (p2 → True))) ∧ (False → ((p1 ∨ p5) ∨ False)))) ∨ p4) ∨ p5)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_183017595430339762217084411578 : (((p3 ∧ False) ∨ ((False → False) ∨ ((False → (False ∨ False)) → True))) ∧ ((p4 ∨ (((p4 ∧ ((True → (p4 ∧ p1)) ∨ p3)) → p5) → p3)) ∨ True)) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_178835209867849172047103988600 : ((((p4 → p4) ∧ p4) → (False ∧ (((p1 → p2) ∨ False) → (p1 ∧ False)))) ∨ (True ∧ ((((p5 ∧ p5) → (p2 ∨ p3)) ∧ False) → (p1 ∨ p4)))) := by
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
  -- False on the left can always be used.
  apply False.elim h3



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_586205066522957942501756600033 : (((((((p4 ∨ p2) ∧ (((p5 ∧ False) ∨ (p2 → (p1 ∨ False))) ∨ p5)) ∨ ((((p3 ∧ p2) → (p1 → True)) → p4) → False)) ∧ False) ∧ p4) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_157966217876068978618341161748 : ((((p5 ∨ (True → p5)) → (p3 ∨ (p5 ∧ p3))) ∨ (((p3 → True) ∨ (p2 ∨ p5)) → (p2 ∧ True))) ∨ (((p2 → p5) → True) ∨ (False ∨ True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_157249109691451442532989003694 : ((((((p1 ∨ (False → p3)) → p5) ∨ True) ∨ (p4 ∧ (True ∧ ((p4 ∨ (p2 ∨ False)) → p1)))) → p3) ∨ (p1 → (True → (p5 ∨ (False ∨ True))))) := by
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
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_178406194379492234317359616027 : ((((p3 ∧ p5) → (p5 → (p3 ∨ ((p1 ∧ p1) ∧ p5)))) → (p4 ∨ p1)) ∨ (((False ∧ (p2 ∧ (p4 ∧ ((True ∧ True) → p2)))) → p5) → True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_780904172751084239486587036533 : (((p2 ∨ ((p5 ∨ (p5 → p5)) ∧ (((True ∨ (p2 → p3)) → (p5 ∧ ((((False ∧ p4) ∨ (True → (False ∨ p3))) ∧ p5) ∨ p1))) ∨ p5))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_311239466658717793516518192106 : (p2 ∨ ((p4 → False) → ((((p3 → (False ∧ ((((p4 ∨ (p2 ∨ False)) ∨ (p2 ∧ (p2 → p3))) ∨ False) → p1))) → (p5 ∧ True)) ∨ True) ∨ True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_41665042361575197775892781606 : (((((((p1 ∧ p2) ∧ p1) ∨ True) ∧ p2) ∨ ((p2 ∨ ((False ∧ ((False → True) → p4)) ∨ p1)) ∨ (((p4 → p3) ∧ p4) ∨ p3))) ∨ True) ∨ p2) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_932325126866270914945006506339 : ((((((p4 → p1) ∧ (True → True)) → (p4 ∧ True)) ∧ (((p3 → ((p1 → True) ∨ p1)) → False) ∧ (((True → (p2 ∧ False)) ∧ p4) → True))) → p1) ∧ True) := by
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
  -- We want to use the implication h4 based on <expert-advice>. So we show its premise.
  have h6 : (p3 → ((p1 → True) ∨ p1)) := by
    -- Implications on the right can always be decomposed.
    intro h7
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Implications on the right can always be decomposed.
    intro h8
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h4, we can now drive its conclusion.
  let h9 := h4 h6
  -- False on the left can always be used.
  apply False.elim h9
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_259645567677141561845321628815 : ((p1 → False) → ((p1 ∧ (p5 ∨ p4)) → (((p5 ∨ p3) → (p5 → ((p3 ∨ p5) ∨ p1))) ∧ (False ∨ (True → ((False → p4) → (False ∨ p4))))))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h3
  -- Implications on the right can always be decomposed.
  intro h4
  -- Disjunctions on the left can always be decomposed.
  cases h3
  case inl h5 =>
    -- Conjunctions on the left can always be decomposed.
    let h6 := h2.left
    let h7 := h2.right
    -- Disjunctions on the left can always be decomposed.
    cases h7
    case inl h8 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- One of the premise coincides with the conclusion.
      exact h6
    case inr h9 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- One of the premise coincides with the conclusion.
      exact h6
  case inr h10 =>
    -- Conjunctions on the left can always be decomposed.
    let h11 := h2.left
    let h12 := h2.right
    -- Disjunctions on the left can always be decomposed.
    cases h12
    case inl h13 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- One of the premise coincides with the conclusion.
      exact h11
    case inr h14 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- One of the premise coincides with the conclusion.
      exact h11
  -- Conjunctions on the left can always be decomposed.
  let h15 := h2.left
  let h16 := h2.right
  -- Disjunctions on the left can always be decomposed.
  cases h16
  case inl h17 =>
    -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
    have h18 : p1 := by
      -- One of the premise coincides with the conclusion.
      exact h15
    -- We have shown the premise of h1, we can now drive its conclusion.
    let h19 := h1 h18
    -- False on the left can always be used.
    apply False.elim h19
  case inr h20 =>
    -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
    have h21 : p1 := by
      -- One of the premise coincides with the conclusion.
      exact h15
    -- We have shown the premise of h1, we can now drive its conclusion.
    let h22 := h1 h21
    -- False on the left can always be used.
    apply False.elim h22



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_213116526513821235987030235733 : ((((p5 ∨ p1) ∧ False) ∧ True) ∨ (((p1 ∧ False) ∨ (p5 ∨ ((p1 ∧ (p3 ∧ (p2 ∨ p5))) ∨ p1))) → (((p4 → p4) ∧ True) → (p2 ∨ True)))) := by
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
  cases h1
  case inl h5 =>
    -- Conjunctions on the left can always be decomposed.
    let h6 := h5.left
    let h7 := h5.right
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
      -- Disjunctions on the left can always be decomposed.
      cases h10
      case inl h11 =>
        -- Conjunctions on the left can always be decomposed.
        let h12 := h11.left
        let h13 := h11.right
        -- Conjunctions on the left can always be decomposed.
        let h14 := h13.left
        let h15 := h13.right
        -- Disjunctions on the left can always be decomposed.
        cases h15
        case inl h16 =>
          -- Show the left disjunct based on <expert-advice>.
          apply Or.inl
          -- One of the premise coincides with the conclusion.
          exact h16
        case inr h17 =>
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- True on the right can always be proven directly.
          apply True.intro
      case inr h18 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- True on the right can always be proven directly.
        apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_647010472186091083210271429410 : ((((p3 → ((((p2 ∨ (False → ((p2 ∧ ((True ∨ (False → p1)) ∧ (p5 ∧ p2))) ∧ True))) → p5) ∨ (p2 ∨ (p3 ∨ p2))) → p4)) → p1) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_99021339290839649162976491454 : ((True → (((False ∧ (p5 ∧ (p4 ∨ (p1 ∨ False)))) ∨ True) → (((p3 → (True ∨ ((p3 ∨ ((False → True) ∧ False)) ∨ p4))) ∨ False) → p4))) → p4) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h2 : True := by
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h3 := h1 h2
  -- We want to use the implication h3 based on <expert-advice>. So we show its premise.
  have h4 : ((False ∧ (p5 ∧ (p4 ∨ (p1 ∨ False)))) ∨ True) := by
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h3, we can now drive its conclusion.
  let h5 := h3 h4
  -- We want to use the implication h5 based on <expert-advice>. So we show its premise.
  have h6 : ((p3 → (True ∨ ((p3 ∨ ((False → True) ∧ False)) ∨ p4))) ∨ False) := by
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Implications on the right can always be decomposed.
    intro h7
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h5, we can now drive its conclusion.
  let h8 := h5 h6
  -- One of the premise coincides with the conclusion.
  exact h8



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_750782987044662420285371067637 : (((True ∧ (((p1 → p3) ∨ (((p1 → ((p3 ∨ True) ∧ False)) ∨ True) ∧ p4)) ∨ (p4 ∧ (p2 ∨ (p5 → (p3 ∨ (p3 ∨ (p2 → False)))))))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_190463323835304589484969602160 : ((((((p3 ∧ (p3 ∨ p1)) ∧ p3) ∨ p2) ∧ p3) → p4) ∨ ((p4 ∧ p2) ∨ (((p1 → (p4 ∧ (True ∧ (p4 ∧ (p1 → False))))) → p1) ∨ True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_40542925984056154911443035477 : ((((p4 ∨ (p4 ∨ (((p2 ∨ ((p5 ∧ (p2 ∨ p3)) ∨ ((True → (p5 → p1)) ∨ p4))) ∨ p1) ∨ (p1 ∨ (p5 → p5))))) ∨ p3) ∨ True) ∨ p2) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_41820343514086231265438033886 : (((((p5 ∨ True) ∨ False) ∧ ((((True ∧ (p2 → p2)) ∧ (p5 → True)) ∨ (p1 → (False → p2))) → (p3 ∧ ((p3 ∧ False) ∧ p2)))) ∨ p5) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_666511891482967343678892900831 : (((((((p1 → (p4 ∨ ((p3 ∧ True) → False))) ∨ (p1 ∧ True)) ∧ (p2 ∧ False)) ∨ (((True ∨ p4) ∨ p2) → p5)) ∧ ((True ∨ p5) → p3)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_117703913220280028965792649340 : ((p3 ∧ (p1 ∧ (((p1 ∧ (p5 ∨ (p3 → p4))) → (((p5 → (p5 → False)) ∨ ((p5 ∨ p1) ∧ p5)) ∧ (p4 ∨ True))) ∧ p2))) ∨ (p5 → p5)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_112364354046647683877813505428 : ((((((((((((p4 → p3) ∨ p1) → True) ∨ True) ∧ ((True ∧ p2) → (p1 ∧ False))) → False) ∨ True) ∨ p3) → p4) ∧ p1) → p2) ∨ (True ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_134925142890642235999467046565 : ((((((((True → False) → p4) ∧ (False → (True ∧ ((p2 ∨ False) → True)))) ∧ (p2 ∧ p5)) ∨ p5) → False) ∧ (p2 ∧ p2)) ∨ (False → (False ∧ p5))) := by
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
theorem thm_5_vars_202672176874407829034151133934 : (((p2 ∧ (False ∧ p4)) → (p3 → p1)) ∧ (p1 → (p2 ∨ ((((False ∨ (((p1 ∨ p5) → p3) → p5)) ∨ (True ∧ False)) ∨ p1) ∨ (True → p1))))) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Conjunctions on the left can always be decomposed.
  let h3 := h1.left
  let h4 := h1.right
  -- Conjunctions on the left can always be decomposed.
  let h5 := h4.left
  let h6 := h4.right
  -- False on the left can always be used.
  apply False.elim h5
  -- Implications on the right can always be decomposed.
  intro h7
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h7



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_112973824973472739030353914286 : (((p1 ∧ ((p4 → p2) ∨ ((((((p3 → False) → ((True → p4) ∧ p3)) ∧ ((True → True) ∧ True)) ∨ p5) ∧ p4) ∧ True))) → p5) ∨ (p5 → p5)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_258787277018674346707045100957 : ((True → False) → ((p1 ∧ ((False ∨ (p4 ∨ p3)) ∧ (p3 ∧ (p2 → p1)))) ∧ ((((p1 ∨ (False ∨ False)) ∨ True) ∨ False) ∧ (p4 ∧ (p3 → p3))))) := by
  -- Implications on the right can always be decomposed.
  intro h1
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
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h4 : True := by
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h5 := h1 h4
  -- False on the left can always be used.
  apply False.elim h5
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
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
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h9 : True := by
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h10 := h1 h9
  -- False on the left can always be used.
  apply False.elim h10
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h11 : True := by
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h12 := h1 h11
  -- False on the left can always be used.
  apply False.elim h12
  -- Implications on the right can always be decomposed.
  intro h13
  -- One of the premise coincides with the conclusion.
  exact h13



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_750241994651634660217755150795 : (((True ∧ ((((((((p4 ∨ (p5 → True)) → True) → True) ∨ (True ∧ p4)) ∨ (p3 ∨ ((False ∨ p1) ∧ True))) ∧ p2) → p4) ∨ (p2 → p5))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_155041960756941081272165963680 : (((((p5 ∨ p4) ∧ p3) ∨ (p4 ∧ ((p2 ∧ False) ∨ (p3 → p5)))) ∨ (p4 ∨ ((False → True) ∨ p2))) ∧ (((p2 ∨ (True ∧ p3)) ∨ p4) → True)) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro
  -- Implications on the right can always be decomposed.
  intro h2
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_147571176603622411344006289477 : (((((False ∨ (p4 ∨ ((p1 ∧ p5) ∧ p1))) ∨ (True ∧ (p4 ∨ ((p3 → (p2 ∧ p1)) → False)))) ∧ p4) → False) ∨ ((p1 → (p3 → p5)) → True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_157983309313581500996424655200 : (((((True ∧ (True → p1)) → (p4 ∧ p3)) ∨ p3) → (p2 ∧ (((p3 ∧ (p2 → p1)) → p3) → p5))) ∨ ((p5 → p5) ∨ (True ∨ (p1 ∨ p1)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_601093000739424538921091164572 : ((((p1 ∧ (p2 ∧ (p2 → ((p1 ∧ ((p2 → (p1 ∧ p5)) ∨ p5)) ∨ ((((False → p2) → (p5 ∨ p4)) ∨ p2) → (p2 ∧ p1)))))) ∧ p5) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_172683634039380807511448930979 : (((False ∧ p4) ∨ (((True → p3) ∨ (p3 → (p5 ∨ ((p4 ∧ False) ∨ p3)))) ∧ False)) ∨ (((((False ∧ (p5 ∧ p2)) ∧ False) ∨ False) → p2) ∧ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
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
    -- False on the left can always be used.
    apply False.elim h5
  case inr h7 =>
    -- False on the left can always be used.
    apply False.elim h7
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_257079532673288562412075455779 : ((p2 ∨ False) → ((p4 → (p2 → (p1 ∨ (p5 ∧ (p5 → ((((False → ((True → p1) ∨ p2)) ∨ p3) → True) → False)))))) ∨ ((p2 ∨ p2) ∧ True))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h2 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Conjunctions on the right can always be decomposed.
    apply And.intro
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- One of the premise coincides with the conclusion.
    exact h2
    -- True on the right can always be proven directly.
    apply True.intro
  case inr h3 =>
    -- False on the left can always be used.
    apply False.elim h3



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_651032846240951223773391568026 : (((((p5 → (p4 ∨ ((True ∧ True) ∨ p1))) → (p1 ∨ (((p5 ∨ (False → (p1 ∧ p1))) → p1) → ((p5 ∧ p1) ∧ p5)))) ∧ (p1 → p3)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_224435526165513714025811246914 : ((p1 → (p1 ∨ p4)) ∧ (False ∨ (p1 ∨ (((((p3 ∨ ((True ∨ p4) ∨ (((False ∨ p3) ∨ (p1 → p5)) ∧ p3))) ∧ p3) → p1) ∨ p3) ∨ True)))) := by
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
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_804329726992449012343047164728 : (((p3 → ((p2 ∨ (p1 ∨ ((p5 ∨ ((True ∧ p1) ∧ p1)) ∨ (p1 → p2)))) ∧ (True ∨ (((False → ((False → p2) → p5)) ∨ p5) ∨ p2)))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_172635374621916026634603996499 : (((p5 ∧ p3) ∧ ((((p4 ∨ p5) ∨ p1) ∨ p1) ∧ ((True ∧ p2) → (p4 ∧ True)))) ∨ ((p4 → (((True → p2) ∨ p3) → True)) ∧ (False → p5))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- True on the right can always be proven directly.
  apply True.intro
  -- Implications on the right can always be decomposed.
  intro h3
  -- False on the left can always be used.
  apply False.elim h3



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_105711158877009811208625550526 : (((((p1 ∨ p1) → ((False → p2) ∧ (((p2 → (p1 ∧ p2)) ∧ False) ∨ p1))) → p3) ∨ (p4 → ((False ∧ p5) → (p5 ∧ p1)))) ∧ (p5 ∨ True)) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Conjunctions on the left can always be decomposed.
  let h3 := h2.left
  let h4 := h2.right
  -- False on the left can always be used.
  apply False.elim h3
  -- Conjunctions on the left can always be decomposed.
  let h5 := h2.left
  let h6 := h2.right
  -- False on the left can always be used.
  apply False.elim h5
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_338169487653610346031985018396 : (p1 → (((p1 → False) ∧ ((p3 → True) → (p4 ∨ p1))) → (p2 ∨ (p4 ∧ (False ∧ (((False ∧ (p1 ∧ (p1 → (p2 ∨ False)))) → True) ∨ False)))))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Conjunctions on the left can always be decomposed.
  let h3 := h2.left
  let h4 := h2.right
  -- We want to use the implication h3 based on <expert-advice>. So we show its premise.
  have h5 : p1 := by
    -- One of the premise coincides with the conclusion.
    exact h1
  -- We have shown the premise of h3, we can now drive its conclusion.
  let h6 := h3 h5
  -- False on the left can always be used.
  apply False.elim h6



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_41936200571813064406715120277 : ((((p2 → (p4 → p3)) → (((p5 ∨ p4) → (((p1 ∨ ((p5 → False) ∧ p3)) ∧ p2) ∧ (p3 → ((p1 → p2) → p5)))) ∨ True)) ∨ p3) ∨ p2) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_65047554995940396402633776456 : ((p2 ∨ (False ∧ ((p4 ∨ p5) ∨ (((p3 → p3) → (((False → p4) → p5) → ((p2 ∨ (False ∨ (True → (p5 ∧ False)))) ∨ p5))) ∧ p5)))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_219829458199459971701459248635 : ((p3 → ((p2 ∨ p5) ∨ p4)) → ((((p1 → p1) → p1) ∧ ((p2 ∨ True) ∧ ((True ∧ ((p1 ∧ p1) → (p5 ∧ p5))) → p4))) → (p1 ∧ True))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Conjunctions on the left can always be decomposed.
  let h3 := h2.left
  let h4 := h2.right
  -- Conjunctions on the left can always be decomposed.
  let h5 := h4.left
  let h6 := h4.right
  -- Disjunctions on the left can always be decomposed.
  cases h5
  case inl h7 =>
    -- We want to use the implication h3 based on <expert-advice>. So we show its premise.
    have h8 : (p1 → p1) := by
      -- Implications on the right can always be decomposed.
      intro h9
      -- One of the premise coincides with the conclusion.
      exact h9
    -- We have shown the premise of h3, we can now drive its conclusion.
    let h10 := h3 h8
    -- One of the premise coincides with the conclusion.
    exact h10
  case inr h11 =>
    -- We want to use the implication h3 based on <expert-advice>. So we show its premise.
    have h12 : (p1 → p1) := by
      -- Implications on the right can always be decomposed.
      intro h13
      -- One of the premise coincides with the conclusion.
      exact h13
    -- We have shown the premise of h3, we can now drive its conclusion.
    let h14 := h3 h12
    -- One of the premise coincides with the conclusion.
    exact h14
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_309783195781092954524757393168 : (p2 ∨ (((((((p4 ∨ (p3 ∨ p5)) → p2) ∧ (p4 → False)) ∨ p1) ∨ ((p1 ∨ True) ∧ (p2 ∧ p5))) ∨ p3) ∨ (p1 → (True ∨ (False → p4))))) := by
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



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_166276952917467720117897832130 : ((p4 ∧ (((((True → p4) ∨ (False ∧ False)) → (True → (p3 ∨ False))) ∧ (p3 ∧ p4)) ∧ p2)) ∨ (((p5 ∨ True) → (p4 ∨ p3)) → (p4 → True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_763519808329918348296152217268 : (((p3 ∧ (p2 ∧ ((p3 → p3) ∧ (((((p1 ∨ True) ∨ (p5 → (p2 ∨ (p2 → (p5 ∨ ((p3 → p3) ∧ p2)))))) → p5) ∧ p5) ∧ p1)))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_731205564792185193765027098783 : ((((p3 ∨ (p2 ∧ p1)) → (((False ∧ ((p4 ∨ p1) ∨ ((p5 ∧ (p4 ∨ p3)) ∧ ((True ∨ p3) ∨ (False ∧ p5))))) ∧ False) ∧ (False ∨ p1))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_324715294839176856944180045672 : (p5 ∨ (((p2 ∨ p4) ∨ p5) → ((False ∨ ((((((((False → p5) ∧ p2) ∧ (p5 ∧ True)) ∨ p2) ∨ p5) → False) → p4) → p1)) → (p1 ∧ p1)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Disjunctions on the left can always be decomposed.
  cases h2
  case inl h3 =>
    -- False on the left can always be used.
    apply False.elim h3
  case inr h4 =>
    -- Disjunctions on the left can always be decomposed.
    cases h1
    case inl h5 =>
      -- Disjunctions on the left can always be decomposed.
      cases h5
      case inl h6 =>
        -- We want to use the implication h4 based on <expert-advice>. So we show its premise.
        have h7 : (((((((False → p5) ∧ p2) ∧ (p5 ∧ True)) ∨ p2) ∨ p5) → False) → p4) := by
          -- Implications on the right can always be decomposed.
          intro h8
          -- We want to use the implication h8 based on <expert-advice>. So we show its premise.
          have h9 : (((((False → p5) ∧ p2) ∧ (p5 ∧ True)) ∨ p2) ∨ p5) := by
            -- Show the left disjunct based on <expert-advice>.
            apply Or.inl
            -- Show the right disjunct based on <expert-advice>.
            apply Or.inr
            -- One of the premise coincides with the conclusion.
            exact h6
          -- We have shown the premise of h8, we can now drive its conclusion.
          let h10 := h8 h9
          -- False on the left can always be used.
          apply False.elim h10
        -- We have shown the premise of h4, we can now drive its conclusion.
        let h11 := h4 h7
        -- One of the premise coincides with the conclusion.
        exact h11
      case inr h12 =>
        -- We want to use the implication h4 based on <expert-advice>. So we show its premise.
        have h13 : (((((((False → p5) ∧ p2) ∧ (p5 ∧ True)) ∨ p2) ∨ p5) → False) → p4) := by
          -- Implications on the right can always be decomposed.
          intro h14
          -- One of the premise coincides with the conclusion.
          exact h12
        -- We have shown the premise of h4, we can now drive its conclusion.
        let h15 := h4 h13
        -- One of the premise coincides with the conclusion.
        exact h15
    case inr h16 =>
      -- We want to use the implication h4 based on <expert-advice>. So we show its premise.
      have h17 : (((((((False → p5) ∧ p2) ∧ (p5 ∧ True)) ∨ p2) ∨ p5) → False) → p4) := by
        -- Implications on the right can always be decomposed.
        intro h18
        -- We want to use the implication h18 based on <expert-advice>. So we show its premise.
        have h19 : (((((False → p5) ∧ p2) ∧ (p5 ∧ True)) ∨ p2) ∨ p5) := by
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- One of the premise coincides with the conclusion.
          exact h16
        -- We have shown the premise of h18, we can now drive its conclusion.
        let h20 := h18 h19
        -- False on the left can always be used.
        apply False.elim h20
      -- We have shown the premise of h4, we can now drive its conclusion.
      let h21 := h4 h17
      -- One of the premise coincides with the conclusion.
      exact h21
  -- Disjunctions on the left can always be decomposed.
  cases h2
  case inl h22 =>
    -- False on the left can always be used.
    apply False.elim h22
  case inr h23 =>
    -- Disjunctions on the left can always be decomposed.
    cases h1
    case inl h24 =>
      -- Disjunctions on the left can always be decomposed.
      cases h24
      case inl h25 =>
        -- We want to use the implication h23 based on <expert-advice>. So we show its premise.
        have h26 : (((((((False → p5) ∧ p2) ∧ (p5 ∧ True)) ∨ p2) ∨ p5) → False) → p4) := by
          -- Implications on the right can always be decomposed.
          intro h27
          -- We want to use the implication h27 based on <expert-advice>. So we show its premise.
          have h28 : (((((False → p5) ∧ p2) ∧ (p5 ∧ True)) ∨ p2) ∨ p5) := by
            -- Show the left disjunct based on <expert-advice>.
            apply Or.inl
            -- Show the right disjunct based on <expert-advice>.
            apply Or.inr
            -- One of the premise coincides with the conclusion.
            exact h25
          -- We have shown the premise of h27, we can now drive its conclusion.
          let h29 := h27 h28
          -- False on the left can always be used.
          apply False.elim h29
        -- We have shown the premise of h23, we can now drive its conclusion.
        let h30 := h23 h26
        -- One of the premise coincides with the conclusion.
        exact h30
      case inr h31 =>
        -- We want to use the implication h23 based on <expert-advice>. So we show its premise.
        have h32 : (((((((False → p5) ∧ p2) ∧ (p5 ∧ True)) ∨ p2) ∨ p5) → False) → p4) := by
          -- Implications on the right can always be decomposed.
          intro h33
          -- One of the premise coincides with the conclusion.
          exact h31
        -- We have shown the premise of h23, we can now drive its conclusion.
        let h34 := h23 h32
        -- One of the premise coincides with the conclusion.
        exact h34
    case inr h35 =>
      -- We want to use the implication h23 based on <expert-advice>. So we show its premise.
      have h36 : (((((((False → p5) ∧ p2) ∧ (p5 ∧ True)) ∨ p2) ∨ p5) → False) → p4) := by
        -- Implications on the right can always be decomposed.
        intro h37
        -- We want to use the implication h37 based on <expert-advice>. So we show its premise.
        have h38 : (((((False → p5) ∧ p2) ∧ (p5 ∧ True)) ∨ p2) ∨ p5) := by
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- One of the premise coincides with the conclusion.
          exact h35
        -- We have shown the premise of h37, we can now drive its conclusion.
        let h39 := h37 h38
        -- False on the left can always be used.
        apply False.elim h39
      -- We have shown the premise of h23, we can now drive its conclusion.
      let h40 := h23 h36
      -- One of the premise coincides with the conclusion.
      exact h40



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_197103194992458678081291792764 : (((p5 ∧ ((p3 → (False ∨ p3)) → p3)) ∨ p1) ∨ ((((p1 ∧ ((p3 ∨ (p3 → p1)) ∨ p3)) ∧ (False ∧ p4)) ∧ p3) ∨ ((p1 ∨ p3) ∨ True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_656326069863422469867862073141 : (((((True ∧ (((True ∧ (p5 → (p1 ∨ p3))) → (p1 ∨ p5)) ∧ False)) ∨ (True ∧ ((p2 ∧ (p2 ∧ (p1 → False))) → True))) ∨ (True → p1)) ∨ p2) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
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
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_173133092745110920999291094583 : ((p2 ∨ (p2 → ((p5 ∧ p1) → ((False ∨ p3) → ((p4 ∧ p4) ∨ (p3 → False)))))) ∨ ((((False → p1) ∧ (p4 → (p5 → p5))) → p5) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_731930648199149042191302688150 : ((((p5 → (p3 ∨ p3)) → (p2 ∨ ((((p3 ∨ (p3 → ((p1 → p3) ∧ p3))) ∧ (p1 ∧ p4)) ∨ p1) ∨ (p3 ∧ (p4 ∨ (p3 → p5)))))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_256151827570224872226541838066 : ((False ∨ True) → (((p2 ∨ (True ∧ ((p3 ∧ (((p4 → p5) ∨ p1) ∧ (((False → p1) → False) ∧ ((p1 → False) ∨ p3)))) → p2))) ∨ p2) ∨ p3)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h2 =>
    -- False on the left can always be used.
    apply False.elim h2
  case inr h3 =>
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Conjunctions on the right can always be decomposed.
    apply And.intro
    -- True on the right can always be proven directly.
    apply True.intro
    -- Implications on the right can always be decomposed.
    intro h4
    -- Conjunctions on the left can always be decomposed.
    let h5 := h4.left
    let h6 := h4.right
    -- Conjunctions on the left can always be decomposed.
    let h7 := h6.left
    let h8 := h6.right
    -- Disjunctions on the left can always be decomposed.
    cases h7
    case inl h9 =>
      -- Conjunctions on the left can always be decomposed.
      let h10 := h8.left
      let h11 := h8.right
      -- Disjunctions on the left can always be decomposed.
      cases h11
      case inl h12 =>
        -- We want to use the implication h10 based on <expert-advice>. So we show its premise.
        have h13 : (False → p1) := by
          -- Implications on the right can always be decomposed.
          intro h14
          -- False on the left can always be used.
          apply False.elim h14
        -- We have shown the premise of h10, we can now drive its conclusion.
        let h15 := h10 h13
        -- False on the left can always be used.
        apply False.elim h15
      case inr h16 =>
        -- We want to use the implication h10 based on <expert-advice>. So we show its premise.
        have h17 : (False → p1) := by
          -- Implications on the right can always be decomposed.
          intro h18
          -- False on the left can always be used.
          apply False.elim h18
        -- We have shown the premise of h10, we can now drive its conclusion.
        let h19 := h10 h17
        -- False on the left can always be used.
        apply False.elim h19
    case inr h20 =>
      -- Conjunctions on the left can always be decomposed.
      let h21 := h8.left
      let h22 := h8.right
      -- Disjunctions on the left can always be decomposed.
      cases h22
      case inl h23 =>
        -- We want to use the implication h23 based on <expert-advice>. So we show its premise.
        have h24 : p1 := by
          -- One of the premise coincides with the conclusion.
          exact h20
        -- We have shown the premise of h23, we can now drive its conclusion.
        let h25 := h23 h24
        -- False on the left can always be used.
        apply False.elim h25
      case inr h26 =>
        -- We want to use the implication h21 based on <expert-advice>. So we show its premise.
        have h27 : (False → p1) := by
          -- Implications on the right can always be decomposed.
          intro h28
          -- False on the left can always be used.
          apply False.elim h28
        -- We have shown the premise of h21, we can now drive its conclusion.
        let h29 := h21 h27
        -- False on the left can always be used.
        apply False.elim h29



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_254718816960860964852952431963 : ((p3 ∧ p3) → ((p1 ∧ ((p2 ∧ (p2 → p2)) ∨ (p1 → (p4 → p4)))) ∨ ((p4 ∧ ((p1 → True) ∨ p1)) ∨ ((p4 ∧ (p5 ∨ False)) ∨ True)))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_112674885536952142436450394395 : ((((((((p4 ∨ ((p3 → (True → p5)) ∧ p1)) ∧ p5) ∨ p1) ∧ (p1 ∧ True)) ∨ (p2 ∧ True)) → ((p1 ∨ True) ∨ p2)) → p4) ∨ (True ∨ p5)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_38768782584311916855543525764 : ((((p3 → ((p1 ∨ p2) ∧ p2)) ∧ (p2 ∨ (False ∧ ((True ∧ ((p5 ∨ True) ∧ (p1 → (((p5 → False) ∧ p4) ∧ True)))) → True)))) ∧ p1) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_116736179070927289332971077182 : (((p4 ∧ True) ∨ (((p5 → ((p3 → p3) → (True ∧ ((False ∧ p5) ∧ p2)))) → (p1 → p2)) ∧ (((p2 ∨ p2) ∧ p3) ∨ p4))) ∨ (True ∨ False)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_113541959090462101278105899362 : (((((p4 ∨ (True → True)) → True) → ((((p5 → (((False → (p3 ∨ True)) ∧ p2) → True)) → p2) → p4) → p1)) ∨ (p2 → p5)) ∨ (False → True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_652072083230665589707366999274 : ((((False ∧ ((p4 → False) ∨ (p3 ∧ ((((p4 → (p4 ∧ ((p4 ∨ p5) ∧ (p5 → (p5 ∧ p3))))) → False) ∧ p3) ∨ True)))) ∧ (p5 ∨ p5)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_183995312549015499655874372132 : ((((True ∨ ((((True ∨ False) ∧ True) → p1) → True)) ∧ p4) ∨ p2) ∨ ((True ∧ ((((p4 ∧ p1) ∨ p1) ∧ True) ∨ p1)) → ((True ∧ p3) ∨ True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
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
    -- Disjunctions on the left can always be decomposed.
    cases h5
    case inl h7 =>
      -- Conjunctions on the left can always be decomposed.
      let h8 := h7.left
      let h9 := h7.right
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- True on the right can always be proven directly.
      apply True.intro
    case inr h10 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- True on the right can always be proven directly.
      apply True.intro
  case inr h11 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_196756137567120666617879483314 : (((((p3 ∨ p4) → False) ∨ (p1 ∨ p4)) ∧ False) ∨ (((p3 ∧ p1) → p3) ∨ (((p3 ∨ p4) ∨ p2) → (p5 → (p3 ∧ ((True → p1) → p4)))))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- One of the premise coincides with the conclusion.
  exact h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_597815529601965815080355096059 : ((((((p1 ∨ False) ∧ p3) ∧ ((p4 ∨ (p4 ∨ (True ∧ (p1 → ((False ∧ ((p5 → (p2 ∨ False)) ∨ p3)) ∨ p4))))) ∧ (p2 ∧ p1))) ∧ False) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_119549451494127908096847073637 : ((p5 → (((((p1 → (p3 ∧ (False ∨ (p4 ∨ p2)))) → (p3 ∧ p1)) ∧ ((p1 → p4) ∨ False)) ∨ False) ∨ (p3 ∨ (False ∧ p2)))) ∨ (True ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_40337967910802944369573818932 : (((((((p2 ∨ p2) → (p3 ∨ p3)) → ((p3 ∧ p3) ∧ ((p5 ∧ ((((p2 ∨ True) → True) ∨ p3) ∨ False)) ∧ True))) ∨ p1) ∨ p3) ∨ False) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_593547861943021952029193729081 : (((((p5 ∧ (p2 ∧ (p2 ∨ (((p3 ∧ p4) ∨ ((p4 ∧ (((p1 ∨ False) ∨ p5) ∨ p5)) ∨ p4)) → p5)))) → (p2 → (False ∧ p5))) ∧ p5) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_342745849989791550122500387568 : (p2 → ((((((p4 ∧ p2) → p1) ∨ False) → p3) ∨ False) ∨ (((((p3 ∨ (p1 → p3)) ∧ (((p1 ∧ p4) ∨ p1) → False)) ∧ p2) ∨ p2) ∨ True))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_164737892869588807949730925585 : (((((((p3 ∧ True) ∧ p5) ∨ p2) ∨ ((p2 ∨ p5) → (p3 → p3))) ∧ (True → p2)) ∨ p3) ∨ ((((p4 ∧ p1) ∨ p2) ∧ (p3 ∧ p4)) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_792339408514713181705564903698 : (((True → ((p5 ∨ ((True ∧ p5) ∨ (False → (((True ∨ p4) → p1) ∨ (p3 → (False ∨ p4)))))) → (p3 ∨ ((p2 ∧ p4) ∨ (False → p2))))) ∨ p1) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
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
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h4
    -- False on the left can always be used.
    apply False.elim h4
  case inr h5 =>
    -- Disjunctions on the left can always be decomposed.
    cases h5
    case inl h6 =>
      -- Conjunctions on the left can always be decomposed.
      let h7 := h6.left
      let h8 := h6.right
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Implications on the right can always be decomposed.
      intro h9
      -- False on the left can always be used.
      apply False.elim h9
    case inr h10 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Implications on the right can always be decomposed.
      intro h11
      -- False on the left can always be used.
      apply False.elim h11
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_117861840857906562255833464078 : ((p5 ∧ ((True → (((((((p2 ∧ (p3 → p3)) ∧ ((p4 ∧ (p2 ∨ p4)) ∧ p2)) ∧ p5) → p3) → p2) ∨ p3) → p5)) ∧ p4)) ∨ (p3 → True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_688226288444061594692946210548 : (((((p3 ∨ p5) ∧ ((p5 ∧ ((p5 ∧ ((p3 → False) → (False → p2))) ∨ p3)) ∨ p1)) ∧ (False ∧ ((True → (True ∨ False)) → (p1 ∧ p1)))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_653653779306115347190283590542 : ((((((p5 ∧ ((p3 ∨ p5) ∧ ((((p1 ∨ p4) → p4) ∨ p2) → ((p2 → (p2 ∧ (p3 ∨ p5))) ∨ p4)))) ∨ p4) ∧ p2) ∨ (False ∨ p2)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_184753723838167980475994448765 : ((((p2 ∧ p1) → (p4 → False)) ∧ (((p1 ∨ True) ∧ p4) ∧ p4)) ∨ (p2 → (((False ∨ False) → (p1 ∨ p4)) ∧ (True ∧ ((True → False) → p1))))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h2
  -- Disjunctions on the left can always be decomposed.
  cases h2
  case inl h3 =>
    -- False on the left can always be used.
    apply False.elim h3
  case inr h4 =>
    -- False on the left can always be used.
    apply False.elim h4
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- Implications on the right can always be decomposed.
  intro h5
  -- We want to use the implication h5 based on <expert-advice>. So we show its premise.
  have h6 : True := by
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h5, we can now drive its conclusion.
  let h7 := h5 h6
  -- False on the left can always be used.
  apply False.elim h7



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_114439463523556720036263911882 : (((p5 ∨ ((p3 ∧ ((((p2 → (p1 → p1)) → p5) ∧ (True ∨ p5)) ∨ p4)) ∨ (p2 → p2))) ∨ ((True ∧ p3) ∧ (p2 → p1))) ∨ (False ∨ p4)) := by
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
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_56757627694273182249533882523 : ((((p3 → p4) ∨ p1) ∧ (True → (p2 ∧ ((p3 ∨ (((p1 ∨ (p3 ∧ False)) ∨ ((p5 ∧ p1) ∧ p2)) → (True → (False → p1)))) → p2)))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_111018724812748776324294962836 : (((((False → ((((p5 → p1) → (p5 → False)) ∨ (p4 ∧ ((False ∧ False) ∨ p3))) ∨ p3)) ∧ p3) → (p1 ∨ (p4 ∧ True))) ∧ p2) ∨ (True ∧ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_4174128387299605600803039594 : (p4 ∨ (((p1 ∨ False) ∧ (p4 → True)) → (((p5 → (True → p2)) ∧ p2) ∨ (((p3 ∧ True) ∨ (((True → False) ∨ p5) → p2)) → p1)))) := by
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
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h5
    -- Disjunctions on the left can always be decomposed.
    cases h5
    case inl h6 =>
      -- Conjunctions on the left can always be decomposed.
      let h7 := h6.left
      let h8 := h6.right
      -- One of the premise coincides with the conclusion.
      exact h4
    case inr h9 =>
      -- One of the premise coincides with the conclusion.
      exact h4
  case inr h10 =>
    -- False on the left can always be used.
    apply False.elim h10



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_190029688002184328500954021009 : ((((p3 → (((False ∧ True) → p2) ∨ p3)) ∧ p1) ∧ p5) ∨ ((p4 ∧ (p4 ∨ (((p1 → p1) ∨ (p4 ∨ (p3 ∧ p2))) ∨ p4))) → (p5 ∨ p4))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- Disjunctions on the left can always be decomposed.
  cases h3
  case inl h4 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h4
  case inr h5 =>
    -- Disjunctions on the left can always be decomposed.
    cases h5
    case inl h6 =>
      -- Disjunctions on the left can always be decomposed.
      cases h6
      case inl h7 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- One of the premise coincides with the conclusion.
        exact h2
      case inr h8 =>
        -- Disjunctions on the left can always be decomposed.
        cases h8
        case inl h9 =>
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- One of the premise coincides with the conclusion.
          exact h9
        case inr h10 =>
          -- Conjunctions on the left can always be decomposed.
          let h11 := h10.left
          let h12 := h10.right
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- One of the premise coincides with the conclusion.
          exact h2
    case inr h13 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- One of the premise coincides with the conclusion.
      exact h13



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_696375530887476345746863981903 : ((((p4 → (p3 ∨ (((p5 ∨ False) → p1) ∨ ((True ∧ True) ∧ (p4 ∨ p2))))) → (((p5 ∨ True) → ((True ∧ (p2 ∨ p4)) ∧ False)) → False)) ∨ False) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
  have h3 : (p5 ∨ True) := by
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h2, we can now drive its conclusion.
  let h4 := h2 h3
  -- We need to get the right conjuct of h4 based on <expert-advice>.
  let h5 := h4.right
  -- False on the left can always be used.
  apply False.elim h5
  -- True on the right can always be proven directly.
  apply True.intro



