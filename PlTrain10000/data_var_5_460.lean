variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_752251609326184982419367664107 : (((True ∧ (p4 → (p4 ∧ ((((p2 ∧ p3) → ((((p1 ∧ (p2 → p4)) ∨ (p5 ∨ p2)) → p1) ∧ False)) → p4) → ((p2 ∧ p1) ∨ p1))))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_217962617749121660421595336797 : (((p2 ∧ True) ∧ (p5 → False)) → (((p4 → False) ∧ p4) → ((p5 ∧ ((p4 ∨ p4) → (p3 ∧ (p2 ∧ (p4 ∧ (p2 → True)))))) ∧ (p3 ∨ True)))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Conjunctions on the left can always be decomposed.
  let h3 := h2.left
  let h4 := h2.right
  -- Conjunctions on the left can always be decomposed.
  let h5 := h1.left
  let h6 := h1.right
  -- Conjunctions on the left can always be decomposed.
  let h7 := h5.left
  let h8 := h5.right
  -- We want to use the implication h3 based on <expert-advice>. So we show its premise.
  have h9 : p4 := by
    -- One of the premise coincides with the conclusion.
    exact h4
  -- We have shown the premise of h3, we can now drive its conclusion.
  let h10 := h3 h9
  -- False on the left can always be used.
  apply False.elim h10
  -- Implications on the right can always be decomposed.
  intro h11
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Disjunctions on the left can always be decomposed.
  cases h11
  case inl h12 =>
    -- Conjunctions on the left can always be decomposed.
    let h13 := h2.left
    let h14 := h2.right
    -- Conjunctions on the left can always be decomposed.
    let h15 := h1.left
    let h16 := h1.right
    -- Conjunctions on the left can always be decomposed.
    let h17 := h15.left
    let h18 := h15.right
    -- We want to use the implication h13 based on <expert-advice>. So we show its premise.
    have h19 : p4 := by
      -- One of the premise coincides with the conclusion.
      exact h14
    -- We have shown the premise of h13, we can now drive its conclusion.
    let h20 := h13 h19
    -- False on the left can always be used.
    apply False.elim h20
  case inr h21 =>
    -- Conjunctions on the left can always be decomposed.
    let h22 := h2.left
    let h23 := h2.right
    -- Conjunctions on the left can always be decomposed.
    let h24 := h1.left
    let h25 := h1.right
    -- Conjunctions on the left can always be decomposed.
    let h26 := h24.left
    let h27 := h24.right
    -- We want to use the implication h22 based on <expert-advice>. So we show its premise.
    have h28 : p4 := by
      -- One of the premise coincides with the conclusion.
      exact h23
    -- We have shown the premise of h22, we can now drive its conclusion.
    let h29 := h22 h28
    -- False on the left can always be used.
    apply False.elim h29
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Disjunctions on the left can always be decomposed.
  cases h11
  case inl h30 =>
    -- Conjunctions on the left can always be decomposed.
    let h31 := h2.left
    let h32 := h2.right
    -- Conjunctions on the left can always be decomposed.
    let h33 := h1.left
    let h34 := h1.right
    -- Conjunctions on the left can always be decomposed.
    let h35 := h33.left
    let h36 := h33.right
    -- One of the premise coincides with the conclusion.
    exact h35
  case inr h37 =>
    -- Conjunctions on the left can always be decomposed.
    let h38 := h2.left
    let h39 := h2.right
    -- Conjunctions on the left can always be decomposed.
    let h40 := h1.left
    let h41 := h1.right
    -- Conjunctions on the left can always be decomposed.
    let h42 := h40.left
    let h43 := h40.right
    -- One of the premise coincides with the conclusion.
    exact h42
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Disjunctions on the left can always be decomposed.
  cases h11
  case inl h44 =>
    -- Conjunctions on the left can always be decomposed.
    let h45 := h2.left
    let h46 := h2.right
    -- Conjunctions on the left can always be decomposed.
    let h47 := h1.left
    let h48 := h1.right
    -- Conjunctions on the left can always be decomposed.
    let h49 := h47.left
    let h50 := h47.right
    -- One of the premise coincides with the conclusion.
    exact h46
  case inr h51 =>
    -- Conjunctions on the left can always be decomposed.
    let h52 := h2.left
    let h53 := h2.right
    -- Conjunctions on the left can always be decomposed.
    let h54 := h1.left
    let h55 := h1.right
    -- Conjunctions on the left can always be decomposed.
    let h56 := h54.left
    let h57 := h54.right
    -- One of the premise coincides with the conclusion.
    exact h53
  -- Implications on the right can always be decomposed.
  intro h58
  -- True on the right can always be proven directly.
  apply True.intro
  -- Conjunctions on the left can always be decomposed.
  let h59 := h2.left
  let h60 := h2.right
  -- Conjunctions on the left can always be decomposed.
  let h61 := h1.left
  let h62 := h1.right
  -- Conjunctions on the left can always be decomposed.
  let h63 := h61.left
  let h64 := h61.right
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_246728257799359537983606425246 : ((p5 ∧ p4) ∨ (p1 → ((p4 → (((p3 ∧ p4) → ((p4 → ((False → p2) → p5)) ∨ (((True ∧ p3) → (True ∧ p4)) → p1))) ∧ p3)) ∨ p1))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_64329036363185589762786579161 : ((p1 ∨ (((((True ∨ p5) ∧ p1) ∨ p3) → ((p5 → (p5 ∨ (((False ∨ (p3 ∧ ((True ∨ p3) ∧ p3))) → p3) → p1))) → p3)) ∧ p2)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_616615568835534543132017172530 : ((((((p1 ∧ False) ∧ (p2 → ((p5 → p5) → (True → p4)))) ∧ ((True → (p4 → ((((p5 → p4) → True) ∨ True) → True))) → False)) ∨ p4) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_329619404411649408909777268275 : (True → ((p5 → False) ∨ (((p4 ∨ (p5 ∧ p5)) ∨ ((True → (p3 ∨ True)) ∨ (p1 ∨ (p5 ∧ ((p4 ∨ p2) ∧ p4))))) ∧ (False → (False ∧ False))))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h2
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- Implications on the right can always be decomposed.
  intro h3
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- False on the left can always be used.
  apply False.elim h3
  -- False on the left can always be used.
  apply False.elim h3



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_778901196992642259676380130401 : (((p1 ∨ (p1 → (((p5 ∧ False) ∨ ((((p5 ∧ p5) ∨ (True ∨ False)) ∨ p1) ∧ ((p3 → p3) ∨ False))) → ((False ∧ (p3 ∧ True)) ∨ False)))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_172148549748460880142326178427 : (((p3 → (((((False ∨ p5) ∧ p1) ∨ p3) → p5) → False)) ∧ ((True ∧ p1) ∨ p5)) ∨ ((False → (p2 ∧ p1)) ∨ ((True → p4) ∨ (p5 ∧ p5)))) := by
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
theorem thm_5_vars_197039769130958230100916952231 : ((((p3 ∧ True) ∧ ((p5 ∧ p2) ∨ p4)) ∨ p2) ∨ (((((((False ∧ (True → False)) ∧ p4) → True) ∨ p3) → p2) → (p4 ∨ (p4 → p2))) ∨ p4)) := by
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
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h3 : ((((False ∧ (True → False)) ∧ p4) → True) ∨ p3) := by
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Implications on the right can always be decomposed.
    intro h4
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h5 := h1 h3
  -- One of the premise coincides with the conclusion.
  exact h5



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_214672788068337471551617651880 : (((p4 → p3) ∧ (p2 ∨ False)) ∨ (((((((False ∧ (p3 ∨ False)) ∨ p1) ∧ p1) ∨ p4) ∧ True) ∨ (((False ∧ (False → False)) ∧ p2) → True)) ∨ p5)) := by
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
theorem thm_5_vars_117271797864582391005147956292 : ((False ∧ ((p1 → (p4 ∧ (p2 ∨ (False ∧ (((((p3 → p4) ∧ (p2 ∧ p4)) ∨ p4) → p5) ∧ (p3 ∧ (True ∧ True))))))) ∧ True)) ∨ (False → p4)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_390661329717728397852660849265 : ((((((p4 ∨ ((p3 ∨ p3) ∧ p1)) ∨ (p4 → False)) ∨ (((((p3 ∧ p5) ∨ True) ∧ True) ∨ p1) ∨ (p5 → (p4 → (False → p1))))) ∨ False) ∧ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
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
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_135853839955892457394029224068 : (((((p1 ∨ p1) ∧ (p5 ∧ ((p2 ∨ True) ∧ (p2 ∨ p5)))) ∧ p1) ∨ (p5 → ((True → False) ∨ ((p2 ∨ False) ∨ True)))) ∨ (p1 ∧ (p2 → p3))) := by
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



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_652868997933758221966868549234 : ((((p4 ∨ (((p4 → ((p5 → ((p5 ∨ True) → False)) ∨ (False ∨ ((False ∧ ((True ∧ p5) → p5)) → p5)))) ∨ p3) ∧ p2)) ∧ (True ∨ p5)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_217349909157332571701509398829 : (((p2 ∨ (p3 ∨ p2)) ∨ True) → ((True ∨ (((((True → p4) ∧ (p5 ∨ p4)) → p3) ∨ (p2 → (False → (p5 ∨ p1)))) ∧ p2)) → (p4 → p4))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Implications on the right can always be decomposed.
  intro h3
  -- Disjunctions on the left can always be decomposed.
  cases h2
  case inl h4 =>
    -- Disjunctions on the left can always be decomposed.
    cases h1
    case inl h5 =>
      -- Disjunctions on the left can always be decomposed.
      cases h5
      case inl h6 =>
        -- One of the premise coincides with the conclusion.
        exact h3
      case inr h7 =>
        -- Disjunctions on the left can always be decomposed.
        cases h7
        case inl h8 =>
          -- One of the premise coincides with the conclusion.
          exact h3
        case inr h9 =>
          -- One of the premise coincides with the conclusion.
          exact h3
    case inr h10 =>
      -- One of the premise coincides with the conclusion.
      exact h3
  case inr h11 =>
    -- Conjunctions on the left can always be decomposed.
    let h12 := h11.left
    let h13 := h11.right
    -- Disjunctions on the left can always be decomposed.
    cases h12
    case inl h14 =>
      -- Disjunctions on the left can always be decomposed.
      cases h1
      case inl h15 =>
        -- Disjunctions on the left can always be decomposed.
        cases h15
        case inl h16 =>
          -- One of the premise coincides with the conclusion.
          exact h3
        case inr h17 =>
          -- Disjunctions on the left can always be decomposed.
          cases h17
          case inl h18 =>
            -- One of the premise coincides with the conclusion.
            exact h3
          case inr h19 =>
            -- One of the premise coincides with the conclusion.
            exact h3
      case inr h20 =>
        -- One of the premise coincides with the conclusion.
        exact h3
    case inr h21 =>
      -- Disjunctions on the left can always be decomposed.
      cases h1
      case inl h22 =>
        -- Disjunctions on the left can always be decomposed.
        cases h22
        case inl h23 =>
          -- One of the premise coincides with the conclusion.
          exact h3
        case inr h24 =>
          -- Disjunctions on the left can always be decomposed.
          cases h24
          case inl h25 =>
            -- One of the premise coincides with the conclusion.
            exact h3
          case inr h26 =>
            -- One of the premise coincides with the conclusion.
            exact h3
      case inr h27 =>
        -- One of the premise coincides with the conclusion.
        exact h3



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_136361962854899787964804622058 : ((((p5 ∨ (p4 → p5)) ∧ p4) ∨ (((p5 → (p5 → (p4 → (p2 ∧ ((p5 ∧ (p3 ∨ True)) ∨ True))))) ∨ p3) ∨ True)) ∨ ((p2 → False) → p1)) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_114367563417191645900004172000 : (((((((p2 → (True → p4)) ∧ (p1 ∧ ((p4 ∧ p3) ∨ p1))) ∧ p1) ∧ (False ∧ p3)) ∨ True) ∨ (((False ∧ p1) → p3) → False)) ∨ (p3 ∨ p3)) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_60025843502175270424428934977 : (((p1 ∨ p2) → ((((((p1 → p1) ∨ False) ∨ True) → False) ∧ (((p3 ∨ p1) ∨ (p4 ∧ (p1 → p4))) ∨ ((True ∧ False) ∨ p4))) → p3)) ∨ p3) := by
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
  cases h4
  case inl h5 =>
    -- Disjunctions on the left can always be decomposed.
    cases h5
    case inl h6 =>
      -- Disjunctions on the left can always be decomposed.
      cases h6
      case inl h7 =>
        -- Disjunctions on the left can always be decomposed.
        cases h1
        case inl h8 =>
          -- One of the premise coincides with the conclusion.
          exact h7
        case inr h9 =>
          -- One of the premise coincides with the conclusion.
          exact h7
      case inr h10 =>
        -- Disjunctions on the left can always be decomposed.
        cases h1
        case inl h11 =>
          -- We want to use the implication h3 based on <expert-advice>. So we show its premise.
          have h12 : (((p1 → p1) ∨ False) ∨ True) := by
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
          have h15 : (((p1 → p1) ∨ False) ∨ True) := by
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
      let h18 := h17.left
      let h19 := h17.right
      -- Disjunctions on the left can always be decomposed.
      cases h1
      case inl h20 =>
        -- We want to use the implication h3 based on <expert-advice>. So we show its premise.
        have h21 : (((p1 → p1) ∨ False) ∨ True) := by
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- True on the right can always be proven directly.
          apply True.intro
        -- We have shown the premise of h3, we can now drive its conclusion.
        let h22 := h3 h21
        -- False on the left can always be used.
        apply False.elim h22
      case inr h23 =>
        -- We want to use the implication h3 based on <expert-advice>. So we show its premise.
        have h24 : (((p1 → p1) ∨ False) ∨ True) := by
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- True on the right can always be proven directly.
          apply True.intro
        -- We have shown the premise of h3, we can now drive its conclusion.
        let h25 := h3 h24
        -- False on the left can always be used.
        apply False.elim h25
  case inr h26 =>
    -- Disjunctions on the left can always be decomposed.
    cases h26
    case inl h27 =>
      -- Conjunctions on the left can always be decomposed.
      let h28 := h27.left
      let h29 := h27.right
      -- False on the left can always be used.
      apply False.elim h29
    case inr h30 =>
      -- Disjunctions on the left can always be decomposed.
      cases h1
      case inl h31 =>
        -- We want to use the implication h3 based on <expert-advice>. So we show its premise.
        have h32 : (((p1 → p1) ∨ False) ∨ True) := by
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- True on the right can always be proven directly.
          apply True.intro
        -- We have shown the premise of h3, we can now drive its conclusion.
        let h33 := h3 h32
        -- False on the left can always be used.
        apply False.elim h33
      case inr h34 =>
        -- We want to use the implication h3 based on <expert-advice>. So we show its premise.
        have h35 : (((p1 → p1) ∨ False) ∨ True) := by
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- True on the right can always be proven directly.
          apply True.intro
        -- We have shown the premise of h3, we can now drive its conclusion.
        let h36 := h3 h35
        -- False on the left can always be used.
        apply False.elim h36



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_341989988450268809674917004758 : (p2 → ((((False ∨ (p2 → ((True ∨ (True → p1)) ∧ (False ∧ p4)))) → p3) → ((((p4 ∧ p1) ∨ p4) ∨ True) → False)) ∨ ((False ∨ p2) ∨ p2))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_86581069956106259462167214035 : (((((p2 ∨ (p4 ∧ (p5 ∨ p2))) ∨ True) → p3) ∧ (((p5 → True) ∨ ((False → p3) ∨ p3)) ∧ ((p2 ∧ (p1 → True)) → (True ∨ p3)))) → p3) := by
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
    -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
    have h7 : ((p2 ∨ (p4 ∧ (p5 ∨ p2))) ∨ True) := by
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- True on the right can always be proven directly.
      apply True.intro
    -- We have shown the premise of h2, we can now drive its conclusion.
    let h8 := h2 h7
    -- One of the premise coincides with the conclusion.
    exact h8
  case inr h9 =>
    -- Disjunctions on the left can always be decomposed.
    cases h9
    case inl h10 =>
      -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
      have h11 : ((p2 ∨ (p4 ∧ (p5 ∨ p2))) ∨ True) := by
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- True on the right can always be proven directly.
        apply True.intro
      -- We have shown the premise of h2, we can now drive its conclusion.
      let h12 := h2 h11
      -- One of the premise coincides with the conclusion.
      exact h12
    case inr h13 =>
      -- One of the premise coincides with the conclusion.
      exact h13



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_350175768527949210995034739458 : (p4 → (((False ∨ (((p1 → p2) ∨ False) ∨ p4)) → ((True → (((p5 ∨ (p5 ∧ False)) ∧ p1) ∨ ((False ∨ (p1 ∧ p4)) ∨ p4))) ∨ False)) ∨ p3)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h2
  -- Disjunctions on the left can always be decomposed.
  cases h2
  case inl h3 =>
    -- False on the left can always be used.
    apply False.elim h3
  case inr h4 =>
    -- Disjunctions on the left can always be decomposed.
    cases h4
    case inl h5 =>
      -- Disjunctions on the left can always be decomposed.
      cases h5
      case inl h6 =>
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- Implications on the right can always be decomposed.
        intro h7
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- One of the premise coincides with the conclusion.
        exact h1
      case inr h8 =>
        -- False on the left can always be used.
        apply False.elim h8
    case inr h9 =>
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- Implications on the right can always be decomposed.
      intro h10
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- One of the premise coincides with the conclusion.
      exact h9



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_111963189560308575382468260028 : (((((False → p2) → (p4 ∨ ((True → p1) → p4))) → (p5 ∧ ((((p5 ∧ p3) ∨ (p4 ∨ p2)) → False) ∧ (False ∧ False)))) ∨ True) ∨ (p2 ∧ True)) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_65883422322271745519693185751 : ((p4 ∨ ((p3 ∨ p3) → (p4 ∨ (((((True → p5) ∨ (((False ∨ ((p1 → p5) ∨ False)) → True) ∧ (False ∧ p2))) ∨ p2) ∧ p3) → p4)))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_611277701541125776967329196894 : ((((((True ∨ p2) ∨ ((p1 ∧ (p3 ∨ (False ∨ ((p4 → ((p5 ∨ p2) ∧ p3)) ∧ (p1 ∧ (False ∨ (p1 → p4))))))) → True)) → p5) ∨ False) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_111331394588343538779380272913 : (((p2 ∧ ((False ∧ p1) ∨ (p3 ∧ ((p2 → (p4 → (p4 ∧ ((True ∧ True) ∨ (False ∨ (p5 ∧ p5)))))) ∧ (p1 ∨ p5))))) ∧ p2) ∨ (p3 → p3)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_44386790136723978440596949577 : (((((False ∧ (True ∧ ((p4 ∨ False) → (p1 ∨ p5)))) ∧ (p3 → (p2 ∧ False))) ∨ ((p3 ∨ (p5 → (p4 ∧ p4))) ∧ (p5 → p1))) → False) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_168319889943712466322910221493 : (((p1 → p1) ∧ ((p1 ∧ ((False ∨ (p3 ∨ (p3 ∨ (p1 → p4)))) ∧ False)) ∨ (p2 ∨ p2))) → (((p2 → p3) ∨ (p4 ∧ (p5 → p3))) ∨ True)) := by
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
    -- Conjunctions on the left can always be decomposed.
    let h7 := h6.left
    let h8 := h6.right
    -- Disjunctions on the left can always be decomposed.
    cases h7
    case inl h9 =>
      -- False on the left can always be used.
      apply False.elim h9
    case inr h10 =>
      -- Disjunctions on the left can always be decomposed.
      cases h10
      case inl h11 =>
        -- False on the left can always be used.
        apply False.elim h8
      case inr h12 =>
        -- Disjunctions on the left can always be decomposed.
        cases h12
        case inl h13 =>
          -- False on the left can always be used.
          apply False.elim h8
        case inr h14 =>
          -- False on the left can always be used.
          apply False.elim h8
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



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_261964243043974947514211351535 : (True ∧ (((True → p2) ∨ (False ∨ ((((p3 → p2) ∧ p1) ∧ (p2 ∧ ((p4 ∧ p3) ∧ ((p1 → False) ∧ (p5 → p3))))) ∨ (False → p1)))) ∧ True)) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- False on the left can always be used.
  apply False.elim h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_804471896412881637450895932127 : (((p3 → ((((p2 ∧ p5) → p3) → ((False → p1) → False)) ∨ (True ∨ ((p5 ∨ True) ∨ (((p3 ∧ (p1 → (True ∧ p2))) ∧ p1) ∨ False))))) ∨ p2) ∧ True) := by
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
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_709523718882931062340065398829 : ((((p5 ∧ (p2 ∨ ((p5 ∨ (p2 ∨ False)) → p1))) → ((p3 ∧ (p5 → (p4 ∧ (False ∨ p4)))) ∨ (p4 → (True ∧ (p5 → (p4 ∧ p4)))))) ∨ False) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
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
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h5
    -- Conjunctions on the right can always be decomposed.
    apply And.intro
    -- True on the right can always be proven directly.
    apply True.intro
    -- Implications on the right can always be decomposed.
    intro h6
    -- Conjunctions on the right can always be decomposed.
    apply And.intro
    -- One of the premise coincides with the conclusion.
    exact h5
    -- One of the premise coincides with the conclusion.
    exact h5
  case inr h7 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h8
    -- Conjunctions on the right can always be decomposed.
    apply And.intro
    -- True on the right can always be proven directly.
    apply True.intro
    -- Implications on the right can always be decomposed.
    intro h9
    -- Conjunctions on the right can always be decomposed.
    apply And.intro
    -- One of the premise coincides with the conclusion.
    exact h8
    -- One of the premise coincides with the conclusion.
    exact h8
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_616237398110346657000164992673 : (((((((True ∧ ((p4 ∧ (p1 ∧ p3)) ∨ (p1 ∨ p5))) ∧ p3) ∧ p3) ∨ ((True ∨ ((p4 ∨ p1) ∨ p1)) ∨ ((False ∨ p3) → p2))) ∨ p4) ∨ p4) ∧ True) := by
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
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_354934125119248628452893174151 : (p5 → ((p4 ∨ (((p2 ∧ (True → (((p1 ∧ p2) ∧ p4) ∧ True))) ∧ ((p5 → p2) → ((True ∨ True) ∧ (p1 ∧ p4)))) → (p3 ∨ False))) ∨ True)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_65257409845942638999659371856 : ((p3 ∨ (((p3 ∨ (p2 ∨ (p2 → p4))) ∧ (p1 ∨ (True ∨ (((p1 ∨ True) ∧ ((p2 ∧ True) ∨ (p4 ∧ False))) ∧ (p1 → p4))))) → p3)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_714156377809889050044198236851 : (((((p2 ∨ (p4 ∨ (p1 → p3))) → True) → ((p2 ∨ (((((False ∨ p2) ∨ False) ∨ p5) → (p4 ∧ (p3 ∨ p3))) ∧ (p2 → p2))) ∨ p3)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_677427627442520280107771866639 : (((((((p2 ∨ (True → ((((p3 ∧ p1) → True) → p1) ∧ True))) ∧ (True ∧ True)) ∧ (p5 ∨ p2)) ∨ False) ∨ (p5 ∨ (True → (True ∨ p1)))) ∨ p5) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
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
theorem thm_5_vars_70270720000382672418227687314 : (((((((p1 → p1) → False) ∧ ((p1 → p2) ∧ (p5 → p2))) ∧ (p1 ∧ (p2 ∨ (p5 ∨ ((p4 ∧ p1) ∨ p1))))) ∧ (p5 ∧ p5)) ∧ p4) → p3) := by
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
  -- Conjunctions on the left can always be decomposed.
  let h10 := h9.left
  let h11 := h9.right
  -- Conjunctions on the left can always be decomposed.
  let h12 := h7.left
  let h13 := h7.right
  -- Disjunctions on the left can always be decomposed.
  cases h13
  case inl h14 =>
    -- Conjunctions on the left can always be decomposed.
    let h15 := h5.left
    let h16 := h5.right
    -- We want to use the implication h8 based on <expert-advice>. So we show its premise.
    have h17 : (p1 → p1) := by
      -- Implications on the right can always be decomposed.
      intro h18
      -- One of the premise coincides with the conclusion.
      exact h18
    -- We have shown the premise of h8, we can now drive its conclusion.
    let h19 := h8 h17
    -- False on the left can always be used.
    apply False.elim h19
  case inr h20 =>
    -- Disjunctions on the left can always be decomposed.
    cases h20
    case inl h21 =>
      -- Conjunctions on the left can always be decomposed.
      let h22 := h5.left
      let h23 := h5.right
      -- We want to use the implication h8 based on <expert-advice>. So we show its premise.
      have h24 : (p1 → p1) := by
        -- Implications on the right can always be decomposed.
        intro h25
        -- One of the premise coincides with the conclusion.
        exact h25
      -- We have shown the premise of h8, we can now drive its conclusion.
      let h26 := h8 h24
      -- False on the left can always be used.
      apply False.elim h26
    case inr h27 =>
      -- Disjunctions on the left can always be decomposed.
      cases h27
      case inl h28 =>
        -- Conjunctions on the left can always be decomposed.
        let h29 := h28.left
        let h30 := h28.right
        -- Conjunctions on the left can always be decomposed.
        let h31 := h5.left
        let h32 := h5.right
        -- We want to use the implication h8 based on <expert-advice>. So we show its premise.
        have h33 : (p1 → p1) := by
          -- Implications on the right can always be decomposed.
          intro h34
          -- One of the premise coincides with the conclusion.
          exact h34
        -- We have shown the premise of h8, we can now drive its conclusion.
        let h35 := h8 h33
        -- False on the left can always be used.
        apply False.elim h35
      case inr h36 =>
        -- Conjunctions on the left can always be decomposed.
        let h37 := h5.left
        let h38 := h5.right
        -- We want to use the implication h8 based on <expert-advice>. So we show its premise.
        have h39 : (p1 → p1) := by
          -- Implications on the right can always be decomposed.
          intro h40
          -- One of the premise coincides with the conclusion.
          exact h40
        -- We have shown the premise of h8, we can now drive its conclusion.
        let h41 := h8 h39
        -- False on the left can always be used.
        apply False.elim h41



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_749117317634729860188364806891 : ((((p5 → False) → (p2 ∧ ((((p2 ∨ (p5 → (p4 → (False → p1)))) ∧ p1) ∧ ((p1 ∨ (p1 → True)) ∧ (True ∨ p3))) ∨ (p1 → p3)))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_59069152156871410931454366115 : (((p5 ∧ False) ∨ (((p1 ∨ (((p2 → (p1 ∨ p1)) ∧ (p2 ∨ ((p1 → p3) → (p5 → ((p4 ∧ p4) ∨ p1))))) ∧ True)) ∧ p4) ∨ True)) ∨ False) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_54336396940500449742385418455 : (((p4 ∧ (p4 ∨ ((True ∨ (p4 ∨ True)) ∧ p2))) ∧ ((p3 ∧ (True → (((False → False) → False) → (p1 ∧ False)))) ∧ ((p1 → p3) ∧ False))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_168063103160878377007207766670 : ((((p3 → (p3 → True)) ∨ p3) ∧ ((((False ∨ p3) ∨ True) → p3) ∧ (True ∧ (p3 → p2)))) → (p2 ∧ (((p1 ∨ p1) ∨ (p1 ∨ p1)) → p2))) := by
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
    -- Conjunctions on the left can always be decomposed.
    let h7 := h6.left
    let h8 := h6.right
    -- We want to use the implication h5 based on <expert-advice>. So we show its premise.
    have h9 : ((False ∨ p3) ∨ True) := by
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- True on the right can always be proven directly.
      apply True.intro
    -- We have shown the premise of h5, we can now drive its conclusion.
    let h10 := h5 h9
    -- We want to use the implication h8 based on <expert-advice>. So we show its premise.
    have h11 : p3 := by
      -- One of the premise coincides with the conclusion.
      exact h10
    -- We have shown the premise of h8, we can now drive its conclusion.
    let h12 := h8 h11
    -- One of the premise coincides with the conclusion.
    exact h12
  case inr h13 =>
    -- Conjunctions on the left can always be decomposed.
    let h14 := h3.left
    let h15 := h3.right
    -- Conjunctions on the left can always be decomposed.
    let h16 := h15.left
    let h17 := h15.right
    -- We want to use the implication h17 based on <expert-advice>. So we show its premise.
    have h18 : p3 := by
      -- One of the premise coincides with the conclusion.
      exact h13
    -- We have shown the premise of h17, we can now drive its conclusion.
    let h19 := h17 h18
    -- One of the premise coincides with the conclusion.
    exact h19
  -- Implications on the right can always be decomposed.
  intro h20
  -- Disjunctions on the left can always be decomposed.
  cases h20
  case inl h21 =>
    -- Disjunctions on the left can always be decomposed.
    cases h21
    case inl h22 =>
      -- Conjunctions on the left can always be decomposed.
      let h23 := h1.left
      let h24 := h1.right
      -- Disjunctions on the left can always be decomposed.
      cases h23
      case inl h25 =>
        -- Conjunctions on the left can always be decomposed.
        let h26 := h24.left
        let h27 := h24.right
        -- Conjunctions on the left can always be decomposed.
        let h28 := h27.left
        let h29 := h27.right
        -- We want to use the implication h26 based on <expert-advice>. So we show its premise.
        have h30 : ((False ∨ p3) ∨ True) := by
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- True on the right can always be proven directly.
          apply True.intro
        -- We have shown the premise of h26, we can now drive its conclusion.
        let h31 := h26 h30
        -- We want to use the implication h29 based on <expert-advice>. So we show its premise.
        have h32 : p3 := by
          -- One of the premise coincides with the conclusion.
          exact h31
        -- We have shown the premise of h29, we can now drive its conclusion.
        let h33 := h29 h32
        -- One of the premise coincides with the conclusion.
        exact h33
      case inr h34 =>
        -- Conjunctions on the left can always be decomposed.
        let h35 := h24.left
        let h36 := h24.right
        -- Conjunctions on the left can always be decomposed.
        let h37 := h36.left
        let h38 := h36.right
        -- We want to use the implication h38 based on <expert-advice>. So we show its premise.
        have h39 : p3 := by
          -- One of the premise coincides with the conclusion.
          exact h34
        -- We have shown the premise of h38, we can now drive its conclusion.
        let h40 := h38 h39
        -- One of the premise coincides with the conclusion.
        exact h40
    case inr h41 =>
      -- Conjunctions on the left can always be decomposed.
      let h42 := h1.left
      let h43 := h1.right
      -- Disjunctions on the left can always be decomposed.
      cases h42
      case inl h44 =>
        -- Conjunctions on the left can always be decomposed.
        let h45 := h43.left
        let h46 := h43.right
        -- Conjunctions on the left can always be decomposed.
        let h47 := h46.left
        let h48 := h46.right
        -- We want to use the implication h45 based on <expert-advice>. So we show its premise.
        have h49 : ((False ∨ p3) ∨ True) := by
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- True on the right can always be proven directly.
          apply True.intro
        -- We have shown the premise of h45, we can now drive its conclusion.
        let h50 := h45 h49
        -- We want to use the implication h48 based on <expert-advice>. So we show its premise.
        have h51 : p3 := by
          -- One of the premise coincides with the conclusion.
          exact h50
        -- We have shown the premise of h48, we can now drive its conclusion.
        let h52 := h48 h51
        -- One of the premise coincides with the conclusion.
        exact h52
      case inr h53 =>
        -- Conjunctions on the left can always be decomposed.
        let h54 := h43.left
        let h55 := h43.right
        -- Conjunctions on the left can always be decomposed.
        let h56 := h55.left
        let h57 := h55.right
        -- We want to use the implication h57 based on <expert-advice>. So we show its premise.
        have h58 : p3 := by
          -- One of the premise coincides with the conclusion.
          exact h53
        -- We have shown the premise of h57, we can now drive its conclusion.
        let h59 := h57 h58
        -- One of the premise coincides with the conclusion.
        exact h59
  case inr h60 =>
    -- Disjunctions on the left can always be decomposed.
    cases h60
    case inl h61 =>
      -- Conjunctions on the left can always be decomposed.
      let h62 := h1.left
      let h63 := h1.right
      -- Disjunctions on the left can always be decomposed.
      cases h62
      case inl h64 =>
        -- Conjunctions on the left can always be decomposed.
        let h65 := h63.left
        let h66 := h63.right
        -- Conjunctions on the left can always be decomposed.
        let h67 := h66.left
        let h68 := h66.right
        -- We want to use the implication h65 based on <expert-advice>. So we show its premise.
        have h69 : ((False ∨ p3) ∨ True) := by
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- True on the right can always be proven directly.
          apply True.intro
        -- We have shown the premise of h65, we can now drive its conclusion.
        let h70 := h65 h69
        -- We want to use the implication h68 based on <expert-advice>. So we show its premise.
        have h71 : p3 := by
          -- One of the premise coincides with the conclusion.
          exact h70
        -- We have shown the premise of h68, we can now drive its conclusion.
        let h72 := h68 h71
        -- One of the premise coincides with the conclusion.
        exact h72
      case inr h73 =>
        -- Conjunctions on the left can always be decomposed.
        let h74 := h63.left
        let h75 := h63.right
        -- Conjunctions on the left can always be decomposed.
        let h76 := h75.left
        let h77 := h75.right
        -- We want to use the implication h77 based on <expert-advice>. So we show its premise.
        have h78 : p3 := by
          -- One of the premise coincides with the conclusion.
          exact h73
        -- We have shown the premise of h77, we can now drive its conclusion.
        let h79 := h77 h78
        -- One of the premise coincides with the conclusion.
        exact h79
    case inr h80 =>
      -- Conjunctions on the left can always be decomposed.
      let h81 := h1.left
      let h82 := h1.right
      -- Disjunctions on the left can always be decomposed.
      cases h81
      case inl h83 =>
        -- Conjunctions on the left can always be decomposed.
        let h84 := h82.left
        let h85 := h82.right
        -- Conjunctions on the left can always be decomposed.
        let h86 := h85.left
        let h87 := h85.right
        -- We want to use the implication h84 based on <expert-advice>. So we show its premise.
        have h88 : ((False ∨ p3) ∨ True) := by
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- True on the right can always be proven directly.
          apply True.intro
        -- We have shown the premise of h84, we can now drive its conclusion.
        let h89 := h84 h88
        -- We want to use the implication h87 based on <expert-advice>. So we show its premise.
        have h90 : p3 := by
          -- One of the premise coincides with the conclusion.
          exact h89
        -- We have shown the premise of h87, we can now drive its conclusion.
        let h91 := h87 h90
        -- One of the premise coincides with the conclusion.
        exact h91
      case inr h92 =>
        -- Conjunctions on the left can always be decomposed.
        let h93 := h82.left
        let h94 := h82.right
        -- Conjunctions on the left can always be decomposed.
        let h95 := h94.left
        let h96 := h94.right
        -- We want to use the implication h96 based on <expert-advice>. So we show its premise.
        have h97 : p3 := by
          -- One of the premise coincides with the conclusion.
          exact h92
        -- We have shown the premise of h96, we can now drive its conclusion.
        let h98 := h96 h97
        -- One of the premise coincides with the conclusion.
        exact h98



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_337116742664804430803639350664 : (p1 → (((True ∨ True) → (((p3 ∧ ((p2 ∨ False) → (p5 ∨ ((True → p2) → (p3 ∧ ((p4 ∧ p3) ∧ p3)))))) ∧ p5) → False)) ∨ (p1 ∧ p1))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- One of the premise coincides with the conclusion.
  exact h1
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_318495644159837600419957591405 : (p4 ∨ ((((True ∧ p2) ∧ p3) ∨ (p3 → (p4 ∨ (p5 → ((True ∧ p2) ∨ ((((True ∧ True) → p5) → p3) ∨ (p4 ∨ p1))))))) ∧ (False → p2))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
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
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h3
  -- One of the premise coincides with the conclusion.
  exact h1
  -- Implications on the right can always be decomposed.
  intro h4
  -- False on the left can always be used.
  apply False.elim h4



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_349001989112399167544157814502 : (p3 → (p4 ∨ ((False → (p5 → True)) → ((((p5 → p3) ∧ True) → (p1 ∧ p4)) → ((p2 → p4) ∨ (p3 → (((p4 → True) ∧ True) ∨ True))))))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h2
  -- Implications on the right can always be decomposed.
  intro h3
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h4
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_53495756423417319556521948496 : (((False ∨ (((p3 ∨ p1) ∧ ((p4 → False) → False)) ∧ (False → p5))) → (((False ∨ (p4 → p5)) → (p5 ∧ ((p5 ∧ p4) → p3))) ∨ True)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_117479310357301359078716264650 : ((p1 ∧ (p1 ∨ ((((p2 → ((p2 ∨ p2) ∨ (p1 ∧ p4))) ∨ p3) → ((p5 → (p4 ∧ p2)) ∧ p3)) → ((p5 ∨ p4) ∨ False)))) ∨ (p3 → True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_657167721487947159627120934356 : (((((p5 ∨ (p5 ∨ p5)) ∨ (p4 ∨ ((p4 → ((((p2 ∨ p5) ∧ p3) → (p4 → (False ∧ p4))) → (False → p3))) ∧ p2))) ∨ (True ∨ False)) ∨ p2) ∧ True) := by
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
theorem thm_5_vars_218277907948542533808000837226 : (((p2 ∨ p4) ∨ (p3 ∧ p2)) → ((p2 ∧ (p4 → ((False ∧ False) → True))) → ((((((p4 → p4) ∨ p2) → p1) ∧ p4) ∧ True) ∨ (p2 ∨ p1)))) := by
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
    -- Disjunctions on the left can always be decomposed.
    cases h5
    case inl h6 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- One of the premise coincides with the conclusion.
      exact h6
    case inr h7 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- One of the premise coincides with the conclusion.
      exact h3
  case inr h8 =>
    -- Conjunctions on the left can always be decomposed.
    let h9 := h8.left
    let h10 := h8.right
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- One of the premise coincides with the conclusion.
    exact h10



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_113727940735363808584936016938 : ((((((p5 ∧ ((p4 → p5) ∨ True)) ∨ (False → p1)) → ((p4 ∨ p5) ∧ (p5 → p4))) ∨ ((p3 → p3) ∨ p2)) → (p3 ∧ p1)) ∨ (p4 ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_199105352577775413650619693724 : ((((p5 → (p5 ∧ p5)) ∧ (False → p3)) ∧ p1) → ((((p2 ∨ p3) ∧ ((p1 → False) ∧ p1)) ∧ p3) ∨ (((p1 ∧ p3) ∨ (p5 ∧ p5)) ∨ True))) := by
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
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_62584454588925135730615549896 : ((p3 ∧ (p2 → (((p2 ∨ p4) → (False → ((p3 → p2) → (p4 ∨ ((p1 → p1) ∨ (p3 ∨ (((False → p5) → False) → p2))))))) → False))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_133956951319081290038757879622 : (((p3 → (((True ∧ (False → ((p2 ∧ (p4 ∨ True)) → p5))) → (p1 → True)) → ((False ∧ (p4 ∨ p3)) ∧ False))) ∧ p4) ∨ ((False ∧ p3) → False)) := by
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
theorem thm_5_vars_308726867705306984830141637770 : (p2 ∨ ((p1 → (((((p2 ∨ p1) ∨ p1) → (((p5 → p5) → p2) → p1)) → p5) ∨ (False ∨ ((p2 ∧ False) ∧ ((True → p1) → p4))))) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_350111615070279595689905576827 : (p4 → ((((p5 ∨ (p5 ∨ p3)) ∨ (((p5 ∧ (p2 → ((True ∧ p3) → False))) ∧ (p3 ∧ p5)) ∨ p1)) ∨ ((False ∨ (p1 ∨ True)) → True)) ∨ p5)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h2
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_137317286638165437621731334610 : ((p2 ∧ ((p4 ∧ (False → (False ∨ True))) ∨ (p1 ∧ (((p4 → (p3 ∨ (p4 ∨ (p2 ∨ p4)))) → (True ∧ p4)) ∨ False)))) ∨ (p1 ∨ (p3 → True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_784578288250009566698033780264 : (((p3 ∨ (p1 ∨ ((p1 ∧ (((p5 → True) ∧ (p4 ∧ True)) ∧ (((p4 ∨ p4) ∨ False) ∧ p1))) → ((p5 ∨ ((False ∨ p1) ∨ p2)) ∨ p2)))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_173086896821512344840811097389 : ((p1 ∨ ((((True → (False → False)) ∧ (p1 ∨ p1)) ∧ p1) ∨ (True ∧ (p1 ∨ True)))) ∨ (((True ∧ False) ∨ (p2 → p1)) ∨ ((p1 ∧ p3) → p2))) := by
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
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_322349984470285948583150906134 : (p5 ∨ ((((p4 ∨ ((((((p2 → False) ∧ p2) ∨ (True ∧ p5)) → p5) ∨ p2) → p2)) ∨ (True ∧ (p4 ∨ False))) ∧ (p1 ∧ (True → p3))) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_323525233998092556762088686836 : (p5 ∨ ((p4 ∨ ((p2 → ((((p3 → ((True → ((False ∨ (p2 ∧ p4)) → p5)) ∧ False)) ∧ p5) ∧ False) ∧ False)) ∨ p3)) ∨ (True ∨ (False → p3)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_172260732351037817898052339268 : (((((p2 → p2) → (p4 ∧ (p5 ∧ p1))) ∧ p2) ∨ ((p3 ∨ (p1 ∨ p5)) ∧ True)) ∨ (p3 → ((((p5 → (p1 ∧ False)) → True) ∨ p2) ∨ p3))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_454905489773751812702005209719 : ((((p3 ∨ (p1 ∧ (((p5 ∨ p1) ∧ (((False → p1) → (p3 ∨ False)) ∨ p1)) → (p3 ∨ (p3 ∨ p3))))) → ((p1 ∨ (True ∧ p5)) → p3)) ∧ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
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
      -- One of the premise coincides with the conclusion.
      exact h4
    case inr h5 =>
      -- Conjunctions on the left can always be decomposed.
      let h6 := h5.left
      let h7 := h5.right
      -- We want to use the implication h7 based on <expert-advice>. So we show its premise.
      have h8 : ((p5 ∨ p1) ∧ (((False → p1) → (p3 ∨ False)) ∨ p1)) := by
        -- Conjunctions on the right can always be decomposed.
        apply And.intro
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- One of the premise coincides with the conclusion.
        exact h6
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- One of the premise coincides with the conclusion.
        exact h6
      -- We have shown the premise of h7, we can now drive its conclusion.
      let h9 := h7 h8
      -- Disjunctions on the left can always be decomposed.
      cases h9
      case inl h10 =>
        -- One of the premise coincides with the conclusion.
        exact h10
      case inr h11 =>
        -- Disjunctions on the left can always be decomposed.
        cases h11
        case inl h12 =>
          -- One of the premise coincides with the conclusion.
          exact h12
        case inr h13 =>
          -- One of the premise coincides with the conclusion.
          exact h13
  case inr h14 =>
    -- Conjunctions on the left can always be decomposed.
    let h15 := h14.left
    let h16 := h14.right
    -- Disjunctions on the left can always be decomposed.
    cases h1
    case inl h17 =>
      -- One of the premise coincides with the conclusion.
      exact h17
    case inr h18 =>
      -- Conjunctions on the left can always be decomposed.
      let h19 := h18.left
      let h20 := h18.right
      -- We want to use the implication h20 based on <expert-advice>. So we show its premise.
      have h21 : ((p5 ∨ p1) ∧ (((False → p1) → (p3 ∨ False)) ∨ p1)) := by
        -- Conjunctions on the right can always be decomposed.
        apply And.intro
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- One of the premise coincides with the conclusion.
        exact h16
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- One of the premise coincides with the conclusion.
        exact h19
      -- We have shown the premise of h20, we can now drive its conclusion.
      let h22 := h20 h21
      -- Disjunctions on the left can always be decomposed.
      cases h22
      case inl h23 =>
        -- One of the premise coincides with the conclusion.
        exact h23
      case inr h24 =>
        -- Disjunctions on the left can always be decomposed.
        cases h24
        case inl h25 =>
          -- One of the premise coincides with the conclusion.
          exact h25
        case inr h26 =>
          -- One of the premise coincides with the conclusion.
          exact h26
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_259382688657442596508164622195 : ((False → p3) → (((((((p2 ∧ (False ∨ p3)) ∧ p1) → ((p1 ∨ (p1 ∨ (p4 ∧ p1))) ∨ True)) → p5) ∨ (p3 → p3)) → p2) ∨ (p3 → True))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h2
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_669688612932696005654962646739 : (((((True ∧ ((((p1 ∧ ((True → p4) ∧ p4)) → ((p5 ∧ p3) ∨ p5)) ∨ False) ∧ p4)) → (p5 ∨ (False ∨ p5))) ∨ ((p1 → p1) ∨ p1)) ∨ p5) ∧ True) := by
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
  -- One of the premise coincides with the conclusion.
  exact h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_117199131884245224164618330561 : ((True ∧ (((False ∧ ((True ∨ (((False ∨ True) → p4) ∨ True)) ∧ p3)) ∧ False) ∨ ((((True → p1) ∧ p3) ∧ p2) ∨ (p3 → True)))) ∨ (p5 ∧ False)) := by
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
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_110798445546369005500007125551 : (((((p2 ∧ ((((p4 → p5) ∨ p5) ∧ (p2 → (p2 ∧ ((p2 ∧ p3) ∨ p2)))) ∧ (p3 ∧ p4))) ∨ (p2 ∧ p2)) ∨ p2) ∧ p3) ∨ (True ∨ False)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_632714259893749796418269867344 : (((((p5 → (((p5 ∧ ((p4 ∧ False) ∨ (False ∨ (p5 ∧ p2)))) ∧ ((((p4 → p1) ∧ False) ∧ False) ∧ p2)) ∨ (p1 → p3))) → p3) → p5) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_195517330059569533150578115925 : ((((p5 → p5) ∧ False) → (p5 ∧ (p4 → p4))) ∧ ((((p5 ∧ p3) ∧ p4) → p5) → (((p1 → ((p2 ∧ (p5 ∨ False)) ∧ p3)) ∧ p3) ∨ True))) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- False on the left can always be used.
  apply False.elim h3
  -- Implications on the right can always be decomposed.
  intro h4
  -- Conjunctions on the left can always be decomposed.
  let h5 := h1.left
  let h6 := h1.right
  -- False on the left can always be used.
  apply False.elim h6
  -- Implications on the right can always be decomposed.
  intro h7
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_691221281572599314739673886541 : (((((False ∨ (p3 ∨ ((False → p5) → p3))) → ((p1 ∨ (True → (True ∨ p2))) ∨ p4)) → (p3 → (p2 ∧ ((p4 ∨ True) ∨ (p2 ∨ p3))))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_193726158152692964149565423765 : ((p2 ∧ ((p3 → p4) ∨ (p5 ∨ (p5 → (p3 → p4))))) → (p1 ∨ (p3 → ((p1 ∧ True) ∨ (p5 → ((p4 ∨ p5) ∧ ((p2 ∨ p5) ∨ p2))))))) := by
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
    -- Implications on the right can always be decomposed.
    intro h5
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h6
    -- Conjunctions on the right can always be decomposed.
    apply And.intro
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h6
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h2
  case inr h7 =>
    -- Disjunctions on the left can always be decomposed.
    cases h7
    case inl h8 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Implications on the right can always be decomposed.
      intro h9
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Implications on the right can always be decomposed.
      intro h10
      -- Conjunctions on the right can always be decomposed.
      apply And.intro
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- One of the premise coincides with the conclusion.
      exact h10
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- One of the premise coincides with the conclusion.
      exact h2
    case inr h11 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Implications on the right can always be decomposed.
      intro h12
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Implications on the right can always be decomposed.
      intro h13
      -- Conjunctions on the right can always be decomposed.
      apply And.intro
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- One of the premise coincides with the conclusion.
      exact h13
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- One of the premise coincides with the conclusion.
      exact h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_113497470382934605202785463373 : ((((p1 ∧ (((p4 ∧ p4) ∨ p4) → ((p1 → ((p5 ∨ False) ∧ (p5 ∨ True))) ∧ p2))) ∨ ((False ∧ p3) → p2)) ∨ (p5 ∨ p5)) ∨ (p1 ∨ p4)) := by
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
  -- False on the left can always be used.
  apply False.elim h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_111891812252688253203304400634 : (((((p5 ∨ ((p4 → ((p5 → (p2 ∨ p4)) ∧ True)) ∨ (p2 → False))) ∧ p2) ∨ (p5 ∨ (p3 ∨ ((False ∨ False) → p3)))) ∨ p3) ∨ (True ∨ False)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_229551767167908626388621165110 : ((p2 → (p1 → p3)) ∨ (p1 ∨ ((p3 ∧ ((((p4 ∨ (False ∧ p5)) → p4) → p4) ∧ ((p1 → p4) → (True ∧ p3)))) → (p4 ∨ (p3 ∧ p2))))) := by
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
  let h4 := h3.left
  let h5 := h3.right
  -- We want to use the implication h4 based on <expert-advice>. So we show its premise.
  have h6 : ((p4 ∨ (False ∧ p5)) → p4) := by
    -- Implications on the right can always be decomposed.
    intro h7
    -- Disjunctions on the left can always be decomposed.
    cases h7
    case inl h8 =>
      -- One of the premise coincides with the conclusion.
      exact h8
    case inr h9 =>
      -- Conjunctions on the left can always be decomposed.
      let h10 := h9.left
      let h11 := h9.right
      -- False on the left can always be used.
      apply False.elim h10
  -- We have shown the premise of h4, we can now drive its conclusion.
  let h12 := h4 h6
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- One of the premise coincides with the conclusion.
  exact h12



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_64665351124530717024957122588 : ((p1 ∨ (p1 ∨ (((p2 ∧ (p2 → ((p2 ∧ (p4 ∧ p5)) ∨ (((((p1 ∨ p1) → p2) ∧ p5) → p3) ∨ p1)))) → p4) ∨ (p4 ∧ p1)))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_314932637036001406093820448394 : (p3 ∨ ((p2 ∧ ((p4 ∨ p3) ∧ ((p4 → (True ∨ p5)) → False))) ∨ ((True ∨ ((False ∨ p5) ∧ p1)) → (p2 → ((p4 → True) → (False → p2)))))) := by
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
  -- False on the left can always be used.
  apply False.elim h4



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_460086985619365736206913070894 : (((((p5 ∨ p1) ∨ ((p1 ∧ (p2 ∧ (((((p5 ∧ p2) ∧ p4) → p5) ∧ p5) → p1))) ∨ p1)) → (p5 ∨ (((True ∧ p5) → p2) ∨ p1))) ∧ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
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
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- One of the premise coincides with the conclusion.
      exact h3
    case inr h4 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- One of the premise coincides with the conclusion.
      exact h4
  case inr h5 =>
    -- Disjunctions on the left can always be decomposed.
    cases h5
    case inl h6 =>
      -- Conjunctions on the left can always be decomposed.
      let h7 := h6.left
      let h8 := h6.right
      -- Conjunctions on the left can always be decomposed.
      let h9 := h8.left
      let h10 := h8.right
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- One of the premise coincides with the conclusion.
      exact h7
    case inr h11 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- One of the premise coincides with the conclusion.
      exact h11
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_613660729059062694399744908834 : ((((((((p3 ∧ (p3 → ((p3 ∨ p2) → True))) ∨ p3) → p4) ∧ (((p3 ∧ (p1 ∨ p5)) ∧ p5) ∨ p2)) ∧ (False ∨ (p4 → p4))) ∨ False) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_171562428390748533657611846486 : ((((p3 ∨ ((p4 ∨ p5) ∧ ((True → p3) ∨ (True → (p3 ∨ p4))))) → False) ∨ p4) ∨ ((True ∨ (p5 ∧ False)) ∧ (True ∨ (p2 ∨ (p5 → p4))))) := by
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
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_255112160267220162707338757142 : ((p4 ∧ p2) → (p5 → ((p3 ∨ (True → (False ∨ (p3 → (p5 ∧ ((True ∨ ((False ∨ p1) ∧ p2)) ∧ ((True → (p4 ∨ True)) ∧ p1))))))) ∨ True))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Conjunctions on the left can always be decomposed.
  let h3 := h1.left
  let h4 := h1.right
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_259453633496493554063460896351 : ((False → p4) → ((p1 ∨ ((((p5 ∧ False) ∨ (p5 ∧ True)) ∧ (p3 ∨ True)) ∧ (p3 ∨ p5))) → (((((p1 ∧ False) ∨ p5) ∨ p4) ∨ True) ∨ p4))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Disjunctions on the left can always be decomposed.
  cases h2
  case inl h3 =>
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro
  case inr h4 =>
    -- Conjunctions on the left can always be decomposed.
    let h5 := h4.left
    let h6 := h4.right
    -- Conjunctions on the left can always be decomposed.
    let h7 := h5.left
    let h8 := h5.right
    -- Disjunctions on the left can always be decomposed.
    cases h7
    case inl h9 =>
      -- Conjunctions on the left can always be decomposed.
      let h10 := h9.left
      let h11 := h9.right
      -- False on the left can always be used.
      apply False.elim h11
    case inr h12 =>
      -- Conjunctions on the left can always be decomposed.
      let h13 := h12.left
      let h14 := h12.right
      -- Disjunctions on the left can always be decomposed.
      cases h8
      case inl h15 =>
        -- Disjunctions on the left can always be decomposed.
        cases h6
        case inl h16 =>
          -- Show the left disjunct based on <expert-advice>.
          apply Or.inl
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- True on the right can always be proven directly.
          apply True.intro
        case inr h17 =>
          -- Show the left disjunct based on <expert-advice>.
          apply Or.inl
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- True on the right can always be proven directly.
          apply True.intro
      case inr h18 =>
        -- Disjunctions on the left can always be decomposed.
        cases h6
        case inl h19 =>
          -- Show the left disjunct based on <expert-advice>.
          apply Or.inl
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- True on the right can always be proven directly.
          apply True.intro
        case inr h20 =>
          -- Show the left disjunct based on <expert-advice>.
          apply Or.inl
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- True on the right can always be proven directly.
          apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_112240749824494983805737022422 : (((p3 ∨ ((p1 ∨ (p3 ∨ ((p4 ∧ p1) ∨ ((p1 ∧ p2) → (((p2 ∧ p2) → False) → (True ∧ (p5 ∧ p2))))))) ∨ p3)) ∨ p3) ∨ (False → p1)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_610883110464000646745009445664 : ((((((p5 → ((True ∨ (p5 → (p2 ∧ p3))) ∧ (p2 ∨ (False ∧ p5)))) ∧ (((p3 ∨ (p5 → (p4 ∨ p2))) → p2) ∨ p2)) → p2) ∨ True) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_114963772497156119724923502598 : (((True → ((((((p4 ∨ p1) ∨ False) → (False ∨ p2)) ∧ p4) ∧ p2) ∧ p1)) → ((p4 ∨ p4) ∨ (((p5 ∨ p2) ∨ p3) → p3))) ∨ (p5 ∧ p5)) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h2 : True := by
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h3 := h1 h2
  -- We need to get the left conjuct of h3 based on <expert-advice>.
  let h4 := h3.left
  -- We need to get the left conjuct of h4 based on <expert-advice>.
  let h5 := h4.left
  -- We need to get the right conjuct of h5 based on <expert-advice>.
  let h6 := h5.right
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- One of the premise coincides with the conclusion.
  exact h6



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_88820742993285615723568910000 : ((((True ∧ p2) → (p3 ∨ p2)) → ((((p5 ∧ (p4 ∧ (((p1 → (p5 → p4)) ∧ (False ∨ p4)) ∧ p5))) ∨ (True ∨ p4)) ∧ p2) ∧ p3)) → p2) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h2 : ((True ∧ p2) → (p3 ∨ p2)) := by
    -- Implications on the right can always be decomposed.
    intro h3
    -- Conjunctions on the left can always be decomposed.
    let h4 := h3.left
    let h5 := h3.right
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h5
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h6 := h1 h2
  -- We need to get the left conjuct of h6 based on <expert-advice>.
  let h7 := h6.left
  -- We need to get the right conjuct of h7 based on <expert-advice>.
  let h8 := h7.right
  -- One of the premise coincides with the conclusion.
  exact h8



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_114045281181431616501224394968 : ((((p3 → (p5 ∧ (((p3 ∨ False) ∧ ((p1 → (True → p3)) ∨ p1)) → (p2 ∨ p5)))) ∨ (p4 ∧ p1)) ∨ (False → (p2 → p2))) ∨ (p4 ∧ p4)) := by
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



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_118707406147078255965445682676 : ((p5 ∨ (((False ∧ (p3 ∨ p3)) → (((p2 → (False ∨ p4)) ∧ (p3 ∧ p5)) ∨ (False ∧ (((p1 ∨ p2) ∧ p3) → p1)))) → p1)) ∨ (False → p1)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_254210026386312973907399071333 : ((p2 ∧ p2) → ((((((True ∧ True) → p1) ∨ ((p5 ∨ p3) ∧ (p1 ∧ True))) ∨ (p5 ∧ True)) ∨ (p1 ∧ (p4 ∨ ((True ∧ p5) ∧ True)))) ∨ p2)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h3



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_259313121949057648175337923135 : ((False → p2) → ((p2 ∧ (True ∧ ((((p2 → True) ∨ p4) → ((((p4 ∧ p2) ∨ True) ∨ True) ∧ p2)) → ((p5 ∨ p5) ∧ (p1 ∧ p4))))) ∨ True)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_57189507527342537417023374316 : ((((p2 ∨ p1) ∨ p1) ∨ (((((False ∨ p1) → p5) ∨ p5) ∧ (p5 ∧ (((p4 ∨ (p1 ∨ p2)) → False) ∨ (False ∨ (False → p5))))) → p2)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_353459421085118099760052137932 : (p4 → (p1 ∨ (True → ((p1 ∧ (p1 ∧ False)) ∨ ((((p3 ∨ (p1 ∨ (p3 ∨ (p5 ∨ (p1 → True))))) ∨ False) ∧ ((True ∨ p1) ∨ False)) ∨ p5))))) := by
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
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h3
  -- True on the right can always be proven directly.
  apply True.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_614919888924257471557945995899 : ((((((((p2 ∧ (True ∧ ((((p3 ∧ p1) → (p3 ∨ False)) → False) ∨ True))) ∨ p4) → False) → p4) → (((p2 → p5) ∨ p3) ∧ p3)) ∨ True) ∨ p2) ∧ True) := by
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
theorem thm_5_vars_207457464125029457476431075238 : (((p5 ∨ (p1 ∨ (p1 ∧ p1))) ∨ p4) → ((p5 ∨ (p4 ∧ (True → False))) → (True → (p1 ∨ ((p5 → ((p1 ∧ p2) ∧ (p3 ∨ p4))) → p1))))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Implications on the right can always be decomposed.
  intro h3
  -- Disjunctions on the left can always be decomposed.
  cases h2
  case inl h4 =>
    -- Disjunctions on the left can always be decomposed.
    cases h1
    case inl h5 =>
      -- Disjunctions on the left can always be decomposed.
      cases h5
      case inl h6 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- Implications on the right can always be decomposed.
        intro h7
        -- We want to use the implication h7 based on <expert-advice>. So we show its premise.
        have h8 : p5 := by
          -- One of the premise coincides with the conclusion.
          exact h6
        -- We have shown the premise of h7, we can now drive its conclusion.
        let h9 := h7 h8
        -- We need to get the left conjuct of h9 based on <expert-advice>.
        let h10 := h9.left
        -- We need to get the left conjuct of h10 based on <expert-advice>.
        let h11 := h10.left
        -- One of the premise coincides with the conclusion.
        exact h11
      case inr h12 =>
        -- Disjunctions on the left can always be decomposed.
        cases h12
        case inl h13 =>
          -- Show the left disjunct based on <expert-advice>.
          apply Or.inl
          -- One of the premise coincides with the conclusion.
          exact h13
        case inr h14 =>
          -- Conjunctions on the left can always be decomposed.
          let h15 := h14.left
          let h16 := h14.right
          -- Show the left disjunct based on <expert-advice>.
          apply Or.inl
          -- One of the premise coincides with the conclusion.
          exact h16
    case inr h17 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Implications on the right can always be decomposed.
      intro h18
      -- We want to use the implication h18 based on <expert-advice>. So we show its premise.
      have h19 : p5 := by
        -- One of the premise coincides with the conclusion.
        exact h4
      -- We have shown the premise of h18, we can now drive its conclusion.
      let h20 := h18 h19
      -- We need to get the left conjuct of h20 based on <expert-advice>.
      let h21 := h20.left
      -- We need to get the left conjuct of h21 based on <expert-advice>.
      let h22 := h21.left
      -- One of the premise coincides with the conclusion.
      exact h22
  case inr h23 =>
    -- Conjunctions on the left can always be decomposed.
    let h24 := h23.left
    let h25 := h23.right
    -- Disjunctions on the left can always be decomposed.
    cases h1
    case inl h26 =>
      -- Disjunctions on the left can always be decomposed.
      cases h26
      case inl h27 =>
        -- We want to use the implication h25 based on <expert-advice>. So we show its premise.
        have h28 : True := by
          -- True on the right can always be proven directly.
          apply True.intro
        -- We have shown the premise of h25, we can now drive its conclusion.
        let h29 := h25 h28
        -- False on the left can always be used.
        apply False.elim h29
      case inr h30 =>
        -- Disjunctions on the left can always be decomposed.
        cases h30
        case inl h31 =>
          -- Show the left disjunct based on <expert-advice>.
          apply Or.inl
          -- One of the premise coincides with the conclusion.
          exact h31
        case inr h32 =>
          -- Conjunctions on the left can always be decomposed.
          let h33 := h32.left
          let h34 := h32.right
          -- Show the left disjunct based on <expert-advice>.
          apply Or.inl
          -- One of the premise coincides with the conclusion.
          exact h34
    case inr h35 =>
      -- We want to use the implication h25 based on <expert-advice>. So we show its premise.
      have h36 : True := by
        -- True on the right can always be proven directly.
        apply True.intro
      -- We have shown the premise of h25, we can now drive its conclusion.
      let h37 := h25 h36
      -- False on the left can always be used.
      apply False.elim h37



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_39876429150697132736662576020 : (((p2 → ((((True ∨ ((p3 ∨ (False → (p5 → (False ∧ False)))) ∨ (False ∧ p5))) → (p4 ∨ (p5 ∨ p5))) ∨ p2) ∨ (p3 ∨ p4))) ∧ False) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_314836427023766441258040228055 : (p3 ∨ ((((True ∧ (False → False)) ∧ p5) ∨ (((p2 → p4) ∧ p4) → p2)) ∨ (True ∨ (((p1 ∧ (p5 ∨ (p3 ∧ p5))) ∨ (p5 → p5)) ∨ p3)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_190168477045841301863307428620 : (((p2 ∧ (((p2 ∨ (p5 → p3)) ∨ p1) ∨ p4)) ∧ p2) ∨ ((p5 → (((p4 ∧ p4) ∧ ((p4 ∨ (p1 ∧ p1)) → p1)) ∨ p5)) ∧ (p1 ∨ True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_351911750913868412240669773600 : (p4 → ((((True ∨ p4) → p3) → (((True ∨ False) ∨ p3) → p2)) ∨ (p3 → (p5 ∨ (((p2 ∧ (p3 ∧ p2)) ∨ (p1 ∧ (p3 ∨ p1))) ∨ p4))))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h2
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_319793964178747567133169204801 : (p4 ∨ ((p5 ∧ (True ∧ ((True ∨ True) ∧ p4))) → ((True ∨ (False → True)) → (((p2 → (p4 → (p4 ∧ ((True ∧ p3) ∨ True)))) ∧ p5) ∨ False)))) := by
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
    let h4 := h1.left
    let h5 := h1.right
    -- Conjunctions on the left can always be decomposed.
    let h6 := h5.left
    let h7 := h5.right
    -- Conjunctions on the left can always be decomposed.
    let h8 := h7.left
    let h9 := h7.right
    -- Disjunctions on the left can always be decomposed.
    cases h8
    case inl h10 =>
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- Conjunctions on the right can always be decomposed.
      apply And.intro
      -- Implications on the right can always be decomposed.
      intro h11
      -- Implications on the right can always be decomposed.
      intro h12
      -- Conjunctions on the right can always be decomposed.
      apply And.intro
      -- One of the premise coincides with the conclusion.
      exact h12
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- True on the right can always be proven directly.
      apply True.intro
      -- One of the premise coincides with the conclusion.
      exact h4
    case inr h13 =>
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- Conjunctions on the right can always be decomposed.
      apply And.intro
      -- Implications on the right can always be decomposed.
      intro h14
      -- Implications on the right can always be decomposed.
      intro h15
      -- Conjunctions on the right can always be decomposed.
      apply And.intro
      -- One of the premise coincides with the conclusion.
      exact h15
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- True on the right can always be proven directly.
      apply True.intro
      -- One of the premise coincides with the conclusion.
      exact h4
  case inr h16 =>
    -- Conjunctions on the left can always be decomposed.
    let h17 := h1.left
    let h18 := h1.right
    -- Conjunctions on the left can always be decomposed.
    let h19 := h18.left
    let h20 := h18.right
    -- Conjunctions on the left can always be decomposed.
    let h21 := h20.left
    let h22 := h20.right
    -- Disjunctions on the left can always be decomposed.
    cases h21
    case inl h23 =>
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- Conjunctions on the right can always be decomposed.
      apply And.intro
      -- Implications on the right can always be decomposed.
      intro h24
      -- Implications on the right can always be decomposed.
      intro h25
      -- Conjunctions on the right can always be decomposed.
      apply And.intro
      -- One of the premise coincides with the conclusion.
      exact h25
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- True on the right can always be proven directly.
      apply True.intro
      -- One of the premise coincides with the conclusion.
      exact h17
    case inr h26 =>
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- Conjunctions on the right can always be decomposed.
      apply And.intro
      -- Implications on the right can always be decomposed.
      intro h27
      -- Implications on the right can always be decomposed.
      intro h28
      -- Conjunctions on the right can always be decomposed.
      apply And.intro
      -- One of the premise coincides with the conclusion.
      exact h28
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- True on the right can always be proven directly.
      apply True.intro
      -- One of the premise coincides with the conclusion.
      exact h17



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_673209304135093063288076121149 : (((((((((p2 → True) → (p5 ∧ False)) ∧ False) ∧ p5) ∨ p3) → (True → (p1 ∧ ((False → (p1 ∨ p4)) ∧ False)))) → ((p1 ∧ False) ∧ p3)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_59175556801863625422055059891 : (((False ∨ p5) ∨ ((((p1 ∧ False) ∨ (p3 ∨ ((p1 ∧ (p2 ∨ (p2 ∨ (((p2 → p3) ∨ p1) ∧ p3)))) ∧ (p2 ∧ p1)))) → False) ∧ p1)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_34965261455578750745094978906 : ((p1 → (((((p2 ∧ ((p1 → p3) → (p5 → True))) ∨ p3) ∧ ((((p2 ∨ p5) → p5) → (p5 → False)) ∧ (p3 ∨ p5))) ∨ True) ∨ p2)) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
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
theorem thm_5_vars_194009664905428560810131155394 : ((p4 ∨ ((True ∧ ((p3 ∧ p3) ∨ False)) ∧ (p5 ∨ p2))) → (p5 ∨ (p5 → (p1 ∨ ((p3 → ((p1 ∨ p5) → p4)) → ((p5 → p4) ∨ True)))))) := by
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
    -- Implications on the right can always be decomposed.
    intro h4
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
    -- Disjunctions on the left can always be decomposed.
    cases h9
    case inl h10 =>
      -- Conjunctions on the left can always be decomposed.
      let h11 := h10.left
      let h12 := h10.right
      -- Disjunctions on the left can always be decomposed.
      cases h7
      case inl h13 =>
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- One of the premise coincides with the conclusion.
        exact h13
      case inr h14 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- Implications on the right can always be decomposed.
        intro h15
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- Implications on the right can always be decomposed.
        intro h16
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- True on the right can always be proven directly.
        apply True.intro
    case inr h17 =>
      -- False on the left can always be used.
      apply False.elim h17



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_41217474894755231070912729060 : (((((((p1 → (((p4 ∨ p2) → p2) ∧ p4)) ∨ (p1 ∨ (p3 → True))) ∧ (True → p4)) → p1) ∧ (p2 ∨ (p1 ∨ (p5 ∧ p2)))) ∨ p4) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



