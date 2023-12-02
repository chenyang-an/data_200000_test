variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_257412971566355251384285739982 : ((p2 ∨ p5) → (p3 ∨ ((((p2 ∧ p3) → p3) ∨ p5) ∧ (((False ∨ p2) ∧ (((p5 ∨ p3) ∨ p2) ∨ (True ∨ (p2 → (p1 ∧ p2))))) ∨ True)))) := by
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
    -- Implications on the right can always be decomposed.
    intro h3
    -- Conjunctions on the left can always be decomposed.
    let h4 := h3.left
    let h5 := h3.right
    -- One of the premise coincides with the conclusion.
    exact h5
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro
  case inr h6 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Conjunctions on the right can always be decomposed.
    apply And.intro
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h6
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_53631766668489690588046172411 : ((((p3 ∧ ((False ∨ p1) ∨ p3)) ∨ (p2 ∨ (p5 ∨ p4))) ∧ ((True ∧ (p2 → (p5 ∧ ((p1 ∧ (p4 → (p4 ∧ p3))) ∧ True)))) ∧ False)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_58826467298065925328426007503 : (((p5 → p5) ∧ (p1 → ((p5 ∧ p1) ∨ ((((p5 → p2) ∧ ((p2 ∧ p1) ∨ (p3 ∨ p3))) ∨ p3) ∨ ((p5 ∧ False) ∨ (p4 → p1)))))) ∨ p1) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h1
  -- One of the premise coincides with the conclusion.
  exact h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h3
  -- One of the premise coincides with the conclusion.
  exact h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_355471341578636896352692952965 : (p5 → (((((p3 ∧ (p1 ∧ p3)) ∨ True) ∨ p5) ∧ ((p2 ∧ ((((p4 ∧ p1) → p1) ∨ p5) ∧ False)) ∨ ((True ∧ p2) ∨ True))) ∧ (True ∧ True))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h1
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
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_337678833763978289352100171827 : (p1 → ((p4 ∨ (((p5 ∧ ((False ∨ (False ∧ (p4 → False))) ∨ p1)) ∧ p4) ∨ (True ∧ (p2 → False)))) ∨ ((((p4 ∧ p3) → p2) ∨ p1) ∨ True))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_138292815931447131277004131553 : ((p3 → (((p4 ∧ True) ∨ (((((p4 ∧ p5) → (p3 ∧ (p3 ∧ p3))) → (p2 → p4)) ∧ False) ∧ p3)) ∨ (True ∨ p3))) ∨ (False ∧ (False ∨ p4))) := by
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



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_740326307530463558124178823018 : ((((p1 ∨ p1) ∨ ((p4 → (((p3 ∧ ((p1 ∧ True) ∨ (False ∨ (p2 ∨ (True ∨ p1))))) ∧ p3) ∧ p5)) ∨ (((p2 ∨ p2) ∧ p2) → p2))) ∨ p2) ∧ True) := by
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
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_476621972677056080203002789717 : (((((p4 ∨ p2) → ((True ∧ p2) ∧ ((p2 ∨ p1) ∨ p4))) ∨ ((False ∧ ((True → ((p4 ∧ ((p3 ∧ p1) ∨ p5)) ∧ p1)) ∧ p2)) ∨ True)) ∧ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
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
theorem thm_5_vars_613859672190546369491298342185 : (((((((((p4 ∨ (True ∨ (((p2 ∨ (p2 ∧ True)) → False) → p5))) → p2) → (p3 ∧ p5)) ∨ p5) ∨ p3) ∨ ((p1 ∧ p4) ∨ p2)) ∨ True) ∨ p5) ∧ True) := by
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
theorem thm_5_vars_748859829669896389952471480992 : ((((p4 → p1) → ((((True → ((p2 → p4) ∧ ((p5 ∨ True) ∧ p2))) → (((True ∧ p4) ∧ False) ∨ False)) ∨ (p1 → (p1 → False))) → False)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_205161849310892950921730467857 : (((p3 ∧ (False ∨ p3)) ∧ (p5 ∨ p1)) ∨ (p5 → (True ∨ (((p2 ∨ p2) ∨ ((p4 ∧ p4) ∧ (True ∧ (p3 ∨ ((True ∧ p3) → False))))) → p2)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_877817253938664613186692846676 : (((((p2 ∨ (p4 ∨ p2)) ∧ ((p2 ∧ (p2 → (True → (((p4 ∧ (p1 ∨ False)) → p3) ∧ (p3 ∧ (p1 ∧ p4)))))) ∨ False)) ∧ (p1 → False)) → p3) ∧ True) := by
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
  cases h4
  case inl h6 =>
    -- Disjunctions on the left can always be decomposed.
    cases h5
    case inl h7 =>
      -- Conjunctions on the left can always be decomposed.
      let h8 := h7.left
      let h9 := h7.right
      -- We want to use the implication h9 based on <expert-advice>. So we show its premise.
      have h10 : p2 := by
        -- One of the premise coincides with the conclusion.
        exact h8
      -- We have shown the premise of h9, we can now drive its conclusion.
      let h11 := h9 h10
      -- We want to use the implication h11 based on <expert-advice>. So we show its premise.
      have h12 : True := by
        -- True on the right can always be proven directly.
        apply True.intro
      -- We have shown the premise of h11, we can now drive its conclusion.
      let h13 := h11 h12
      -- We need to get the right conjuct of h13 based on <expert-advice>.
      let h14 := h13.right
      -- We need to get the left conjuct of h14 based on <expert-advice>.
      let h15 := h14.left
      -- One of the premise coincides with the conclusion.
      exact h15
    case inr h16 =>
      -- False on the left can always be used.
      apply False.elim h16
  case inr h17 =>
    -- Disjunctions on the left can always be decomposed.
    cases h17
    case inl h18 =>
      -- Disjunctions on the left can always be decomposed.
      cases h5
      case inl h19 =>
        -- Conjunctions on the left can always be decomposed.
        let h20 := h19.left
        let h21 := h19.right
        -- We want to use the implication h21 based on <expert-advice>. So we show its premise.
        have h22 : p2 := by
          -- One of the premise coincides with the conclusion.
          exact h20
        -- We have shown the premise of h21, we can now drive its conclusion.
        let h23 := h21 h22
        -- We want to use the implication h23 based on <expert-advice>. So we show its premise.
        have h24 : True := by
          -- True on the right can always be proven directly.
          apply True.intro
        -- We have shown the premise of h23, we can now drive its conclusion.
        let h25 := h23 h24
        -- We need to get the right conjuct of h25 based on <expert-advice>.
        let h26 := h25.right
        -- We need to get the left conjuct of h26 based on <expert-advice>.
        let h27 := h26.left
        -- One of the premise coincides with the conclusion.
        exact h27
      case inr h28 =>
        -- False on the left can always be used.
        apply False.elim h28
    case inr h29 =>
      -- Disjunctions on the left can always be decomposed.
      cases h5
      case inl h30 =>
        -- Conjunctions on the left can always be decomposed.
        let h31 := h30.left
        let h32 := h30.right
        -- We want to use the implication h32 based on <expert-advice>. So we show its premise.
        have h33 : p2 := by
          -- One of the premise coincides with the conclusion.
          exact h31
        -- We have shown the premise of h32, we can now drive its conclusion.
        let h34 := h32 h33
        -- We want to use the implication h34 based on <expert-advice>. So we show its premise.
        have h35 : True := by
          -- True on the right can always be proven directly.
          apply True.intro
        -- We have shown the premise of h34, we can now drive its conclusion.
        let h36 := h34 h35
        -- We need to get the right conjuct of h36 based on <expert-advice>.
        let h37 := h36.right
        -- We need to get the left conjuct of h37 based on <expert-advice>.
        let h38 := h37.left
        -- One of the premise coincides with the conclusion.
        exact h38
      case inr h39 =>
        -- False on the left can always be used.
        apply False.elim h39
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_717979169636821856759221963674 : ((((((p2 ∧ p2) ∧ p3) ∨ p2) ∨ ((((p1 ∨ False) → ((((p1 → False) ∨ (p1 → True)) → True) → (p3 → p5))) ∧ (p5 → p4)) ∨ True)) ∨ False) ∧ True) := by
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
theorem thm_5_vars_205067724973128801895319667942 : (((p3 → (p3 ∧ (False ∧ False))) → p4) ∨ ((((((True ∨ p5) ∧ p4) ∨ p2) → (p4 → False)) ∨ (p2 ∧ (p4 ∧ (p2 → (p3 ∨ True))))) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_167162569273985179137764248679 : ((((p3 → (p4 ∧ p5)) → (((p2 ∧ p5) ∨ p4) ∧ ((p1 ∨ (p1 ∨ p4)) ∨ p1))) ∨ True) → (((True → (p2 → False)) ∧ True) ∨ (True ∨ True))) := by
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
theorem thm_5_vars_207082497018068354393053093968 : (((p5 ∧ ((p2 ∧ True) ∧ p1)) ∧ p3) → ((((p5 ∨ (p5 ∨ p1)) ∨ p1) ∨ p3) → (False ∨ ((False → p4) → (((p1 ∧ p5) ∧ p5) ∧ True))))) := by
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
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- Implications on the right can always be decomposed.
        intro h14
        -- Conjunctions on the right can always be decomposed.
        apply And.intro
        -- Conjunctions on the right can always be decomposed.
        apply And.intro
        -- Conjunctions on the right can always be decomposed.
        apply And.intro
        -- One of the premise coincides with the conclusion.
        exact h11
        -- One of the premise coincides with the conclusion.
        exact h8
        -- One of the premise coincides with the conclusion.
        exact h8
        -- True on the right can always be proven directly.
        apply True.intro
      case inr h15 =>
        -- Disjunctions on the left can always be decomposed.
        cases h15
        case inl h16 =>
          -- Conjunctions on the left can always be decomposed.
          let h17 := h1.left
          let h18 := h1.right
          -- Conjunctions on the left can always be decomposed.
          let h19 := h17.left
          let h20 := h17.right
          -- Conjunctions on the left can always be decomposed.
          let h21 := h20.left
          let h22 := h20.right
          -- Conjunctions on the left can always be decomposed.
          let h23 := h21.left
          let h24 := h21.right
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- Implications on the right can always be decomposed.
          intro h25
          -- Conjunctions on the right can always be decomposed.
          apply And.intro
          -- Conjunctions on the right can always be decomposed.
          apply And.intro
          -- Conjunctions on the right can always be decomposed.
          apply And.intro
          -- One of the premise coincides with the conclusion.
          exact h22
          -- One of the premise coincides with the conclusion.
          exact h19
          -- One of the premise coincides with the conclusion.
          exact h19
          -- True on the right can always be proven directly.
          apply True.intro
        case inr h26 =>
          -- Conjunctions on the left can always be decomposed.
          let h27 := h1.left
          let h28 := h1.right
          -- Conjunctions on the left can always be decomposed.
          let h29 := h27.left
          let h30 := h27.right
          -- Conjunctions on the left can always be decomposed.
          let h31 := h30.left
          let h32 := h30.right
          -- Conjunctions on the left can always be decomposed.
          let h33 := h31.left
          let h34 := h31.right
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- Implications on the right can always be decomposed.
          intro h35
          -- Conjunctions on the right can always be decomposed.
          apply And.intro
          -- Conjunctions on the right can always be decomposed.
          apply And.intro
          -- Conjunctions on the right can always be decomposed.
          apply And.intro
          -- One of the premise coincides with the conclusion.
          exact h32
          -- One of the premise coincides with the conclusion.
          exact h29
          -- One of the premise coincides with the conclusion.
          exact h29
          -- True on the right can always be proven directly.
          apply True.intro
    case inr h36 =>
      -- Conjunctions on the left can always be decomposed.
      let h37 := h1.left
      let h38 := h1.right
      -- Conjunctions on the left can always be decomposed.
      let h39 := h37.left
      let h40 := h37.right
      -- Conjunctions on the left can always be decomposed.
      let h41 := h40.left
      let h42 := h40.right
      -- Conjunctions on the left can always be decomposed.
      let h43 := h41.left
      let h44 := h41.right
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Implications on the right can always be decomposed.
      intro h45
      -- Conjunctions on the right can always be decomposed.
      apply And.intro
      -- Conjunctions on the right can always be decomposed.
      apply And.intro
      -- Conjunctions on the right can always be decomposed.
      apply And.intro
      -- One of the premise coincides with the conclusion.
      exact h42
      -- One of the premise coincides with the conclusion.
      exact h39
      -- One of the premise coincides with the conclusion.
      exact h39
      -- True on the right can always be proven directly.
      apply True.intro
  case inr h46 =>
    -- Conjunctions on the left can always be decomposed.
    let h47 := h1.left
    let h48 := h1.right
    -- Conjunctions on the left can always be decomposed.
    let h49 := h47.left
    let h50 := h47.right
    -- Conjunctions on the left can always be decomposed.
    let h51 := h50.left
    let h52 := h50.right
    -- Conjunctions on the left can always be decomposed.
    let h53 := h51.left
    let h54 := h51.right
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h55
    -- Conjunctions on the right can always be decomposed.
    apply And.intro
    -- Conjunctions on the right can always be decomposed.
    apply And.intro
    -- Conjunctions on the right can always be decomposed.
    apply And.intro
    -- One of the premise coincides with the conclusion.
    exact h52
    -- One of the premise coincides with the conclusion.
    exact h49
    -- One of the premise coincides with the conclusion.
    exact h49
    -- True on the right can always be proven directly.
    apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_350071563704091338674898082602 : (p4 → ((((False → True) → (((p2 → p4) ∧ (True → (p5 ∨ False))) ∧ (((((p1 ∧ False) ∧ p5) → True) ∨ p4) → p4))) ∨ (p5 ∨ True)) ∨ p5)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_57079576945907591280874516302 : ((((False ∧ p1) ∧ p5) ∨ (((p3 → ((False → p5) → (p5 → ((p2 ∧ p1) ∧ ((p3 ∧ (p2 → p4)) → (p5 → False)))))) ∧ False) ∧ p3)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_65456398301527673273193547763 : ((p3 ∨ ((False ∨ True) → (((p2 ∧ ((False ∧ p3) ∨ (True → p1))) ∧ ((((False ∧ (False ∧ False)) ∧ True) ∨ p4) ∧ p1)) ∨ (p2 → p2)))) ∨ p1) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h2 =>
    -- False on the left can always be used.
    apply False.elim h2
  case inr h3 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h4
    -- One of the premise coincides with the conclusion.
    exact h4



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_62484998551111389055149824750 : ((p3 ∧ ((p1 → p1) → ((p3 ∧ ((p5 ∧ True) → ((False → (p1 ∨ (False ∨ (True → p2)))) ∧ (p5 ∧ True)))) → ((True ∧ p3) → p2)))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_677449871086338325610577146379 : ((((((((p3 ∨ p5) ∨ p5) ∧ ((p3 ∨ (p5 ∧ p5)) → (p3 → False))) ∨ ((p1 → p1) ∨ p3)) ∨ p3) ∨ ((p2 ∨ p5) ∧ (p4 → True))) ∨ False) ∧ True) := by
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
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- One of the premise coincides with the conclusion.
  exact h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_50677517547492141476399658450 : ((((False ∨ (p2 ∨ (p3 ∨ True))) ∧ ((True ∧ ((p1 ∧ ((p5 ∧ (False → True)) ∧ p5)) ∧ p1)) ∧ True)) → ((p3 ∨ (False ∧ p3)) ∧ True)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_731235387326345051796628799845 : ((((p3 ∨ (p3 ∨ p2)) → (((((p2 ∧ p4) ∧ False) ∧ ((p4 → p5) ∧ (((p4 ∧ (p1 ∨ False)) ∧ (p4 → p5)) ∧ p4))) ∨ p2) ∨ True)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_51024084807577611303323193871 : (((p3 ∧ ((True ∧ (((True → (p5 ∧ (p5 → True))) ∨ (p4 → p4)) ∨ (p4 ∨ p1))) → p1)) ∧ (((p1 → p2) ∧ p1) ∨ (p1 → p4))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_157580180786400851355602729475 : ((((p2 ∨ p1) → (((p2 → (((False ∧ (False ∧ True)) → False) → p5)) ∨ False) → p2)) → (p5 → p5)) ∨ ((True → (p1 ∧ p1)) ∨ (p5 → p2))) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- One of the premise coincides with the conclusion.
  exact h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_138581551460444516688751336448 : (((((p2 ∨ (p2 ∧ (p5 ∧ p2))) ∨ ((((p5 → p3) → (p4 ∧ ((p2 ∧ True) ∧ p1))) → True) ∨ p4)) → True) ∧ p4) → ((p3 ∨ False) → p3)) := by
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
    -- One of the premise coincides with the conclusion.
    exact h3
  case inr h6 =>
    -- False on the left can always be used.
    apply False.elim h6



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_41835244137770400099577821096 : ((((p3 ∧ (True → p3)) ∧ ((True ∧ ((((p4 ∨ (p5 ∨ p5)) → p5) → p1) ∨ (p2 ∨ (p2 ∨ (p5 ∧ (p2 ∧ p3)))))) ∨ True)) ∨ False) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_47326230316761012679622437696 : ((((p1 ∨ (p3 → p3)) → (p4 → (p2 ∨ (((True → (p1 ∨ ((p4 ∨ p3) → ((p4 ∧ True) ∨ p1)))) ∧ p3) ∨ True)))) ∨ (p2 ∧ p2)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_43774334767210920951482360929 : ((((True ∨ ((p4 → ((p2 ∨ False) ∧ (((p4 ∧ (False ∨ True)) ∧ p2) ∧ p1))) → (p3 → (p2 ∨ ((p4 → False) → p3))))) → p3) → p4) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_608661968332124449699492420129 : (((((((p2 ∧ (((p4 ∨ p2) ∧ p4) ∧ p5)) ∨ (((p5 → p5) ∨ ((p5 ∨ p1) ∧ (p3 → True))) ∨ p1)) ∨ (p5 ∨ p1)) ∨ p3) ∨ p3) ∨ p3) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
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
  -- Implications on the right can always be decomposed.
  intro h1
  -- One of the premise coincides with the conclusion.
  exact h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_158409630826339918815863137029 : (((p1 ∧ True) ∨ ((p2 → (((p3 → (p1 ∨ (False ∧ (False ∧ True)))) → p3) ∧ (p5 ∨ p5))) → p2)) ∨ (((p1 ∧ (False → p2)) ∧ p1) → True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_196714966320668335291481387159 : (((((False → (True ∨ p4)) ∨ True) → p4) ∧ p4) ∨ ((True ∨ ((p4 ∧ ((p1 ∨ p2) ∧ True)) → (False ∧ (p3 → p5)))) ∨ (False ∨ (p3 ∨ p4)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_112035040625233973205759667883 : ((((p4 ∧ (p3 ∧ False)) ∨ (((p1 → (p3 ∧ (True ∧ ((p1 → ((p3 ∨ p5) ∧ True)) ∨ (p3 ∨ p2))))) ∧ p5) ∨ True)) ∨ p1) ∨ (True → p1)) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_205002646489573361132046888009 : (((False ∨ ((p3 → p5) ∧ True)) → p1) ∨ (p1 ∨ (((((p1 ∧ (True ∨ p5)) ∧ p5) ∧ (True ∨ False)) → p1) ∨ ((p4 ∨ (p3 → p4)) ∧ p2)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
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
  let h6 := h4.left
  let h7 := h4.right
  -- Disjunctions on the left can always be decomposed.
  cases h7
  case inl h8 =>
    -- Disjunctions on the left can always be decomposed.
    cases h3
    case inl h9 =>
      -- One of the premise coincides with the conclusion.
      exact h6
    case inr h10 =>
      -- False on the left can always be used.
      apply False.elim h10
  case inr h11 =>
    -- Disjunctions on the left can always be decomposed.
    cases h3
    case inl h12 =>
      -- One of the premise coincides with the conclusion.
      exact h6
    case inr h13 =>
      -- False on the left can always be used.
      apply False.elim h13



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_593545407395963835952525696121 : (((((p5 ∧ ((p4 ∧ (p4 ∨ (p1 → (p2 → ((p2 ∨ (False → False)) ∨ ((p2 ∨ p3) ∨ True)))))) ∨ True)) → ((p2 → p3) ∨ False)) ∧ True) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_59093755969327109288917186413 : (((p5 ∧ p4) ∨ (((p2 ∧ ((p3 ∨ p1) ∧ p3)) ∨ ((True ∨ p4) ∨ (p3 → p1))) ∨ (((((p5 ∨ p4) ∨ True) ∨ p4) → p2) ∧ p4))) ∨ p3) := by
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
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_682537855338548440898063089035 : (((((((True ∨ False) → (True ∨ True)) ∨ (p3 → (p4 → p5))) ∨ (p1 ∧ ((p3 ∧ p3) ∨ p2))) ∧ (p1 ∨ ((p5 → (p3 ∧ p3)) ∧ True))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_977271171938393462052445438447 : (((True ∧ ((True ∧ (p1 ∨ (False ∨ ((p5 → (p3 ∨ ((True ∧ True) ∨ True))) ∨ p2)))) → ((((p5 ∨ p4) → (p2 ∨ p2)) → p4) ∧ False))) → p1) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- We want to use the implication h3 based on <expert-advice>. So we show its premise.
  have h4 : (True ∧ (p1 ∨ (False ∨ ((p5 → (p3 ∨ ((True ∧ True) ∨ True))) ∨ p2)))) := by
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
    intro h5
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h3, we can now drive its conclusion.
  let h6 := h3 h4
  -- We need to get the right conjuct of h6 based on <expert-advice>.
  let h7 := h6.right
  -- False on the left can always be used.
  apply False.elim h7
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_57906049769499365858640350208 : (((p4 ∨ (p1 ∨ p3)) → ((p2 ∨ (p4 ∧ ((p5 ∧ (p3 → False)) → (((p1 → p2) ∧ (p1 ∨ (p1 → p3))) → p2)))) ∨ (p1 → True))) ∨ p3) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
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
theorem thm_5_vars_320514840929432454445838636881 : (p4 ∨ (True ∧ (((p3 ∧ (((False ∨ ((p2 ∨ (p4 → p3)) ∨ p5)) ∨ p4) ∧ (False → (False ∨ (p3 ∧ p1))))) ∧ (p2 → p5)) ∨ (True ∨ p4)))) := by
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
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_167160274042850979370256006363 : (((((p4 ∧ p2) → p3) → ((p1 ∧ p4) → (p4 ∨ (False ∧ (True → (p4 → p4)))))) ∨ p1) → (p2 → (p1 ∨ (((p3 ∨ False) → False) ∨ True)))) := by
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
    -- True on the right can always be proven directly.
    apply True.intro
  case inr h4 =>
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- One of the premise coincides with the conclusion.
    exact h4



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_343638306871256823631857701969 : (p2 → (True ∧ ((True → ((((p3 ∨ p4) ∧ (p1 → p1)) → (p2 → (p4 ∨ (p2 ∨ p1)))) → p1)) ∨ ((p4 ∧ p2) → ((False ∨ p4) → p2))))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h2
  -- Implications on the right can always be decomposed.
  intro h3
  -- Disjunctions on the left can always be decomposed.
  cases h3
  case inl h4 =>
    -- False on the left can always be used.
    apply False.elim h4
  case inr h5 =>
    -- Conjunctions on the left can always be decomposed.
    let h6 := h2.left
    let h7 := h2.right
    -- One of the premise coincides with the conclusion.
    exact h7



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_257746873358585073823488911479 : ((p3 ∨ p4) → (((((p2 ∧ p4) → (((p5 ∨ (True → (p2 ∧ p1))) ∨ p1) → ((True ∧ p3) → p5))) → p1) → p3) ∨ ((p5 → p5) ∨ p3))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h2 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h2
  case inr h3 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Implications on the right can always be decomposed.
    intro h4
    -- One of the premise coincides with the conclusion.
    exact h4



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_194084053270784560372795628729 : ((True → ((p3 ∨ p3) → (True → ((p5 ∧ p4) ∨ p4)))) → (p3 ∨ ((p5 ∧ ((False → (p4 → p5)) → ((p3 ∨ (p1 ∨ p1)) ∧ False))) → False))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h2
  -- Conjunctions on the left can always be decomposed.
  let h3 := h2.left
  let h4 := h2.right
  -- We want to use the implication h4 based on <expert-advice>. So we show its premise.
  have h5 : (False → (p4 → p5)) := by
    -- Implications on the right can always be decomposed.
    intro h6
    -- Implications on the right can always be decomposed.
    intro h7
    -- False on the left can always be used.
    apply False.elim h6
  -- We have shown the premise of h4, we can now drive its conclusion.
  let h8 := h4 h5
  -- We need to get the right conjuct of h8 based on <expert-advice>.
  let h9 := h8.right
  -- False on the left can always be used.
  apply False.elim h9



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_693973867322355624770434994108 : ((((((p3 ∨ False) ∨ (p4 ∧ (((p2 ∧ p5) ∧ p5) ∨ p4))) ∨ (True ∧ p4)) ∨ ((p5 ∨ (p5 ∧ p1)) ∧ (p2 → ((False → p3) ∧ True)))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_147408737316004672725226631580 : (((((p5 → p5) ∨ (True → True)) ∧ ((p3 ∧ (p5 → p3)) ∨ (p1 ∨ ((p5 ∧ (p4 ∧ False)) ∧ p5)))) ∨ p5) ∨ ((False ∧ (False ∨ True)) → True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_349419022815264331336780628636 : (p3 → (p4 → (((p3 ∧ (p2 ∧ ((p2 ∧ True) ∨ p3))) ∨ (p2 ∧ False)) ∨ ((p1 → (p3 → (p2 ∧ p1))) ∨ (True → (p2 → (p4 → p2))))))) := by
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
  -- Implications on the right can always be decomposed.
  intro h4
  -- Implications on the right can always be decomposed.
  intro h5
  -- One of the premise coincides with the conclusion.
  exact h4



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_615784015809735535868932561021 : (((((((p3 ∧ (p4 → ((True ∧ p1) ∨ p1))) ∧ ((p3 → True) → p2)) ∧ p1) ∨ ((((p1 ∧ p4) ∨ p4) ∨ p5) ∧ (False ∧ False))) ∨ p3) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_160576055701829405633706078367 : (((p2 ∧ ((p5 ∧ (((p2 ∧ p4) ∨ p1) ∧ p2)) → (p5 → p2))) → (((p2 ∧ p4) ∧ p1) ∧ p5)) → ((p2 ∧ ((p3 ∧ False) → False)) → p5)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Conjunctions on the left can always be decomposed.
  let h3 := h2.left
  let h4 := h2.right
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h5 : (p2 ∧ ((p5 ∧ (((p2 ∧ p4) ∨ p1) ∧ p2)) → (p5 → p2))) := by
    -- Conjunctions on the right can always be decomposed.
    apply And.intro
    -- One of the premise coincides with the conclusion.
    exact h3
    -- Implications on the right can always be decomposed.
    intro h6
    -- Implications on the right can always be decomposed.
    intro h7
    -- Conjunctions on the left can always be decomposed.
    let h8 := h6.left
    let h9 := h6.right
    -- Conjunctions on the left can always be decomposed.
    let h10 := h9.left
    let h11 := h9.right
    -- Disjunctions on the left can always be decomposed.
    cases h10
    case inl h12 =>
      -- Conjunctions on the left can always be decomposed.
      let h13 := h12.left
      let h14 := h12.right
      -- One of the premise coincides with the conclusion.
      exact h11
    case inr h15 =>
      -- One of the premise coincides with the conclusion.
      exact h11
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h16 := h1 h5
  -- We need to get the right conjuct of h16 based on <expert-advice>.
  let h17 := h16.right
  -- One of the premise coincides with the conclusion.
  exact h17



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_263895939186676872432127872458 : (True ∧ ((((False ∧ p4) → p4) ∧ (p5 ∧ ((False ∨ False) ∨ (p4 ∧ (p4 ∧ p1))))) ∨ ((((p4 → True) → (True ∨ (p5 → p2))) ∨ p1) → True))) := by
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
theorem thm_5_vars_301289154080793198853129831361 : (False ∨ ((((p4 ∨ p2) ∨ p5) ∨ (p2 ∨ True)) → (((((((False ∨ (p1 → p3)) ∨ p2) ∧ p3) ∨ p2) ∨ p3) → p5) ∨ (p4 → (False → False))))) := by
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
      -- Disjunctions on the left can always be decomposed.
      cases h3
      case inl h4 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
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
        -- False on the left can always be used.
        apply False.elim h9
    case inr h10 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Implications on the right can always be decomposed.
      intro h11
      -- Implications on the right can always be decomposed.
      intro h12
      -- False on the left can always be used.
      apply False.elim h12
  case inr h13 =>
    -- Disjunctions on the left can always be decomposed.
    cases h13
    case inl h14 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Implications on the right can always be decomposed.
      intro h15
      -- Implications on the right can always be decomposed.
      intro h16
      -- False on the left can always be used.
      apply False.elim h16
    case inr h17 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Implications on the right can always be decomposed.
      intro h18
      -- Implications on the right can always be decomposed.
      intro h19
      -- False on the left can always be used.
      apply False.elim h19



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_644434260563974258778175778303 : ((((False ∨ (p3 ∨ (((((p4 ∧ p3) ∨ True) ∧ (p3 → p2)) → (True → ((p1 → p2) → p4))) → (p3 → (False ∨ (False ∧ p2)))))) → p4) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_184209354854341736000365929105 : ((((p3 → ((True → p2) → (p1 ∧ (False ∧ False)))) ∧ True) → p2) ∨ (False ∨ ((p5 ∧ p3) ∨ (True ∨ ((p1 ∨ p5) ∨ (True → (p3 ∨ p5))))))) := by
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



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_138345340092555240057005193664 : ((p4 → ((((False ∨ (p5 → ((p2 → (((True → p2) → p1) → p5)) → (p3 ∧ p4)))) ∨ p2) ∧ (p1 → p2)) ∨ p1)) ∨ ((p2 → p3) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_318853505982200021361650688578 : (p4 ∨ (((((p4 ∨ p2) ∧ ((p3 ∨ p1) → True)) → (((False → p5) → ((p2 ∧ p5) ∧ (p3 → p4))) → False)) ∨ p1) ∨ (False → (p4 ∨ p3)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_665047234581061180226525984193 : ((((p4 → (p3 ∨ ((((p5 ∧ True) ∧ (((p4 ∧ (p1 ∧ (p4 ∨ p5))) ∨ True) ∨ p4)) ∧ p3) → (p3 ∧ (False ∧ False))))) → (p5 ∨ False)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_587184073413585968356956513160 : (((((p4 → (p1 ∨ (p5 ∧ ((((p2 ∧ (True → (False ∧ p4))) ∨ p3) ∧ (p2 ∨ p1)) → ((p4 ∧ False) ∨ (p5 → False)))))) ∧ False) ∧ p1) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_258810924852573167132481051439 : ((True → False) → (p5 ∨ ((((((p5 ∨ p1) → True) → ((p4 → p2) ∧ p4)) → ((p5 ∧ p1) ∧ (((p4 → p5) ∨ p5) ∧ p2))) → p1) ∧ p5))) := by
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
theorem thm_5_vars_121348632553144475390331813979 : ((((p1 → ((((p5 ∨ ((True ∨ True) ∨ (p2 → p4))) ∧ False) → (p3 → ((p2 ∨ p1) → p2))) → (True ∧ p5))) ∧ False) → True) → (p4 → p4)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- One of the premise coincides with the conclusion.
  exact h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_52707641442038490764644416097 : (((p5 → (((p2 ∧ (False ∧ p3)) ∨ (p2 ∧ p1)) ∧ ((p3 → p1) ∧ p3))) ∨ ((True → (((True ∨ (False ∨ p4)) ∨ False) ∨ False)) ∨ p2)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_797637228022415975334106168307 : (((p1 → ((((p2 ∨ ((p5 ∧ p4) → p4)) ∨ p5) ∨ ((p4 ∨ (p2 ∨ (((p1 → p1) → True) ∧ ((p3 → True) ∧ True)))) → p3)) → p5)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_669066500054941385848709099835 : ((((((p5 ∧ (((p4 ∨ (False ∧ (p1 ∧ p1))) ∨ p3) ∨ ((False → p3) → ((p3 ∧ False) ∨ p4)))) → True) → False) ∨ (True ∧ (p5 → True))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_245296941204517424349964822027 : ((p2 ∧ p2) ∨ ((False ∨ ((False ∧ (p4 ∨ (((p4 ∨ (p2 → True)) ∧ True) ∧ (p5 ∨ ((p2 → p2) ∨ p1))))) ∨ True)) ∧ ((p4 ∧ p3) → True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_305206779005389848139314780438 : (p1 ∨ (((((p2 → p3) → ((p3 ∨ p2) → (((True ∨ False) → p2) ∨ True))) → (True → (p4 ∨ p3))) ∨ p1) → ((p3 ∧ (p2 → True)) ∨ True))) := by
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
theorem thm_5_vars_427507071284706441967639521037 : (((((p3 ∨ (p3 → (p4 ∧ (((False ∨ (p4 ∧ p5)) ∨ (p1 ∨ ((True → (p2 → (p3 ∧ p3))) ∨ p5))) ∧ p1)))) ∧ p4) ∨ (True ∨ p4)) ∧ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_37484857460040428583891200413 : (((((False ∨ ((p5 ∨ p4) → p3)) → (p4 ∨ (((p4 ∨ p4) → ((p1 ∧ False) ∨ p3)) ∧ ((True → (False → p1)) ∧ p4)))) ∨ p4) ∧ p2) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_148259112020076927111720919804 : (((p4 ∧ (p2 → (((False ∧ (p3 ∧ (p3 ∧ (p3 → p2)))) ∨ p4) ∧ (p1 → p4)))) ∨ (True → (p1 ∧ p2))) ∨ ((p2 ∨ False) → (False → p5))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- False on the left can always be used.
  apply False.elim h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_755570919463769701436920985258 : (((p1 ∧ (((p4 ∧ (p1 ∨ (p5 ∨ (False ∨ (p1 ∨ (((False → (False ∨ (p5 ∨ p3))) → (p4 → False)) ∨ (p1 → p3))))))) ∧ True) ∨ p1)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_137156845612019796510155048414 : ((False ∧ (((p3 ∨ (p2 ∨ (p1 ∨ p3))) → ((((p4 ∧ p4) → p2) → p2) ∧ (((False → p3) ∧ p1) ∨ p3))) ∨ p1)) ∨ (True → (True ∨ True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_65036723656188330774889002184 : ((p2 ∨ ((p3 → p1) → (p4 ∧ (((((((True ∧ p5) ∧ False) ∧ False) → p3) ∧ ((False ∧ p4) → p5)) ∨ (p3 ∧ p2)) → (p5 ∧ p2))))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_136032445498670704252314594751 : ((((True → p5) ∧ (((True ∧ p4) ∧ p2) ∨ (p5 ∨ p4))) → ((((((p5 ∧ p2) → p2) → False) ∨ p2) ∧ p3) ∧ p5)) ∨ ((p5 ∧ p2) → p5)) := by
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
theorem thm_5_vars_157734601559220607788968926039 : (((p1 → (p2 ∨ (p5 ∧ (((((p4 ∧ p2) ∨ p3) ∧ False) ∨ p3) → True)))) → ((p2 ∧ p1) ∨ p5)) ∨ (False → (p2 ∨ (p4 → (p5 ∨ p4))))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_177791290933731986777213063662 : (((False ∨ ((p1 → ((False ∧ p2) ∧ (p5 ∨ (p1 → p2)))) → p4)) ∧ p2) ∨ (((True ∧ (p3 → True)) ∨ False) ∧ (p1 ∨ ((p1 ∧ p3) → True)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- True on the right can always be proven directly.
  apply True.intro
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
theorem thm_5_vars_356278661508401513711783312087 : (p5 → ((((p4 ∨ ((p1 ∧ ((p1 → p4) → p3)) → (True → (p4 ∨ True)))) → p3) ∧ p3) → (((p1 ∧ (True → (p2 ∧ p1))) ∨ p3) ∨ False))) := by
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
  exact h4



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_134394827570561693015502161535 : (((True → ((((p5 ∧ p3) ∧ ((p5 ∧ ((p4 ∧ p4) → False)) → p4)) ∧ False) ∨ ((p3 ∨ False) ∨ (p3 ∨ True)))) ∨ p3) ∨ ((p3 ∨ p3) → p1)) := by
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
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_52050478203124139493508528224 : (((p2 → (((((p4 ∨ False) → (p2 → (p5 ∨ True))) ∧ p5) → False) ∨ (p1 → p2))) ∨ (p2 ∨ (False ∨ (((False ∧ False) → False) → p5)))) ∨ p1) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h2
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_245494904797845950910015759056 : ((p2 ∧ p5) ∨ ((True → (p2 ∧ False)) ∨ (((True ∨ (p4 → (((p2 → p5) ∧ (p2 ∧ p3)) ∨ False))) ∧ ((False ∨ (True ∨ False)) → p4)) ∨ True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_205659135994956768304891913252 : (((False ∨ p2) ∨ (p2 ∨ (p3 ∧ p3))) ∨ ((((((p1 ∧ p1) ∨ False) ∨ (p3 ∧ p3)) ∧ p5) ∨ ((p2 ∨ ((p4 ∨ p3) ∧ p4)) ∨ True)) ∨ False)) := by
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
theorem thm_5_vars_118457516732256184279690857808 : ((p3 ∨ (((((True ∨ p4) ∧ ((p3 ∨ p3) → ((p1 → False) → (p2 → p1)))) → (p4 ∧ p1)) ∨ ((p1 ∨ p2) ∧ False)) ∨ False)) ∨ (p4 → p4)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_789431716705171215382964109580 : (((p5 ∨ ((p1 → (True ∧ (p4 → ((((p3 ∧ p4) → (p4 ∨ True)) → p4) ∧ True)))) → (True ∧ (((False → p4) → p5) → (p4 ∨ p5))))) ∨ p5) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- Implications on the right can always be decomposed.
  intro h2
  -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
  have h3 : (False → p4) := by
    -- Implications on the right can always be decomposed.
    intro h4
    -- False on the left can always be used.
    apply False.elim h4
  -- We have shown the premise of h2, we can now drive its conclusion.
  let h5 := h2 h3
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h5
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_166320467613066993839286836385 : ((p5 ∧ (((p1 ∧ p3) ∨ ((p4 ∨ (((p3 → p2) ∧ p1) ∨ False)) ∨ p4)) → (p5 ∨ True))) ∨ ((p3 → p1) ∨ (True ∨ ((p5 ∨ False) ∧ p5)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_56226087114390431837882702804 : (((p3 ∨ (p4 ∧ (False ∨ p5))) ∨ (((True ∧ (p2 → (p2 ∨ ((p3 → (p3 → True)) → (p5 ∨ True))))) ∨ (False → (True → False))) → p3)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_582423678395759180524961450670 : (((p5 → (((((p2 ∧ (p2 → (p2 → (False → (p4 → ((p3 ∧ p3) ∧ p4)))))) → p4) ∧ p1) ∨ (p2 → ((False ∨ p5) ∨ True))) ∧ True)) ∧ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h2
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
theorem thm_5_vars_186480444464814057427208590195 : (((((False → p4) ∧ p5) → (p1 → (p3 → p3))) ∧ (p1 → p5)) → (((False ∨ ((p1 → (p1 ∨ ((p1 ∧ p5) → p1))) → p1)) ∨ True) ∨ True)) := by
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
theorem thm_5_vars_149690871399198720239834909813 : ((p5 ∧ (((((p5 ∨ False) ∨ p1) ∨ p2) ∧ ((p4 ∧ ((p1 ∨ False) ∧ p1)) ∧ True)) → (p3 → (p5 ∧ p2)))) ∨ ((p2 ∧ False) → (True → p4))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Conjunctions on the left can always be decomposed.
  let h3 := h1.left
  let h4 := h1.right
  -- False on the left can always be used.
  apply False.elim h4



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_215152627583292100776731655146 : ((True ∧ ((p2 ∧ p4) ∧ False)) ∨ ((((p4 ∧ (((p2 ∧ p3) → p1) ∨ True)) ∧ p2) ∨ ((p4 ∧ (p1 ∨ True)) → (p4 ∨ (p5 → p3)))) ∨ False)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
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
  cases h3
  case inl h4 =>
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- One of the premise coincides with the conclusion.
    exact h2
  case inr h5 =>
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- One of the premise coincides with the conclusion.
    exact h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_47306328399237102504028823267 : (((((p2 → p1) ∧ p4) ∨ (((p1 → p5) → p1) ∧ (p2 → (((False ∨ True) ∧ (p1 → (p5 ∨ (True → False)))) ∨ p4)))) ∨ (False → p3)) ∨ p2) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_323932357978577491015544659110 : (p5 ∨ (((p3 ∨ (p3 ∧ ((True ∧ False) → True))) ∧ (p4 ∨ ((False ∨ p5) ∧ (p3 ∨ True)))) → (((True → (p3 ∨ p2)) ∧ True) ∧ (p2 ∨ p3)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h2
  -- Conjunctions on the left can always be decomposed.
  let h3 := h1.left
  let h4 := h1.right
  -- Disjunctions on the left can always be decomposed.
  cases h3
  case inl h5 =>
    -- Disjunctions on the left can always be decomposed.
    cases h4
    case inl h6 =>
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- One of the premise coincides with the conclusion.
      exact h5
    case inr h7 =>
      -- Conjunctions on the left can always be decomposed.
      let h8 := h7.left
      let h9 := h7.right
      -- Disjunctions on the left can always be decomposed.
      cases h8
      case inl h10 =>
        -- False on the left can always be used.
        apply False.elim h10
      case inr h11 =>
        -- Disjunctions on the left can always be decomposed.
        cases h9
        case inl h12 =>
          -- Show the left disjunct based on <expert-advice>.
          apply Or.inl
          -- One of the premise coincides with the conclusion.
          exact h12
        case inr h13 =>
          -- Show the left disjunct based on <expert-advice>.
          apply Or.inl
          -- One of the premise coincides with the conclusion.
          exact h5
  case inr h14 =>
    -- Conjunctions on the left can always be decomposed.
    let h15 := h14.left
    let h16 := h14.right
    -- Disjunctions on the left can always be decomposed.
    cases h4
    case inl h17 =>
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- One of the premise coincides with the conclusion.
      exact h15
    case inr h18 =>
      -- Conjunctions on the left can always be decomposed.
      let h19 := h18.left
      let h20 := h18.right
      -- Disjunctions on the left can always be decomposed.
      cases h19
      case inl h21 =>
        -- False on the left can always be used.
        apply False.elim h21
      case inr h22 =>
        -- Disjunctions on the left can always be decomposed.
        cases h20
        case inl h23 =>
          -- Show the left disjunct based on <expert-advice>.
          apply Or.inl
          -- One of the premise coincides with the conclusion.
          exact h23
        case inr h24 =>
          -- Show the left disjunct based on <expert-advice>.
          apply Or.inl
          -- One of the premise coincides with the conclusion.
          exact h15
  -- True on the right can always be proven directly.
  apply True.intro
  -- Conjunctions on the left can always be decomposed.
  let h25 := h1.left
  let h26 := h1.right
  -- Disjunctions on the left can always be decomposed.
  cases h25
  case inl h27 =>
    -- Disjunctions on the left can always be decomposed.
    cases h26
    case inl h28 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- One of the premise coincides with the conclusion.
      exact h27
    case inr h29 =>
      -- Conjunctions on the left can always be decomposed.
      let h30 := h29.left
      let h31 := h29.right
      -- Disjunctions on the left can always be decomposed.
      cases h30
      case inl h32 =>
        -- False on the left can always be used.
        apply False.elim h32
      case inr h33 =>
        -- Disjunctions on the left can always be decomposed.
        cases h31
        case inl h34 =>
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- One of the premise coincides with the conclusion.
          exact h34
        case inr h35 =>
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- One of the premise coincides with the conclusion.
          exact h27
  case inr h36 =>
    -- Conjunctions on the left can always be decomposed.
    let h37 := h36.left
    let h38 := h36.right
    -- Disjunctions on the left can always be decomposed.
    cases h26
    case inl h39 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- One of the premise coincides with the conclusion.
      exact h37
    case inr h40 =>
      -- Conjunctions on the left can always be decomposed.
      let h41 := h40.left
      let h42 := h40.right
      -- Disjunctions on the left can always be decomposed.
      cases h41
      case inl h43 =>
        -- False on the left can always be used.
        apply False.elim h43
      case inr h44 =>
        -- Disjunctions on the left can always be decomposed.
        cases h42
        case inl h45 =>
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- One of the premise coincides with the conclusion.
          exact h45
        case inr h46 =>
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- One of the premise coincides with the conclusion.
          exact h37



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_152681126087674889508446958589 : (((False ∧ True) ∨ ((p4 ∨ p4) ∧ ((False → ((p3 ∧ (False ∧ (p2 ∨ p2))) ∧ ((p5 ∨ p5) → True))) → False))) → (p5 ∨ ((True → p5) → False))) := by
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
    -- Conjunctions on the left can always be decomposed.
    let h6 := h5.left
    let h7 := h5.right
    -- Disjunctions on the left can always be decomposed.
    cases h6
    case inl h8 =>
      -- We want to use the implication h7 based on <expert-advice>. So we show its premise.
      have h9 : (False → ((p3 ∧ (False ∧ (p2 ∨ p2))) ∧ ((p5 ∨ p5) → True))) := by
        -- Implications on the right can always be decomposed.
        intro h10
        -- Conjunctions on the right can always be decomposed.
        apply And.intro
        -- Conjunctions on the right can always be decomposed.
        apply And.intro
        -- False on the left can always be used.
        apply False.elim h10
        -- Conjunctions on the right can always be decomposed.
        apply And.intro
        -- False on the left can always be used.
        apply False.elim h10
        -- False on the left can always be used.
        apply False.elim h10
        -- Implications on the right can always be decomposed.
        intro h11
        -- True on the right can always be proven directly.
        apply True.intro
      -- We have shown the premise of h7, we can now drive its conclusion.
      let h12 := h7 h9
      -- False on the left can always be used.
      apply False.elim h12
    case inr h13 =>
      -- We want to use the implication h7 based on <expert-advice>. So we show its premise.
      have h14 : (False → ((p3 ∧ (False ∧ (p2 ∨ p2))) ∧ ((p5 ∨ p5) → True))) := by
        -- Implications on the right can always be decomposed.
        intro h15
        -- Conjunctions on the right can always be decomposed.
        apply And.intro
        -- Conjunctions on the right can always be decomposed.
        apply And.intro
        -- False on the left can always be used.
        apply False.elim h15
        -- Conjunctions on the right can always be decomposed.
        apply And.intro
        -- False on the left can always be used.
        apply False.elim h15
        -- False on the left can always be used.
        apply False.elim h15
        -- Implications on the right can always be decomposed.
        intro h16
        -- True on the right can always be proven directly.
        apply True.intro
      -- We have shown the premise of h7, we can now drive its conclusion.
      let h17 := h7 h14
      -- False on the left can always be used.
      apply False.elim h17



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_357277250583599851632798130006 : (p5 → ((p4 ∧ p5) ∨ ((((p1 ∨ ((p1 ∧ (p3 ∧ p1)) → p3)) ∧ p5) → (((p1 → (p4 ∧ (True ∨ (p3 ∨ p1)))) ∧ True) ∧ False)) → False))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h2
  -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
  have h3 : ((p1 ∨ ((p1 ∧ (p3 ∧ p1)) → p3)) ∧ p5) := by
    -- Conjunctions on the right can always be decomposed.
    apply And.intro
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h4
    -- Conjunctions on the left can always be decomposed.
    let h5 := h4.left
    let h6 := h4.right
    -- Conjunctions on the left can always be decomposed.
    let h7 := h6.left
    let h8 := h6.right
    -- One of the premise coincides with the conclusion.
    exact h7
    -- One of the premise coincides with the conclusion.
    exact h1
  -- We have shown the premise of h2, we can now drive its conclusion.
  let h9 := h2 h3
  -- We need to get the right conjuct of h9 based on <expert-advice>.
  let h10 := h9.right
  -- False on the left can always be used.
  apply False.elim h10



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_749183717671578087664958532508 : ((((p5 → p2) → ((((p5 ∨ False) ∨ p1) ∨ (p2 ∧ ((p4 ∨ (p1 ∧ (False ∨ p2))) ∧ False))) ∨ ((p1 ∧ ((p4 → p5) ∨ p3)) ∨ False))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_695193325851398037508962770184 : (((((True ∨ ((p1 ∨ (((p1 ∧ p1) ∧ p5) ∨ (True ∧ p4))) ∧ p4)) ∨ p1) → (((False ∨ (p1 ∧ (True → (p5 ∧ True)))) ∨ p1) → p2)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_622400941400783780648724821230 : ((((p3 ∧ (((p5 ∨ (((p1 → p5) ∧ (p3 → p3)) ∨ p1)) → p2) → (((False → (False → False)) ∨ p2) ∧ (True → (True → False))))) ∨ p5) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_937699687424094163307174912182 : ((((p2 ∧ ((p4 ∨ p2) → (p3 ∨ p3))) ∧ (((p1 ∨ (p4 ∧ p4)) ∨ p4) ∧ ((p1 → False) ∧ (p1 ∧ (p1 ∨ ((False ∨ p5) → p2)))))) → False) ∧ True) := by
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
  -- Conjunctions on the left can always be decomposed.
  let h6 := h3.left
  let h7 := h3.right
  -- Disjunctions on the left can always be decomposed.
  cases h6
  case inl h8 =>
    -- Disjunctions on the left can always be decomposed.
    cases h8
    case inl h9 =>
      -- Conjunctions on the left can always be decomposed.
      let h10 := h7.left
      let h11 := h7.right
      -- Conjunctions on the left can always be decomposed.
      let h12 := h11.left
      let h13 := h11.right
      -- Disjunctions on the left can always be decomposed.
      cases h13
      case inl h14 =>
        -- We want to use the implication h10 based on <expert-advice>. So we show its premise.
        have h15 : p1 := by
          -- One of the premise coincides with the conclusion.
          exact h14
        -- We have shown the premise of h10, we can now drive its conclusion.
        let h16 := h10 h15
        -- False on the left can always be used.
        apply False.elim h16
      case inr h17 =>
        -- We want to use the implication h10 based on <expert-advice>. So we show its premise.
        have h18 : p1 := by
          -- One of the premise coincides with the conclusion.
          exact h12
        -- We have shown the premise of h10, we can now drive its conclusion.
        let h19 := h10 h18
        -- False on the left can always be used.
        apply False.elim h19
    case inr h20 =>
      -- Conjunctions on the left can always be decomposed.
      let h21 := h20.left
      let h22 := h20.right
      -- Conjunctions on the left can always be decomposed.
      let h23 := h7.left
      let h24 := h7.right
      -- Conjunctions on the left can always be decomposed.
      let h25 := h24.left
      let h26 := h24.right
      -- Disjunctions on the left can always be decomposed.
      cases h26
      case inl h27 =>
        -- We want to use the implication h23 based on <expert-advice>. So we show its premise.
        have h28 : p1 := by
          -- One of the premise coincides with the conclusion.
          exact h27
        -- We have shown the premise of h23, we can now drive its conclusion.
        let h29 := h23 h28
        -- False on the left can always be used.
        apply False.elim h29
      case inr h30 =>
        -- We want to use the implication h23 based on <expert-advice>. So we show its premise.
        have h31 : p1 := by
          -- One of the premise coincides with the conclusion.
          exact h25
        -- We have shown the premise of h23, we can now drive its conclusion.
        let h32 := h23 h31
        -- False on the left can always be used.
        apply False.elim h32
  case inr h33 =>
    -- Conjunctions on the left can always be decomposed.
    let h34 := h7.left
    let h35 := h7.right
    -- Conjunctions on the left can always be decomposed.
    let h36 := h35.left
    let h37 := h35.right
    -- Disjunctions on the left can always be decomposed.
    cases h37
    case inl h38 =>
      -- We want to use the implication h34 based on <expert-advice>. So we show its premise.
      have h39 : p1 := by
        -- One of the premise coincides with the conclusion.
        exact h38
      -- We have shown the premise of h34, we can now drive its conclusion.
      let h40 := h34 h39
      -- False on the left can always be used.
      apply False.elim h40
    case inr h41 =>
      -- We want to use the implication h34 based on <expert-advice>. So we show its premise.
      have h42 : p1 := by
        -- One of the premise coincides with the conclusion.
        exact h36
      -- We have shown the premise of h34, we can now drive its conclusion.
      let h43 := h34 h42
      -- False on the left can always be used.
      apply False.elim h43
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_646030085715820610201731786095 : ((((True → ((p3 → p3) ∧ ((p1 ∨ ((p5 ∧ False) → (False ∧ True))) → ((p5 → p3) ∧ ((p2 ∨ ((p4 ∨ p3) → p4)) ∧ p2))))) → p4) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_766543977798518059542854425358 : (((p4 ∧ (p3 ∧ (p5 ∨ (((p4 → p1) ∨ ((p1 ∧ ((p4 ∨ (p5 ∧ p4)) → ((p3 ∧ (p2 → False)) ∧ p3))) → (True ∧ p1))) ∧ p4)))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_158529057007830811924182865848 : (((True → False) → ((p5 ∨ ((p2 ∧ ((p1 → ((p4 → p2) → p4)) → (p1 → p4))) ∧ True)) ∧ False)) ∨ ((p1 → (p1 → (True → False))) ∧ p4)) := by
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



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_263121914264153770242126290800 : (True ∧ ((((p4 ∧ (p4 ∨ (True ∧ ((True ∨ p1) ∧ (p3 ∧ p4))))) ∨ True) → (False ∨ ((p5 ∧ (p1 → (True ∨ p5))) ∨ True))) ∨ (p1 → p1))) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_124592962219555057762756613250 : ((((p3 → True) ∧ (p4 ∨ (True → p4))) ∨ ((False ∨ p3) ∨ ((p1 → ((p4 → True) → (p1 ∧ ((True ∧ p4) ∧ p5)))) ∨ p3))) → (p5 → p5)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h3 =>
    -- Conjunctions on the left can always be decomposed.
    let h4 := h3.left
    let h5 := h3.right
    -- Disjunctions on the left can always be decomposed.
    cases h5
    case inl h6 =>
      -- One of the premise coincides with the conclusion.
      exact h2
    case inr h7 =>
      -- One of the premise coincides with the conclusion.
      exact h2
  case inr h8 =>
    -- Disjunctions on the left can always be decomposed.
    cases h8
    case inl h9 =>
      -- Disjunctions on the left can always be decomposed.
      cases h9
      case inl h10 =>
        -- False on the left can always be used.
        apply False.elim h10
      case inr h11 =>
        -- One of the premise coincides with the conclusion.
        exact h2
    case inr h12 =>
      -- Disjunctions on the left can always be decomposed.
      cases h12
      case inl h13 =>
        -- One of the premise coincides with the conclusion.
        exact h2
      case inr h14 =>
        -- One of the premise coincides with the conclusion.
        exact h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_357449888971129294166302159515 : (p5 → ((False → p3) → ((((p3 → p3) → (p3 → p1)) ∧ (False ∧ (p3 ∧ (False ∧ (((((p4 → False) → True) ∨ p1) ∨ p5) ∨ p3))))) ∨ p5))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h1



