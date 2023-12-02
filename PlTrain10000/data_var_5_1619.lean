variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_61055688536079585743245492768 : ((False ∧ ((p2 → (((p4 → (False → (p2 → (p1 ∧ False)))) → ((False ∧ (False ∨ p4)) ∨ ((p4 → p1) → True))) → p5)) → (True ∧ p2))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_68634690333834865486070522285 : ((p4 → ((p3 → (p3 → ((((False ∧ ((p3 → (((p1 ∧ p2) → (p2 ∧ (p4 ∧ p5))) ∧ p2)) ∨ p3)) ∧ p4) ∧ p2) ∨ False))) ∨ p3)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_251980388840873057609214300920 : ((p4 → False) ∨ ((p3 → (((((p4 ∨ True) → (p2 ∧ (False → p3))) ∧ p2) → ((p4 → p3) ∨ False)) → False)) ∨ ((p1 → (True ∨ False)) ∨ p1))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
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
theorem thm_5_vars_351670630689328646832085853249 : (p4 → (((p2 ∨ ((p3 ∨ (p4 → False)) ∨ p1)) ∧ (p4 ∧ (p2 ∧ ((p2 ∨ False) → p2)))) → (p5 → (p3 → ((p2 → (p1 ∧ p1)) ∨ p2))))) := by
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
  -- Disjunctions on the left can always be decomposed.
  cases h5
  case inl h7 =>
    -- Conjunctions on the left can always be decomposed.
    let h8 := h6.left
    let h9 := h6.right
    -- Conjunctions on the left can always be decomposed.
    let h10 := h9.left
    let h11 := h9.right
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h10
  case inr h12 =>
    -- Disjunctions on the left can always be decomposed.
    cases h12
    case inl h13 =>
      -- Disjunctions on the left can always be decomposed.
      cases h13
      case inl h14 =>
        -- Conjunctions on the left can always be decomposed.
        let h15 := h6.left
        let h16 := h6.right
        -- Conjunctions on the left can always be decomposed.
        let h17 := h16.left
        let h18 := h16.right
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- One of the premise coincides with the conclusion.
        exact h17
      case inr h19 =>
        -- Conjunctions on the left can always be decomposed.
        let h20 := h6.left
        let h21 := h6.right
        -- Conjunctions on the left can always be decomposed.
        let h22 := h21.left
        let h23 := h21.right
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- One of the premise coincides with the conclusion.
        exact h22
    case inr h24 =>
      -- Conjunctions on the left can always be decomposed.
      let h25 := h6.left
      let h26 := h6.right
      -- Conjunctions on the left can always be decomposed.
      let h27 := h26.left
      let h28 := h26.right
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- One of the premise coincides with the conclusion.
      exact h27



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_199934663203301154251206904777 : (((True ∧ ((True ∧ False) → p5)) ∨ (p5 ∧ p1)) → ((p4 ∨ (((((p2 ∧ p2) ∨ (p5 → True)) ∧ ((p1 ∨ True) → False)) ∧ p1) ∨ p4)) → p4)) := by
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
      -- One of the premise coincides with the conclusion.
      exact h3
    case inr h7 =>
      -- Conjunctions on the left can always be decomposed.
      let h8 := h7.left
      let h9 := h7.right
      -- One of the premise coincides with the conclusion.
      exact h3
  case inr h10 =>
    -- Disjunctions on the left can always be decomposed.
    cases h10
    case inl h11 =>
      -- Conjunctions on the left can always be decomposed.
      let h12 := h11.left
      let h13 := h11.right
      -- Conjunctions on the left can always be decomposed.
      let h14 := h12.left
      let h15 := h12.right
      -- Disjunctions on the left can always be decomposed.
      cases h14
      case inl h16 =>
        -- Conjunctions on the left can always be decomposed.
        let h17 := h16.left
        let h18 := h16.right
        -- Disjunctions on the left can always be decomposed.
        cases h1
        case inl h19 =>
          -- Conjunctions on the left can always be decomposed.
          let h20 := h19.left
          let h21 := h19.right
          -- We want to use the implication h15 based on <expert-advice>. So we show its premise.
          have h22 : (p1 ∨ True) := by
            -- Show the left disjunct based on <expert-advice>.
            apply Or.inl
            -- One of the premise coincides with the conclusion.
            exact h13
          -- We have shown the premise of h15, we can now drive its conclusion.
          let h23 := h15 h22
          -- False on the left can always be used.
          apply False.elim h23
        case inr h24 =>
          -- Conjunctions on the left can always be decomposed.
          let h25 := h24.left
          let h26 := h24.right
          -- We want to use the implication h15 based on <expert-advice>. So we show its premise.
          have h27 : (p1 ∨ True) := by
            -- Show the left disjunct based on <expert-advice>.
            apply Or.inl
            -- One of the premise coincides with the conclusion.
            exact h26
          -- We have shown the premise of h15, we can now drive its conclusion.
          let h28 := h15 h27
          -- False on the left can always be used.
          apply False.elim h28
      case inr h29 =>
        -- Disjunctions on the left can always be decomposed.
        cases h1
        case inl h30 =>
          -- Conjunctions on the left can always be decomposed.
          let h31 := h30.left
          let h32 := h30.right
          -- We want to use the implication h15 based on <expert-advice>. So we show its premise.
          have h33 : (p1 ∨ True) := by
            -- Show the left disjunct based on <expert-advice>.
            apply Or.inl
            -- One of the premise coincides with the conclusion.
            exact h13
          -- We have shown the premise of h15, we can now drive its conclusion.
          let h34 := h15 h33
          -- False on the left can always be used.
          apply False.elim h34
        case inr h35 =>
          -- Conjunctions on the left can always be decomposed.
          let h36 := h35.left
          let h37 := h35.right
          -- We want to use the implication h15 based on <expert-advice>. So we show its premise.
          have h38 : (p1 ∨ True) := by
            -- Show the left disjunct based on <expert-advice>.
            apply Or.inl
            -- One of the premise coincides with the conclusion.
            exact h37
          -- We have shown the premise of h15, we can now drive its conclusion.
          let h39 := h15 h38
          -- False on the left can always be used.
          apply False.elim h39
    case inr h40 =>
      -- Disjunctions on the left can always be decomposed.
      cases h1
      case inl h41 =>
        -- Conjunctions on the left can always be decomposed.
        let h42 := h41.left
        let h43 := h41.right
        -- One of the premise coincides with the conclusion.
        exact h40
      case inr h44 =>
        -- Conjunctions on the left can always be decomposed.
        let h45 := h44.left
        let h46 := h44.right
        -- One of the premise coincides with the conclusion.
        exact h40



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_457335302702633704291742695217 : (((((p2 ∧ (((p4 ∨ (p5 ∧ p3)) ∧ (p3 ∨ True)) ∨ ((p1 → (p4 → p4)) ∧ p2))) ∨ True) ∨ (((p3 ∧ (p4 ∨ True)) ∧ p4) → p1)) ∧ True) ∧ True) := by
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
theorem thm_5_vars_168060593709345497689058587096 : (((((True ∧ p3) → p5) ∨ False) ∧ (((p5 → p1) → ((p3 ∨ p3) ∨ (p3 → False))) ∨ p3)) → (((p2 ∨ p5) ∨ True) ∨ ((True ∧ p1) ∨ p3))) := by
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
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- True on the right can always be proven directly.
      apply True.intro
    case inr h6 =>
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- True on the right can always be proven directly.
      apply True.intro
  case inr h7 =>
    -- False on the left can always be used.
    apply False.elim h7



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_43074661851938127241890870860 : (((((((((p3 → ((p3 ∧ p1) → (((False ∨ (p2 ∧ p4)) ∨ p2) → p1))) → p5) → p5) ∨ False) ∧ p1) ∧ (p1 ∨ p2)) ∧ p3) → p5) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_184975924333530103618068409635 : (((p4 ∨ (False ∨ True)) → (((False ∧ True) → p4) ∧ (p2 ∨ p3))) ∨ ((p5 → p5) → (p5 → (p3 ∨ (p2 → (((False ∧ p4) → p5) ∨ p1)))))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h3
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h4
  -- Conjunctions on the left can always be decomposed.
  let h5 := h4.left
  let h6 := h4.right
  -- False on the left can always be used.
  apply False.elim h5



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_304688259759237361209792799891 : (p1 ∨ (((((((p1 → (False ∧ p4)) ∨ (p1 → ((p5 → p4) ∧ True))) → p4) ∧ True) → ((p4 ∧ (p5 → p2)) ∧ False)) ∨ True) ∨ (p2 ∧ p2))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_250732607852666259504130470473 : ((p1 → False) ∨ (p3 ∨ ((((p5 ∨ p5) ∨ p4) → ((p4 ∨ (p5 ∧ (p5 → p5))) ∨ (p3 ∨ p2))) ∧ ((p4 ∧ p1) ∨ (False → (p3 ∨ p4)))))) := by
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
    -- Disjunctions on the left can always be decomposed.
    cases h2
    case inl h3 =>
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Conjunctions on the right can always be decomposed.
      apply And.intro
      -- One of the premise coincides with the conclusion.
      exact h3
      -- Implications on the right can always be decomposed.
      intro h4
      -- One of the premise coincides with the conclusion.
      exact h4
    case inr h5 =>
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Conjunctions on the right can always be decomposed.
      apply And.intro
      -- One of the premise coincides with the conclusion.
      exact h5
      -- Implications on the right can always be decomposed.
      intro h6
      -- One of the premise coincides with the conclusion.
      exact h6
  case inr h7 =>
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- One of the premise coincides with the conclusion.
    exact h7
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h8
  -- False on the left can always be used.
  apply False.elim h8



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_598505492717899419104748817157 : ((((((True ∧ True) → False) → (p4 ∨ (((p2 ∨ ((p4 ∧ False) ∨ p5)) → (p5 ∧ (p1 ∨ (False ∨ (True ∨ (False → False)))))) ∨ p3))) ∧ True) ∨ p4) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h1
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h2 : (True ∧ True) := by
    -- Conjunctions on the right can always be decomposed.
    apply And.intro
    -- True on the right can always be proven directly.
    apply True.intro
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h3 := h1 h2
  -- False on the left can always be used.
  apply False.elim h3
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_48268779553633568226633706676 : (((p3 ∧ ((((True ∧ p3) ∧ ((((p5 → True) ∨ (p1 ∧ (p5 → p4))) ∨ (p4 → p1)) ∧ p2)) ∨ p2) ∧ (p2 ∨ p4))) → (p5 ∨ p3)) ∨ p4) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
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
      -- Disjunctions on the left can always be decomposed.
      cases h13
      case inl h14 =>
        -- Disjunctions on the left can always be decomposed.
        cases h5
        case inl h15 =>
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- One of the premise coincides with the conclusion.
          exact h10
        case inr h16 =>
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- One of the premise coincides with the conclusion.
          exact h10
      case inr h17 =>
        -- Conjunctions on the left can always be decomposed.
        let h18 := h17.left
        let h19 := h17.right
        -- Disjunctions on the left can always be decomposed.
        cases h5
        case inl h20 =>
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- One of the premise coincides with the conclusion.
          exact h10
        case inr h21 =>
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- One of the premise coincides with the conclusion.
          exact h10
    case inr h22 =>
      -- Disjunctions on the left can always be decomposed.
      cases h5
      case inl h23 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- One of the premise coincides with the conclusion.
        exact h10
      case inr h24 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- One of the premise coincides with the conclusion.
        exact h10
  case inr h25 =>
    -- Disjunctions on the left can always be decomposed.
    cases h5
    case inl h26 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- One of the premise coincides with the conclusion.
      exact h2
    case inr h27 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- One of the premise coincides with the conclusion.
      exact h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_135854749085267200020328913125 : ((((False ∨ ((p2 ∧ p5) → ((p4 ∧ (True ∨ p2)) ∧ p4))) ∧ True) ∨ (True ∧ ((((p5 ∧ p3) ∧ p5) ∧ True) ∨ p3))) ∨ (p1 → (True ∨ p4))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_37752727100596075519968236171 : ((((((p2 ∧ (p2 ∨ True)) ∨ True) ∧ (p1 ∨ (False ∨ (((p5 ∧ p4) → (p3 ∧ (p2 ∨ p1))) ∨ ((p3 → True) ∧ p5))))) → False) ∧ p2) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_164765390020734569155163850272 : (((((True ∧ p4) ∨ ((p1 ∨ p5) ∨ ((p4 ∧ p4) ∨ True))) → (p1 ∨ (p1 ∧ p2))) ∨ True) ∨ (True ∧ (p4 ∨ ((p3 ∧ (p2 ∧ False)) → True)))) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_121660823611427571340616015355 : (((((((((p2 ∨ p3) ∨ p1) → p2) → p4) → (p4 ∨ True)) ∨ p5) ∧ (p4 → ((p2 ∨ True) ∧ (False → (p3 → p3))))) → False) → (p2 ∧ p1)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h2 : (((((((p2 ∨ p3) ∨ p1) → p2) → p4) → (p4 ∨ True)) ∨ p5) ∧ (p4 → ((p2 ∨ True) ∧ (False → (p3 → p3))))) := by
    -- Conjunctions on the right can always be decomposed.
    apply And.intro
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Implications on the right can always be decomposed.
    intro h3
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro
    -- Implications on the right can always be decomposed.
    intro h4
    -- Conjunctions on the right can always be decomposed.
    apply And.intro
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro
    -- Implications on the right can always be decomposed.
    intro h5
    -- Implications on the right can always be decomposed.
    intro h6
    -- False on the left can always be used.
    apply False.elim h5
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h7 := h1 h2
  -- False on the left can always be used.
  apply False.elim h7
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h8 : (((((((p2 ∨ p3) ∨ p1) → p2) → p4) → (p4 ∨ True)) ∨ p5) ∧ (p4 → ((p2 ∨ True) ∧ (False → (p3 → p3))))) := by
    -- Conjunctions on the right can always be decomposed.
    apply And.intro
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Implications on the right can always be decomposed.
    intro h9
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro
    -- Implications on the right can always be decomposed.
    intro h10
    -- Conjunctions on the right can always be decomposed.
    apply And.intro
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro
    -- Implications on the right can always be decomposed.
    intro h11
    -- Implications on the right can always be decomposed.
    intro h12
    -- False on the left can always be used.
    apply False.elim h11
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h13 := h1 h8
  -- False on the left can always be used.
  apply False.elim h13



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_780314256839993784357317726326 : (((p2 ∨ ((((p2 ∨ ((p1 ∧ p4) ∨ ((p4 ∧ p5) ∨ p2))) ∧ p2) ∧ (p2 ∨ (p5 ∨ (p3 → p2)))) ∨ (((p3 ∨ p5) ∨ True) ∨ p3))) ∨ p5) ∧ True) := by
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
theorem thm_5_vars_616502124572005005013531300568 : (((((True ∨ (p5 ∨ (p3 → ((p2 ∨ (p3 ∨ (True → p3))) ∧ p1)))) → ((((False ∨ p2) ∨ ((p4 ∨ p3) ∨ p4)) ∨ p5) ∨ p4)) ∨ p1) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_258124185582825630839349139106 : ((p4 ∨ p3) → ((p1 ∧ (p1 ∧ (p4 ∨ p5))) ∨ (p1 → (((p2 ∨ p2) ∨ (p2 → False)) → ((False ∨ (p2 ∧ p2)) → (True ∧ (True ∨ True))))))) := by
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
    -- Implications on the right can always be decomposed.
    intro h5
    -- Conjunctions on the right can always be decomposed.
    apply And.intro
    -- True on the right can always be proven directly.
    apply True.intro
    -- Disjunctions on the left can always be decomposed.
    cases h5
    case inl h6 =>
      -- False on the left can always be used.
      apply False.elim h6
    case inr h7 =>
      -- Conjunctions on the left can always be decomposed.
      let h8 := h7.left
      let h9 := h7.right
      -- Disjunctions on the left can always be decomposed.
      cases h4
      case inl h10 =>
        -- Disjunctions on the left can always be decomposed.
        cases h10
        case inl h11 =>
          -- Show the left disjunct based on <expert-advice>.
          apply Or.inl
          -- True on the right can always be proven directly.
          apply True.intro
        case inr h12 =>
          -- Show the left disjunct based on <expert-advice>.
          apply Or.inl
          -- True on the right can always be proven directly.
          apply True.intro
      case inr h13 =>
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- True on the right can always be proven directly.
        apply True.intro
  case inr h14 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h15
    -- Implications on the right can always be decomposed.
    intro h16
    -- Implications on the right can always be decomposed.
    intro h17
    -- Conjunctions on the right can always be decomposed.
    apply And.intro
    -- True on the right can always be proven directly.
    apply True.intro
    -- Disjunctions on the left can always be decomposed.
    cases h17
    case inl h18 =>
      -- False on the left can always be used.
      apply False.elim h18
    case inr h19 =>
      -- Conjunctions on the left can always be decomposed.
      let h20 := h19.left
      let h21 := h19.right
      -- Disjunctions on the left can always be decomposed.
      cases h16
      case inl h22 =>
        -- Disjunctions on the left can always be decomposed.
        cases h22
        case inl h23 =>
          -- Show the left disjunct based on <expert-advice>.
          apply Or.inl
          -- True on the right can always be proven directly.
          apply True.intro
        case inr h24 =>
          -- Show the left disjunct based on <expert-advice>.
          apply Or.inl
          -- True on the right can always be proven directly.
          apply True.intro
      case inr h25 =>
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- True on the right can always be proven directly.
        apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_748302723438002686045727612782 : ((((p2 → p1) → ((False ∧ (p1 ∨ (((((((p4 → p4) ∨ p5) ∧ ((p2 → True) ∨ (p4 ∨ p1))) ∨ p4) → p1) ∨ True) → p3))) ∧ p4)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_748304668281389254034521391296 : ((((p2 → p1) → (((p4 ∨ ((((p5 ∨ p2) ∨ (True ∨ ((True → p5) ∨ p5))) ∨ ((p5 ∨ p4) ∧ True)) → (True ∨ p2))) → p5) ∨ True)) ∨ p1) ∧ True) := by
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
theorem thm_5_vars_259284556922996948129023829277 : ((False → p1) → ((p3 → p4) ∨ (((p4 → (p5 ∧ ((((False ∧ (True → (p4 ∨ (p3 ∨ p2)))) ∧ (p3 ∨ True)) → p2) → True))) ∧ p2) ∨ True))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_157763308552385547170375264658 : (((p4 ∧ (p5 → ((p1 → (p4 ∨ p2)) ∧ ((p5 → p5) → p1)))) ∧ ((p4 ∨ p4) ∨ (p3 → True))) ∨ (((p1 ∧ p5) → p1) ∨ (p2 ∨ False))) := by
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
theorem thm_5_vars_135310540946097234917657402735 : (((((p4 ∨ p5) → ((False ∧ ((p2 → (p4 → False)) → False)) → (p4 ∧ (p2 ∨ p3)))) → False) ∧ (p5 ∨ (p4 → False))) ∨ ((True ∧ False) → True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_190858999158815217245663199461 : (((((True → (p1 ∧ p3)) ∨ p3) → p3) → (p3 → p5)) ∨ (p2 → ((p3 ∧ ((p5 ∨ p4) ∧ (((p4 ∨ p4) → p2) → p4))) ∨ (p1 → True)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h2
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_111579414040191719815573097011 : ((((False ∧ (((p5 ∧ (p2 → p3)) → p2) ∨ (((False → ((True → True) → ((p3 ∨ p4) ∨ p1))) ∨ p1) ∧ p4))) ∧ p2) ∨ p5) ∨ (True ∧ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_65250240521433889642369256188 : ((p3 ∨ (((((p2 ∧ (((True → (True ∧ p5)) ∧ False) ∨ (True ∧ (True ∨ p1)))) ∨ (p4 ∨ p2)) ∧ p4) → (False → (p1 ∧ p4))) → p1)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_618800631050933602314254472576 : (((((p2 ∧ (True ∨ p5)) ∧ (p3 ∧ ((p3 ∧ ((False → p5) → p5)) → ((p1 → (p2 ∨ (True ∨ (p5 → False)))) ∧ (p5 ∧ p5))))) ∨ True) ∨ p4) ∧ True) := by
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
theorem thm_5_vars_113607364401359475093067493549 : (((p2 ∨ (p5 → (((p4 ∧ (((p5 ∧ p2) → (True ∨ p5)) ∧ (False → False))) ∧ p3) ∨ (p5 ∧ (p2 ∨ p2))))) ∨ (True ∨ p1)) ∨ (p3 ∨ p4)) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_9052078885273916560831432698 : (((((False ∨ (p1 ∧ (False ∧ p2))) ∧ (((False → (p4 → p3)) ∨ False) ∧ p5)) ∨ ((False ∨ (p3 ∧ ((False → p5) ∧ p5))) → p3)) ∨ p3) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
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
    -- Conjunctions on the left can always be decomposed.
    let h4 := h3.left
    let h5 := h3.right
    -- Conjunctions on the left can always be decomposed.
    let h6 := h5.left
    let h7 := h5.right
    -- One of the premise coincides with the conclusion.
    exact h4
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_690030459960167204655903235508 : ((((p3 ∧ ((p5 ∨ (p3 ∨ (True → (p5 → p5)))) ∨ (((True ∨ p2) ∨ p1) ∧ False))) ∨ (((False → (p3 → (False ∨ p4))) ∧ p2) → p5)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_133559228977825452468119081832 : ((((((((p1 ∨ p2) ∧ p3) ∨ (p1 → (((p4 ∨ True) ∧ p3) ∧ (p4 ∨ p3)))) → (p2 → False)) ∨ p5) ∨ p1) ∧ True) ∨ (p4 → (True → True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_607979267980460921499719605162 : (((((p3 → (((p3 ∨ ((p2 ∨ ((False ∨ p1) ∨ p2)) ∨ p5)) → p5) ∨ (p5 ∨ ((((True ∧ p4) ∧ p3) ∨ p4) ∧ True)))) ∧ p3) ∨ p5) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_148523533601652274178110758225 : ((((((p5 → (p4 → p1)) ∨ (p5 → p3)) → p3) → (p5 ∧ p4)) → ((((False → p1) → p4) ∧ False) ∨ True)) ∨ (((p1 → p3) → True) ∨ p2)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_622114935369530350825257999273 : ((((p2 ∧ (((p1 → ((p1 ∧ p1) ∨ p3)) → (((p1 ∨ p2) → p5) ∨ p4)) ∧ (((p3 ∧ (p4 ∨ (p1 → p3))) ∨ p4) → p2))) ∨ True) ∨ p3) ∧ True) := by
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
theorem thm_5_vars_138162184525790981893797004652 : ((p1 → (((p1 → ((p4 ∨ p3) → p4)) → (p4 → ((True ∨ (p4 ∧ ((p4 ∨ p4) → p1))) → True))) → (p5 ∨ False))) ∨ (False → (False ∨ p1))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_329544984997295720588552970845 : (True → ((p5 ∧ p5) ∨ (True ∧ (((False ∨ ((p5 ∨ (True → (p2 ∧ p4))) → p1)) ∧ True) ∨ ((p1 ∨ False) ∨ ((p2 ∧ p1) → (p2 → p1))))))) := by
  -- Implications on the right can always be decomposed.
  intro h1
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
  intro h2
  -- Implications on the right can always be decomposed.
  intro h3
  -- Conjunctions on the left can always be decomposed.
  let h4 := h2.left
  let h5 := h2.right
  -- One of the premise coincides with the conclusion.
  exact h5



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_336106269420179878645917102645 : (p1 → (((((((p5 → (p4 ∨ (False ∧ (False → (False ∧ p5))))) ∨ False) ∨ ((False ∧ True) ∨ p5)) ∨ (p5 → (p4 ∧ p1))) ∧ True) ∨ False) ∨ True)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_197465722799877865629137985495 : ((((False → (p5 → p4)) → p3) ∧ (p5 ∨ p1)) ∨ ((p5 → (((p3 ∧ (p5 ∧ ((p5 ∧ p3) ∨ False))) → p3) → True)) ∨ (p1 ∨ (p2 ∧ p1)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_246586395112056556724997982250 : ((p5 ∧ p2) ∨ ((p5 → ((False ∨ False) ∨ p3)) → (p1 ∨ ((False ∧ ((p1 → p1) ∧ (True ∧ p4))) ∨ ((True ∧ ((p4 ∨ True) ∨ p3)) ∨ True))))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
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
theorem thm_5_vars_675507047088833611368139800629 : (((((p5 → ((p3 ∧ ((((False ∨ p5) ∨ p2) → p3) ∧ ((False ∨ p5) ∨ (p1 ∧ True)))) → p3)) → p1) ∧ ((True → p3) ∨ (p3 → p3))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_120883524354433658503939873375 : (((((p2 → True) ∨ ((p5 ∨ (p3 ∧ True)) → True)) ∨ (True ∨ (p2 ∧ (((((True ∧ p5) ∧ True) ∨ p3) ∧ p2) ∨ p2)))) ∨ p1) → (p1 ∨ True)) := by
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
        -- True on the right can always be proven directly.
        apply True.intro
      case inr h5 =>
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
        -- Conjunctions on the left can always be decomposed.
        let h9 := h8.left
        let h10 := h8.right
        -- Disjunctions on the left can always be decomposed.
        cases h10
        case inl h11 =>
          -- Conjunctions on the left can always be decomposed.
          let h12 := h11.left
          let h13 := h11.right
          -- Disjunctions on the left can always be decomposed.
          cases h12
          case inl h14 =>
            -- Conjunctions on the left can always be decomposed.
            let h15 := h14.left
            let h16 := h14.right
            -- Conjunctions on the left can always be decomposed.
            let h17 := h15.left
            let h18 := h15.right
            -- Show the right disjunct based on <expert-advice>.
            apply Or.inr
            -- True on the right can always be proven directly.
            apply True.intro
          case inr h19 =>
            -- Show the right disjunct based on <expert-advice>.
            apply Or.inr
            -- True on the right can always be proven directly.
            apply True.intro
        case inr h20 =>
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- True on the right can always be proven directly.
          apply True.intro
  case inr h21 =>
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- One of the premise coincides with the conclusion.
    exact h21



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_44293439192151968933621040513 : ((((((p3 ∨ p4) → (p2 ∧ p3)) ∨ (True → ((p1 ∧ (p5 ∧ p5)) ∨ (p5 → p4)))) ∧ ((((p3 ∧ True) ∨ p2) ∧ p2) → p3)) → p5) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_197095790423434153172796924335 : (((p3 ∧ (p5 ∧ (False ∨ (p3 ∨ p2)))) ∨ p4) ∨ (p5 → (((p1 ∨ p1) ∨ (False → (p4 → ((False → ((p3 ∨ p5) ∨ p3)) → False)))) ∧ p5))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h2
  -- Implications on the right can always be decomposed.
  intro h3
  -- Implications on the right can always be decomposed.
  intro h4
  -- False on the left can always be used.
  apply False.elim h2
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_41638849229608058701515530200 : ((((p4 → (((p4 → p5) → p1) → (p5 → p4))) → (p5 ∨ ((p1 ∨ (True ∨ (p1 ∨ p5))) ∧ ((True ∨ (p4 → p1)) → True)))) ∨ p5) ∨ p2) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
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
  -- True on the right can always be proven directly.
  apply True.intro
  -- Implications on the right can always be decomposed.
  intro h2
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_206970044172789513883234143538 : ((((p3 ∨ (p2 → p2)) → p3) ∧ p2) → (True → ((((True ∨ False) → (p4 ∨ (False ∧ p5))) ∨ (p5 ∨ ((True ∨ p5) ∧ p1))) ∨ (True ∨ p4)))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Conjunctions on the left can always be decomposed.
  let h3 := h1.left
  let h4 := h1.right
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_316438738949460933524970667740 : (p3 ∨ (p1 ∨ (((p5 ∧ ((p4 → False) ∧ (p3 → p3))) ∨ ((((p4 ∨ p1) → True) ∧ p5) → (((True → p1) ∨ p2) ∧ p5))) ∨ (False → p1)))) := by
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



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_260243889634777878452010766472 : ((p2 → p3) → (((p1 → p2) ∧ ((True ∧ ((True → p2) ∨ p4)) ∧ (p3 → p1))) ∨ (((p4 → p1) ∧ False) → (p4 ∧ (p2 → (p2 ∨ p2)))))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h2
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Conjunctions on the left can always be decomposed.
  let h3 := h2.left
  let h4 := h2.right
  -- False on the left can always be used.
  apply False.elim h4
  -- Implications on the right can always be decomposed.
  intro h5
  -- Conjunctions on the left can always be decomposed.
  let h6 := h2.left
  let h7 := h2.right
  -- False on the left can always be used.
  apply False.elim h7



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_690991875143245842883585851689 : ((((((p2 → p1) → ((p2 ∧ (p1 → (False ∧ (p3 → p2)))) ∨ p3)) → (p5 ∨ p3)) → (((p2 ∧ p3) ∧ (p2 → (False → True))) → False)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_197483790657055029107131142082 : ((((p5 ∨ p5) → (p5 ∧ False)) ∧ (True ∨ p3)) ∨ ((p1 → ((p1 ∧ (True ∨ p5)) ∧ (p4 ∧ p1))) ∨ (((p4 ∧ (p5 ∨ False)) ∨ p2) ∨ True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_187156146717234276380143152412 : (((p2 → p4) ∨ (((p4 → (p1 ∧ p3)) → (True → True)) → p5)) → ((False → p1) ∧ (((False ∨ ((p2 → False) → True)) → (False ∧ p1)) → p2))) := by
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
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h4 =>
    -- We want to use the implication h3 based on <expert-advice>. So we show its premise.
    have h5 : (False ∨ ((p2 → False) → True)) := by
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Implications on the right can always be decomposed.
      intro h6
      -- True on the right can always be proven directly.
      apply True.intro
    -- We have shown the premise of h3, we can now drive its conclusion.
    let h7 := h3 h5
    -- We need to get the left conjuct of h7 based on <expert-advice>.
    let h8 := h7.left
    -- False on the left can always be used.
    apply False.elim h8
  case inr h9 =>
    -- We want to use the implication h3 based on <expert-advice>. So we show its premise.
    have h10 : (False ∨ ((p2 → False) → True)) := by
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Implications on the right can always be decomposed.
      intro h11
      -- True on the right can always be proven directly.
      apply True.intro
    -- We have shown the premise of h3, we can now drive its conclusion.
    let h12 := h3 h10
    -- We need to get the left conjuct of h12 based on <expert-advice>.
    let h13 := h12.left
    -- False on the left can always be used.
    apply False.elim h13



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_114177597800824956397253424096 : (((((((((p5 ∨ (p1 → p5)) ∨ p5) → p1) ∨ True) ∨ p4) ∧ ((p5 → False) → True)) → (p3 ∨ False)) → (p3 ∨ (p2 → p5))) ∨ (False ∨ p2)) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h2 : ((((((p5 ∨ (p1 → p5)) ∨ p5) → p1) ∨ True) ∨ p4) ∧ ((p5 → False) → True)) := by
    -- Conjunctions on the right can always be decomposed.
    apply And.intro
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro
    -- Implications on the right can always be decomposed.
    intro h3
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h4 := h1 h2
  -- Disjunctions on the left can always be decomposed.
  cases h4
  case inl h5 =>
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- One of the premise coincides with the conclusion.
    exact h5
  case inr h6 =>
    -- False on the left can always be used.
    apply False.elim h6



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_158952934336336907433531122009 : ((p2 ∨ ((p4 → p3) ∨ ((p3 ∧ (p4 ∨ (((p1 ∧ (p1 ∨ p1)) ∨ p5) ∨ (p4 ∨ False)))) ∨ p3))) ∨ (True ∨ ((p4 ∨ (False → p3)) → p2))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_186005543125088459325258890089 : (((True → (True ∧ (p1 → (True ∨ ((p4 → p4) ∨ p3))))) ∧ True) → (p2 ∨ ((True → ((p3 ∨ p2) → ((True → p2) → p5))) ∨ (False → p2)))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h4
  -- False on the left can always be used.
  apply False.elim h4



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_317659657904477101509515321788 : (p4 ∨ (((((True ∨ ((True → p3) ∨ (((p5 → True) ∨ ((False → (p1 → True)) ∨ ((p1 ∨ True) ∨ True))) ∨ p3))) ∧ p4) → p4) → False) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_226281911463023512835067336072 : (((p4 ∨ p1) ∨ False) ∨ ((True → (((p1 ∨ (p4 ∧ False)) → (p1 → p1)) → (((p1 ∧ p5) ∧ (p4 → (p1 ∧ p4))) → p4))) ∨ (False → p1))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_152764377646195313820911013946 : (((p4 → p4) ∨ (((p4 ∧ p3) ∨ True) → (((((p2 ∧ p4) ∧ (p1 ∧ p4)) ∨ False) ∨ p1) → (True → p5)))) → (p4 ∨ ((False ∨ False) ∨ True))) := by
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
theorem thm_5_vars_226004425501015577723606799628 : (((p4 ∧ False) ∨ p4) ∨ (p5 ∨ (((True ∧ p1) ∨ ((p2 → (True → ((p5 ∧ p2) → (p1 → True)))) ∨ p4)) ∨ (((p1 → False) ∧ p4) ∧ p1)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
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
  -- Implications on the right can always be decomposed.
  intro h2
  -- Implications on the right can always be decomposed.
  intro h3
  -- Implications on the right can always be decomposed.
  intro h4
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_299317133091615960743940933499 : (False ∨ (((((p1 → p2) ∧ False) ∧ (p1 ∧ False)) ∨ (((((((p5 ∧ p1) ∧ p1) → (p1 ∨ p5)) → p1) ∧ p5) ∧ (p5 ∧ p1)) ∧ p3)) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_41239910489964294659069908083 : ((((p1 → (p3 ∨ ((((p5 ∨ (False ∧ p4)) ∨ (p4 → True)) → (p1 ∧ (False ∨ False))) ∧ p5))) ∧ (p3 → (p4 ∧ (p2 → False)))) ∨ True) ∨ p1) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_607741132787759695336588211347 : (((((p1 ∨ ((((((False ∧ False) ∧ (p4 → (p4 ∧ True))) ∨ ((p4 ∧ p2) ∨ True)) ∨ p3) ∨ ((False ∨ True) ∨ p2)) → False)) ∧ False) ∨ p4) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_64773021092213627947845551208 : ((p2 ∨ ((((p3 ∨ p5) → (((True → (p4 ∧ (p4 ∧ (((p4 ∨ (p3 ∧ True)) ∧ (False ∨ p1)) ∧ p2)))) ∨ p4) ∨ False)) ∧ p2) ∨ False)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_182134994600194756860673368006 : (((p4 → (((p3 ∨ (p1 ∨ p1)) ∧ p5) ∨ (True ∧ True))) ∨ p4) ∧ ((p5 → (p5 ∨ p2)) ∧ (p5 ∨ (p5 → (p2 ∨ ((False → True) ∨ p4)))))) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
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
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h2
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- One of the premise coincides with the conclusion.
  exact h2
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h3
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h4
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_344723525094049582381174684526 : (p2 → (p3 → (((((p5 ∨ True) → ((p3 ∧ p1) ∧ p2)) → p5) ∧ (p4 ∧ ((False ∨ (((p5 ∧ p1) ∨ False) ∧ p4)) ∧ p3))) ∨ (p3 → p3)))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h3
  -- One of the premise coincides with the conclusion.
  exact h3



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_263976050909335471257943470470 : (True ∧ (((((p4 → p3) ∨ p5) ∧ (((True ∨ True) ∨ False) ∨ True)) → p1) ∨ ((p1 ∧ ((((p4 ∧ p5) ∧ p4) → (p1 → True)) ∧ p2)) ∨ True))) := by
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



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_259293627824568235710053654216 : ((False → p1) → (p1 ∨ (((((p5 → (((p2 → True) ∧ p5) ∧ (p5 ∧ (p4 ∨ p2)))) ∧ ((p5 → p4) → p3)) ∨ p2) ∧ (p4 → True)) ∨ True))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_607056943330543701693974448802 : ((((((p5 → (False → ((p1 ∧ (p2 ∨ (False ∧ (True → p2)))) ∧ p3))) → (((True ∧ ((p2 ∧ p1) ∨ p4)) → p3) → p2)) ∧ p4) ∨ p1) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_65249331993955321842383064675 : ((p3 ∨ ((((((p2 ∧ p4) ∧ (p1 → p4)) ∨ p2) ∧ ((p4 ∨ p3) ∨ (p4 → (p2 ∧ (False ∧ False))))) ∧ ((p5 ∨ True) ∧ p1)) → p4)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_114114374700932119936525685785 : (((p3 ∨ ((False ∧ (False ∧ (p5 ∧ (((p1 → (p3 → p1)) ∨ p5) ∨ (p2 → False))))) ∧ (p3 ∧ p3))) ∨ ((p5 ∧ p2) → True)) ∨ (p3 → True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_183916372492728097931393332294 : (((False ∧ (True ∧ ((p2 ∧ (p5 ∧ (p5 ∨ True))) ∧ False))) ∧ p4) ∨ ((False → (False ∧ (True ∧ (p5 ∨ p5)))) ∧ (p4 ∨ (True ∨ (p5 ∧ p2))))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- False on the left can always be used.
  apply False.elim h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- False on the left can always be used.
  apply False.elim h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_174951094428701375796174172184 : ((True ∧ (((p3 → ((p3 ∨ p5) ∧ (True ∨ p5))) ∨ (p1 ∧ (False ∧ p5))) ∨ True)) → (((p4 ∧ (p1 ∨ (p4 → p1))) ∨ (p5 → p4)) ∨ True)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- Disjunctions on the left can always be decomposed.
  cases h3
  case inl h4 =>
    -- Disjunctions on the left can always be decomposed.
    cases h4
    case inl h5 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- True on the right can always be proven directly.
      apply True.intro
    case inr h6 =>
      -- Conjunctions on the left can always be decomposed.
      let h7 := h6.left
      let h8 := h6.right
      -- Conjunctions on the left can always be decomposed.
      let h9 := h8.left
      let h10 := h8.right
      -- False on the left can always be used.
      apply False.elim h9
  case inr h11 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_209268983718781882783859733065 : ((True → (((p1 ∧ True) ∧ p5) ∧ True)) → (((True → False) ∧ ((p4 ∧ False) ∧ (p3 ∧ p2))) ∨ (((p4 → p5) ∧ (False ∧ p3)) → (p4 → p2)))) := by
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
  -- Conjunctions on the left can always be decomposed.
  let h6 := h5.left
  let h7 := h5.right
  -- False on the left can always be used.
  apply False.elim h6



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_345380853444893458268763137525 : (p3 → (((p1 ∧ (p4 → (((p1 ∧ (False ∧ False)) ∧ p3) ∨ ((p5 ∨ (p4 ∧ (((p1 ∧ p2) ∨ (p4 ∨ p2)) ∧ p3))) ∧ p3)))) ∨ False) ∨ p3)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_51511640834005938916335188097 : ((((p4 ∧ p2) ∧ (((p4 ∧ ((False → False) → (True → False))) ∧ False) → (False ∨ (p3 → p5)))) → (True → ((p5 ∨ (p1 ∨ p2)) ∨ p2))) ∨ p4) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
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
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h6



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_172535559165336617067119729678 : (((p3 → (p1 ∨ p3)) ∧ (((p2 ∨ ((True ∧ p5) → p3)) → (False → True)) → p4)) ∨ ((p4 → (p4 ∧ True)) ∨ (((p5 ∨ p4) ∨ p3) ∨ p5))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- One of the premise coincides with the conclusion.
  exact h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_49621407805818581293297236948 : ((((p2 ∧ (((p2 → False) ∧ True) ∨ (p4 ∧ p4))) → (p3 ∨ ((p4 → (True → (p2 → (p3 ∧ True)))) ∨ False))) → (p2 ∨ (p5 → p2))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_742311634382680328210037052294 : ((((p1 → p2) ∨ (p2 ∨ (p3 ∧ (((p5 → p3) → p1) ∨ (((p2 → p5) → ((p4 ∧ (p3 ∨ (False ∧ (p2 → p4)))) → False)) → p3))))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_64703813630369680809802595974 : ((p1 ∨ (p1 → (((p4 ∧ p1) ∧ ((False ∨ ((p5 ∧ (p2 ∧ ((p3 → (True → p3)) ∧ (p3 ∧ p3)))) ∧ (p5 → p5))) ∨ p2)) ∨ p1))) ∨ p4) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_115500703050419012688498024605 : (((((p4 → (p2 ∧ True)) → (True → p1)) → p3) → ((((p5 → (True ∧ p1)) ∨ p4) → ((p5 ∧ p3) ∧ (p5 ∨ p3))) ∧ p5)) ∨ (True ∨ p2)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_191364145705789839127487723972 : (((p5 ∨ p3) ∨ (p4 ∧ (p3 ∧ ((False → p2) ∧ False)))) ∨ (True ∨ ((((True ∨ p4) → (p2 ∨ False)) → (p1 ∧ ((p5 ∧ p5) → False))) ∨ p5))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_776409621529136937497622611571 : (((p1 ∨ (((((False → (p3 → (True ∨ (((p1 ∧ ((p3 ∧ p1) ∨ p3)) ∧ (p5 ∨ False)) → False)))) ∧ (False ∧ p4)) ∨ p5) ∨ p2) ∨ p1)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_175216109515077271415587272495 : ((False ∨ (p4 → (((((False → p3) ∨ p3) ∧ p1) ∧ True) ∨ ((p5 ∨ p1) ∧ p4)))) → (p5 ∨ (((p2 ∨ p1) → True) → ((p4 → p3) ∨ True)))) := by
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
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_245730828031523998631039841149 : ((p3 ∧ p2) ∨ ((p2 ∧ (((p3 ∧ p3) → (p4 ∧ (p2 ∨ False))) ∨ p5)) ∨ (((True → p2) → ((True ∨ p2) ∨ p3)) ∨ ((p1 → p2) ∧ p5)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_314828005954060822163892006655 : (p3 ∨ (((p5 → (((p4 ∨ ((p5 ∧ False) ∧ p3)) ∧ False) ∨ p1)) ∨ True) ∨ ((p2 ∨ (p3 ∨ p2)) ∨ ((((p2 ∨ p3) ∧ p1) ∧ p2) ∨ p4)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_157604099025509907723337955721 : (((((((False ∨ (((p3 ∧ p3) ∧ p1) → p4)) ∧ p2) ∨ False) ∨ p5) ∧ p1) ∧ ((p3 → True) → p3)) ∨ ((p3 → ((p3 ∨ p3) ∨ False)) ∨ p3)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_150254329224359169273239317476 : ((p3 → ((((p5 → (False ∨ p1)) → p3) → (False ∧ (True ∧ False))) ∨ (((True → False) → p3) → (p4 ∨ p3)))) ∨ (p3 → ((True → p4) ∨ p3))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_698756582305664205370334559202 : (((((p3 ∨ False) ∨ ((p4 ∨ (p2 ∧ (p5 → (True ∨ p5)))) ∨ p1)) ∨ ((p3 → (False → True)) ∧ (False → (p4 → (p2 → (p4 ∧ p3)))))) ∨ p2) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
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
  -- True on the right can always be proven directly.
  apply True.intro
  -- Implications on the right can always be decomposed.
  intro h3
  -- Implications on the right can always be decomposed.
  intro h4
  -- Implications on the right can always be decomposed.
  intro h5
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- False on the left can always be used.
  apply False.elim h3
  -- False on the left can always be used.
  apply False.elim h3
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_677413917604908212923625153604 : (((((((((p5 → p1) ∨ p4) → (True ∧ (p4 ∧ p5))) ∧ (p5 → ((p2 → p2) ∧ False))) → p5) ∨ p3) ∨ ((p1 ∨ (False ∨ p3)) ∧ p1)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_344436104090875085178742438340 : (p2 → (p5 ∨ (((p5 ∧ False) ∧ (p4 ∧ False)) ∨ (p2 ∧ (p5 ∨ (p4 → (False → ((((p4 → True) → p2) → (p3 ∨ (p2 ∧ False))) → p5)))))))) := by
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
  -- Implications on the right can always be decomposed.
  intro h2
  -- Implications on the right can always be decomposed.
  intro h3
  -- Implications on the right can always be decomposed.
  intro h4
  -- False on the left can always be used.
  apply False.elim h3



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_597129995378979862940580254409 : (((((p2 → (p4 → (False → (p2 ∨ p1)))) → ((p3 ∧ p3) ∨ ((p4 ∧ False) ∧ (p2 → (((p4 ∨ p5) → False) ∨ (p1 ∧ p3)))))) ∧ p1) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_59613288311340745071167161336 : (((p4 → p5) ∨ (p3 ∨ ((((False ∧ True) ∨ (True ∨ ((False ∨ p2) → (p1 ∨ (p3 ∨ ((p3 ∧ p3) → False)))))) → (p2 ∧ p4)) ∨ False))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_146674238983118428450226256052 : ((p1 → (((True ∧ (p3 ∨ (p3 → p4))) → ((True ∧ ((p1 ∧ p1) → False)) → (False ∧ (p3 ∧ False)))) ∨ False)) ∧ (((p5 ∧ False) → p4) ∧ True)) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h2
  -- Implications on the right can always be decomposed.
  intro h3
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Conjunctions on the left can always be decomposed.
  let h4 := h3.left
  let h5 := h3.right
  -- Conjunctions on the left can always be decomposed.
  let h6 := h2.left
  let h7 := h2.right
  -- Disjunctions on the left can always be decomposed.
  cases h7
  case inl h8 =>
    -- We want to use the implication h5 based on <expert-advice>. So we show its premise.
    have h9 : (p1 ∧ p1) := by
      -- Conjunctions on the right can always be decomposed.
      apply And.intro
      -- One of the premise coincides with the conclusion.
      exact h1
      -- One of the premise coincides with the conclusion.
      exact h1
    -- We have shown the premise of h5, we can now drive its conclusion.
    let h10 := h5 h9
    -- False on the left can always be used.
    apply False.elim h10
  case inr h11 =>
    -- We want to use the implication h5 based on <expert-advice>. So we show its premise.
    have h12 : (p1 ∧ p1) := by
      -- Conjunctions on the right can always be decomposed.
      apply And.intro
      -- One of the premise coincides with the conclusion.
      exact h1
      -- One of the premise coincides with the conclusion.
      exact h1
    -- We have shown the premise of h5, we can now drive its conclusion.
    let h13 := h5 h12
    -- False on the left can always be used.
    apply False.elim h13
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Conjunctions on the left can always be decomposed.
  let h14 := h3.left
  let h15 := h3.right
  -- Conjunctions on the left can always be decomposed.
  let h16 := h2.left
  let h17 := h2.right
  -- Disjunctions on the left can always be decomposed.
  cases h17
  case inl h18 =>
    -- One of the premise coincides with the conclusion.
    exact h18
  case inr h19 =>
    -- We want to use the implication h15 based on <expert-advice>. So we show its premise.
    have h20 : (p1 ∧ p1) := by
      -- Conjunctions on the right can always be decomposed.
      apply And.intro
      -- One of the premise coincides with the conclusion.
      exact h1
      -- One of the premise coincides with the conclusion.
      exact h1
    -- We have shown the premise of h15, we can now drive its conclusion.
    let h21 := h15 h20
    -- False on the left can always be used.
    apply False.elim h21
  -- Conjunctions on the left can always be decomposed.
  let h22 := h3.left
  let h23 := h3.right
  -- Conjunctions on the left can always be decomposed.
  let h24 := h2.left
  let h25 := h2.right
  -- Disjunctions on the left can always be decomposed.
  cases h25
  case inl h26 =>
    -- We want to use the implication h23 based on <expert-advice>. So we show its premise.
    have h27 : (p1 ∧ p1) := by
      -- Conjunctions on the right can always be decomposed.
      apply And.intro
      -- One of the premise coincides with the conclusion.
      exact h1
      -- One of the premise coincides with the conclusion.
      exact h1
    -- We have shown the premise of h23, we can now drive its conclusion.
    let h28 := h23 h27
    -- False on the left can always be used.
    apply False.elim h28
  case inr h29 =>
    -- We want to use the implication h23 based on <expert-advice>. So we show its premise.
    have h30 : (p1 ∧ p1) := by
      -- Conjunctions on the right can always be decomposed.
      apply And.intro
      -- One of the premise coincides with the conclusion.
      exact h1
      -- One of the premise coincides with the conclusion.
      exact h1
    -- We have shown the premise of h23, we can now drive its conclusion.
    let h31 := h23 h30
    -- False on the left can always be used.
    apply False.elim h31
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h32
  -- Conjunctions on the left can always be decomposed.
  let h33 := h32.left
  let h34 := h32.right
  -- False on the left can always be used.
  apply False.elim h34
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_61412521513546776863295926375 : ((p1 ∧ (((p4 → ((((p3 ∨ (True ∨ (p2 ∧ p4))) ∨ p4) ∨ (p5 ∨ ((p2 ∧ p5) ∨ p4))) ∧ (p1 ∨ (p1 → p4)))) ∧ p2) → p3)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_246219460928174915741675828040 : ((p4 ∧ p3) ∨ ((p3 ∧ (p2 ∧ ((p1 ∨ p1) ∧ False))) ∨ ((False ∧ ((p5 ∧ p2) ∧ p4)) → ((p5 → p5) ∨ (((p3 → p1) → p2) → p5))))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
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
theorem thm_5_vars_41061747322828338060787847399 : ((((p2 ∧ ((True ∧ False) → (((True → p2) ∧ p4) ∨ (((p2 ∨ p4) ∧ ((p5 ∨ p1) ∨ p4)) ∨ (p3 → p2))))) → (p1 ∨ p4)) ∨ p4) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_83370084273590337275331672634 : (((True ∧ (((((False → (p2 ∧ (p1 → p4))) ∧ False) → ((p5 ∧ p1) ∧ p4)) ∨ p2) ∧ p2)) ∧ (False ∨ ((p4 ∨ (False ∨ p4)) ∧ p4))) → p2) := by
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
  -- Disjunctions on the left can always be decomposed.
  cases h6
  case inl h8 =>
    -- Disjunctions on the left can always be decomposed.
    cases h3
    case inl h9 =>
      -- False on the left can always be used.
      apply False.elim h9
    case inr h10 =>
      -- Conjunctions on the left can always be decomposed.
      let h11 := h10.left
      let h12 := h10.right
      -- Disjunctions on the left can always be decomposed.
      cases h11
      case inl h13 =>
        -- One of the premise coincides with the conclusion.
        exact h7
      case inr h14 =>
        -- Disjunctions on the left can always be decomposed.
        cases h14
        case inl h15 =>
          -- False on the left can always be used.
          apply False.elim h15
        case inr h16 =>
          -- One of the premise coincides with the conclusion.
          exact h7
  case inr h17 =>
    -- Disjunctions on the left can always be decomposed.
    cases h3
    case inl h18 =>
      -- False on the left can always be used.
      apply False.elim h18
    case inr h19 =>
      -- Conjunctions on the left can always be decomposed.
      let h20 := h19.left
      let h21 := h19.right
      -- Disjunctions on the left can always be decomposed.
      cases h20
      case inl h22 =>
        -- One of the premise coincides with the conclusion.
        exact h7
      case inr h23 =>
        -- Disjunctions on the left can always be decomposed.
        cases h23
        case inl h24 =>
          -- False on the left can always be used.
          apply False.elim h24
        case inr h25 =>
          -- One of the premise coincides with the conclusion.
          exact h7



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_183949218597731012220581320976 : (((p3 ∨ (p5 → ((p3 → ((False ∧ p1) ∧ p1)) → False))) ∧ p4) ∨ (((False → p2) ∧ True) → ((p5 → False) → (p3 → ((True → False) → False))))) := by
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
  -- Conjunctions on the left can always be decomposed.
  let h5 := h1.left
  let h6 := h1.right
  -- We want to use the implication h4 based on <expert-advice>. So we show its premise.
  have h7 : True := by
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h4, we can now drive its conclusion.
  let h8 := h4 h7
  -- False on the left can always be used.
  apply False.elim h8



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_40382316467853435781599865234 : ((((((p5 → (False ∨ (((p2 ∧ (False ∧ p1)) ∨ ((p1 → p4) → p2)) ∨ (p4 ∨ (p4 → p2))))) ∧ p2) ∨ (p4 → p4)) ∨ p4) ∨ True) ∨ p3) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_42541707233099215699784008532 : (((p1 ∨ (((p5 ∨ False) ∧ (p2 → (True → (p5 → (False ∨ ((p1 ∨ (p5 ∨ p5)) ∧ p4)))))) ∨ (((p3 ∧ p3) ∧ p1) → p1))) ∨ p5) ∨ False) := by
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
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- Conjunctions on the left can always be decomposed.
  let h4 := h2.left
  let h5 := h2.right
  -- One of the premise coincides with the conclusion.
  exact h3



