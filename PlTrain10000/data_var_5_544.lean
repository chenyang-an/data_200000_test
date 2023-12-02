variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_56548427624930871727081381999 : (((p2 ∨ (False → (True → p4))) → ((((p2 ∨ (p2 ∨ ((p2 ∨ p1) → (p5 ∨ ((p4 ∧ p2) ∧ p4))))) ∨ True) ∧ (p1 ∨ p5)) ∨ True)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_177715740857458792018431564688 : ((((p2 ∨ ((p5 → (p4 ∨ False)) ∨ False)) ∨ ((p3 → p2) ∧ p4)) ∧ p2) ∨ ((p3 → ((True ∨ True) ∨ True)) ∨ (((p4 → p2) ∧ p4) ∧ True))) := by
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
theorem thm_5_vars_52271782247639340440078014340 : (((False → ((p4 ∨ (True → ((p1 → p5) ∧ False))) ∨ (((False ∧ True) ∧ True) → p1))) → ((((False → (False → p1)) ∨ True) ∧ p3) → False)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_603517327150140366904641147503 : ((((p3 ∨ ((p1 ∨ ((p2 ∨ p2) ∨ p5)) ∧ ((((p5 → (False → p2)) ∨ True) → p5) ∧ ((True ∨ ((p1 → p4) → p1)) ∨ p4)))) ∧ p5) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_136467567033765470299711037464 : ((((p4 ∧ p4) ∧ False) ∧ (False ∧ ((((((p2 ∨ p2) ∧ (True → (p3 ∧ p1))) ∨ (p3 ∧ True)) → p3) ∧ p2) ∧ p4))) ∨ ((False ∨ p4) → p4)) := by
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
    -- One of the premise coincides with the conclusion.
    exact h3



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_4232474147341185230413877508 : (p5 ∨ ((((p5 ∨ p5) ∨ False) ∧ (True ∧ p2)) ∨ ((((p5 → p1) ∨ (p4 → p3)) ∨ (((p3 → p5) ∨ (p1 ∨ p1)) → True)) ∧ True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_119517608604532570749502540440 : ((p5 → ((((p5 → (((True ∧ True) ∨ True) ∧ (p2 ∧ p2))) ∨ (((p2 → True) ∨ (p2 → p1)) → (p4 ∧ False))) ∨ True) ∨ p3)) ∨ (p5 ∨ False)) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_674489559023253063935978142975 : ((((p4 ∨ (((p4 ∧ p5) ∧ True) → ((False ∧ p4) → (p1 ∨ (True ∨ ((p1 ∨ (p5 ∨ p3)) ∨ (p1 → p2))))))) → ((p2 ∨ p3) ∨ True)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_126165903779132246657549340802 : ((True ∧ (p5 ∧ ((p2 ∨ (p5 ∧ (False → (p1 → p4)))) ∨ (((((p5 ∨ p1) → False) ∨ p1) ∨ (p5 → p4)) → (False ∨ p2))))) → (p4 → p4)) := by
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
  -- Disjunctions on the left can always be decomposed.
  cases h6
  case inl h7 =>
    -- Disjunctions on the left can always be decomposed.
    cases h7
    case inl h8 =>
      -- One of the premise coincides with the conclusion.
      exact h2
    case inr h9 =>
      -- Conjunctions on the left can always be decomposed.
      let h10 := h9.left
      let h11 := h9.right
      -- One of the premise coincides with the conclusion.
      exact h2
  case inr h12 =>
    -- One of the premise coincides with the conclusion.
    exact h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_166006690302604284244805409498 : (((False ∨ p1) ∨ (True ∧ ((True ∧ ((p3 ∨ False) ∨ (p2 ∨ ((p5 ∨ p1) → p5)))) ∨ p4))) ∨ (p5 → ((p3 → True) ∧ ((p4 ∧ p5) → p5)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h2
  -- True on the right can always be proven directly.
  apply True.intro
  -- Implications on the right can always be decomposed.
  intro h3
  -- Conjunctions on the left can always be decomposed.
  let h4 := h3.left
  let h5 := h3.right
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_167822095498007383688454111956 : (((True ∨ ((((p2 ∨ p2) ∧ (p1 → p4)) ∧ False) → p5)) ∧ (p5 ∧ (p2 → (True → p5)))) → (p4 ∨ (True ∧ (p5 ∨ (True ∨ (p1 ∨ False)))))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- Disjunctions on the left can always be decomposed.
  cases h2
  case inl h4 =>
    -- Conjunctions on the left can always be decomposed.
    let h5 := h3.left
    let h6 := h3.right
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
  case inr h7 =>
    -- Conjunctions on the left can always be decomposed.
    let h8 := h3.left
    let h9 := h3.right
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
theorem thm_5_vars_152022053793189622447422597790 : ((((p5 ∨ ((p5 ∧ (False → p4)) → (p1 ∨ False))) ∨ p4) ∧ (((p2 → True) ∧ (p1 ∧ p1)) → (False ∨ p3))) → ((p4 → (p1 ∨ p5)) ∨ True)) := by
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
theorem thm_5_vars_328696906585991579084776558616 : (True → (((True → (p1 ∨ ((p5 → p2) ∨ (False ∧ (False ∧ p5))))) ∨ p5) ∨ (((p1 ∨ p1) ∨ p4) ∨ (p2 ∨ ((p3 ∨ (p2 → p1)) → True))))) := by
  -- Implications on the right can always be decomposed.
  intro h1
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



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_157266423265919486404189230890 : (((((p4 → False) ∨ p2) ∧ (False ∨ (((p1 ∧ p2) → p1) ∧ (p2 ∨ ((p2 → p2) → False))))) → False) ∨ (p3 ∨ (p4 → ((p3 → p1) → p4)))) := by
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
theorem thm_5_vars_248805362727923157786617852879 : ((p3 ∨ p4) ∨ ((((((True → True) ∧ (p4 ∧ False)) → False) ∧ (p3 ∧ p3)) ∨ ((((False → p4) ∧ p3) → ((p2 → p1) ∨ p5)) ∨ p5)) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_314755224714936076171523563490 : (p3 ∨ ((p2 ∧ ((((p3 ∧ p1) → p2) ∧ (p1 ∨ (p4 → True))) ∨ (p1 ∧ p1))) ∨ (((p4 → False) ∨ (True → (p5 → (True ∨ p5)))) → True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_181124567178424102386976695110 : ((True ∧ ((p1 ∨ p4) ∨ ((p2 ∧ p4) → (p5 ∨ ((p3 ∨ p2) ∨ p5))))) → (((((p2 → p2) ∧ ((p2 → False) → p1)) ∨ p1) ∧ p5) ∨ True)) := by
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
theorem thm_5_vars_135701429035547708453342756973 : ((((((p4 ∨ False) → False) ∧ p5) → ((((p3 ∧ True) ∨ p4) ∧ False) ∨ p4)) ∧ (p3 ∨ (((p1 → p2) ∨ p2) ∧ p1))) ∨ (True ∨ (p4 ∨ p4))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_15858869448104711344285075806 : ((((p4 → p4) → ((((p5 ∧ (((True ∨ (p1 ∧ p2)) → (p4 ∧ p1)) → ((p4 → p3) → p5))) → p2) ∨ p3) ∧ False)) → (p2 → p5)) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h3 : (p4 → p4) := by
    -- Implications on the right can always be decomposed.
    intro h4
    -- One of the premise coincides with the conclusion.
    exact h4
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h5 := h1 h3
  -- We need to get the right conjuct of h5 based on <expert-advice>.
  let h6 := h5.right
  -- False on the left can always be used.
  apply False.elim h6
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_342319870691377943195390253382 : (p2 → ((((p2 ∨ (p1 → p3)) ∨ ((p3 ∧ (p1 → (False ∨ p1))) ∨ (p1 → p3))) → (p1 ∨ p1)) → (p1 ∨ (p3 → ((p3 → p3) → p1))))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
  have h3 : ((p2 ∨ (p1 → p3)) ∨ ((p3 ∧ (p1 → (False ∨ p1))) ∨ (p1 → p3))) := by
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- One of the premise coincides with the conclusion.
    exact h1
  -- We have shown the premise of h2, we can now drive its conclusion.
  let h4 := h2 h3
  -- Disjunctions on the left can always be decomposed.
  cases h4
  case inl h5 =>
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- One of the premise coincides with the conclusion.
    exact h5
  case inr h6 =>
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- One of the premise coincides with the conclusion.
    exact h6



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_233065740062407156648981711312 : ((p4 ∧ (p3 ∨ p3)) → (((p2 ∨ True) → ((((p4 ∨ ((False ∨ p5) ∨ ((True → p2) ∨ p1))) ∧ (True ∧ True)) → p4) → (p4 ∧ False))) → p5)) := by
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
    -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
    have h6 : (p2 ∨ True) := by
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- True on the right can always be proven directly.
      apply True.intro
    -- We have shown the premise of h2, we can now drive its conclusion.
    let h7 := h2 h6
    -- We want to use the implication h7 based on <expert-advice>. So we show its premise.
    have h8 : (((p4 ∨ ((False ∨ p5) ∨ ((True → p2) ∨ p1))) ∧ (True ∧ True)) → p4) := by
      -- Implications on the right can always be decomposed.
      intro h9
      -- Conjunctions on the left can always be decomposed.
      let h10 := h9.left
      let h11 := h9.right
      -- Disjunctions on the left can always be decomposed.
      cases h10
      case inl h12 =>
        -- Conjunctions on the left can always be decomposed.
        let h13 := h11.left
        let h14 := h11.right
        -- One of the premise coincides with the conclusion.
        exact h12
      case inr h15 =>
        -- Disjunctions on the left can always be decomposed.
        cases h15
        case inl h16 =>
          -- Disjunctions on the left can always be decomposed.
          cases h16
          case inl h17 =>
            -- False on the left can always be used.
            apply False.elim h17
          case inr h18 =>
            -- Conjunctions on the left can always be decomposed.
            let h19 := h11.left
            let h20 := h11.right
            -- One of the premise coincides with the conclusion.
            exact h3
        case inr h21 =>
          -- Disjunctions on the left can always be decomposed.
          cases h21
          case inl h22 =>
            -- Conjunctions on the left can always be decomposed.
            let h23 := h11.left
            let h24 := h11.right
            -- One of the premise coincides with the conclusion.
            exact h3
          case inr h25 =>
            -- Conjunctions on the left can always be decomposed.
            let h26 := h11.left
            let h27 := h11.right
            -- One of the premise coincides with the conclusion.
            exact h3
    -- We have shown the premise of h7, we can now drive its conclusion.
    let h28 := h7 h8
    -- We need to get the right conjuct of h28 based on <expert-advice>.
    let h29 := h28.right
    -- False on the left can always be used.
    apply False.elim h29
  case inr h30 =>
    -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
    have h31 : (p2 ∨ True) := by
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- True on the right can always be proven directly.
      apply True.intro
    -- We have shown the premise of h2, we can now drive its conclusion.
    let h32 := h2 h31
    -- We want to use the implication h32 based on <expert-advice>. So we show its premise.
    have h33 : (((p4 ∨ ((False ∨ p5) ∨ ((True → p2) ∨ p1))) ∧ (True ∧ True)) → p4) := by
      -- Implications on the right can always be decomposed.
      intro h34
      -- Conjunctions on the left can always be decomposed.
      let h35 := h34.left
      let h36 := h34.right
      -- Disjunctions on the left can always be decomposed.
      cases h35
      case inl h37 =>
        -- Conjunctions on the left can always be decomposed.
        let h38 := h36.left
        let h39 := h36.right
        -- One of the premise coincides with the conclusion.
        exact h37
      case inr h40 =>
        -- Disjunctions on the left can always be decomposed.
        cases h40
        case inl h41 =>
          -- Disjunctions on the left can always be decomposed.
          cases h41
          case inl h42 =>
            -- False on the left can always be used.
            apply False.elim h42
          case inr h43 =>
            -- Conjunctions on the left can always be decomposed.
            let h44 := h36.left
            let h45 := h36.right
            -- One of the premise coincides with the conclusion.
            exact h3
        case inr h46 =>
          -- Disjunctions on the left can always be decomposed.
          cases h46
          case inl h47 =>
            -- Conjunctions on the left can always be decomposed.
            let h48 := h36.left
            let h49 := h36.right
            -- One of the premise coincides with the conclusion.
            exact h3
          case inr h50 =>
            -- Conjunctions on the left can always be decomposed.
            let h51 := h36.left
            let h52 := h36.right
            -- One of the premise coincides with the conclusion.
            exact h3
    -- We have shown the premise of h32, we can now drive its conclusion.
    let h53 := h32 h33
    -- We need to get the right conjuct of h53 based on <expert-advice>.
    let h54 := h53.right
    -- False on the left can always be used.
    apply False.elim h54



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_166242589245375467802364530325 : ((p2 ∧ (p4 → ((((True ∨ (False → ((False ∨ True) → p2))) → (p3 ∨ p3)) ∨ True) ∧ p1))) ∨ ((((True ∧ (p4 ∧ p5)) ∨ False) ∧ True) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_113418328061234580553236640220 : (((((((True ∨ (p1 ∧ p5)) → p2) ∧ False) ∧ ((False ∨ (p3 → (p2 → False))) ∧ ((p1 → True) → p5))) ∧ p1) ∨ (p5 ∨ p5)) ∨ (p3 → p3)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_309383365517383274884286815077 : (p2 ∨ ((False ∧ (p5 ∧ (((p3 ∧ (True ∧ ((False → (p5 ∧ p1)) ∧ ((p4 ∧ False) ∨ p2)))) → ((False → p5) → p1)) ∨ True))) ∨ (p5 → p5))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_300710454105049894565654503127 : (False ∨ (((True ∧ ((((p4 → p3) → p3) → (p3 → p3)) ∧ (p5 → (p5 ∧ p3)))) ∧ (p2 ∨ p1)) → (p5 ∨ (True → ((p1 ∨ False) ∨ p2))))) := by
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
  let h6 := h5.left
  let h7 := h5.right
  -- Disjunctions on the left can always be decomposed.
  cases h3
  case inl h8 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h9
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h8
  case inr h10 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h11
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- One of the premise coincides with the conclusion.
    exact h10



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_149486131381314842399105728102 : ((p1 ∧ (((False → ((((p3 → p5) → p4) → ((((p4 ∨ p3) ∨ False) ∧ p2) ∧ False)) ∧ True)) → p1) ∧ True)) ∨ (True → ((True ∧ p5) → p5))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Conjunctions on the left can always be decomposed.
  let h3 := h2.left
  let h4 := h2.right
  -- One of the premise coincides with the conclusion.
  exact h4



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_50861109446316927905965761643 : (((((False ∨ (False ∨ (True ∨ (p3 → p4)))) → (((p1 ∨ True) ∧ (p3 ∨ p2)) ∧ True)) ∨ p4) ∧ (((False ∧ p3) ∨ (p1 → False)) ∨ False)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_61987513005906366715383187361 : ((p2 ∧ ((((False ∨ p1) → (p4 → p1)) → p4) ∧ ((False ∧ (p3 ∨ True)) → (((True ∨ (False ∨ (p1 → False))) ∨ (True → True)) ∧ p4)))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_740956791032047389260387008082 : ((((p3 ∨ p3) ∨ ((False ∧ (((p4 ∨ (p1 ∧ p2)) → (((p1 ∨ False) ∨ p4) ∧ p5)) ∧ p2)) ∧ (p5 ∨ (((False ∧ False) ∧ False) ∧ p3)))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_76239634396666633600284911330 : (((((p2 ∨ False) → (((((p2 ∨ (False → (p4 ∧ p3))) → (p3 ∧ (p1 ∧ p5))) ∧ False) ∨ (True ∨ p1)) ∨ p5)) ∧ (False → True)) → False) → p2) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h2 : (((p2 ∨ False) → (((((p2 ∨ (False → (p4 ∧ p3))) → (p3 ∧ (p1 ∧ p5))) ∧ False) ∨ (True ∨ p1)) ∨ p5)) ∧ (False → True)) := by
    -- Conjunctions on the right can always be decomposed.
    apply And.intro
    -- Implications on the right can always be decomposed.
    intro h3
    -- Disjunctions on the left can always be decomposed.
    cases h3
    case inl h4 =>
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- True on the right can always be proven directly.
      apply True.intro
    case inr h5 =>
      -- False on the left can always be used.
      apply False.elim h5
    -- Implications on the right can always be decomposed.
    intro h6
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h7 := h1 h2
  -- False on the left can always be used.
  apply False.elim h7



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_300415799976751342778943863401 : (False ∨ ((p3 → ((True → True) → ((((p1 ∧ ((True ∧ p4) → True)) ∧ True) ∨ (p1 ∧ (p5 ∨ (p4 ∧ p3)))) ∧ p1))) ∨ (p5 → (p4 ∨ p5)))) := by
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
theorem thm_5_vars_345513839476355988088183271372 : (p3 → (((((True ∧ p2) ∨ p3) → ((p5 ∨ p2) → ((p4 ∧ (p5 ∧ p5)) ∧ p5))) → (p5 ∧ (p5 → ((p2 → p5) ∨ (p1 ∨ True))))) ∨ p3)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_306233852563447265286720083452 : (p1 ∨ (((p2 ∨ p1) → False) → ((p5 → p5) → (((True → ((True ∨ p2) → (p3 ∨ (p3 ∨ (p1 → (p2 ∨ p3)))))) → (p2 → p3)) ∨ True)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_355829076128917363293781929273 : (p5 → (((((p4 ∧ (((p4 → (((p5 ∨ p3) ∨ False) → False)) ∨ (p4 ∧ p3)) → p4)) ∨ (p2 ∨ True)) ∨ True) ∧ p4) ∨ (True → (p5 → True)))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h2
  -- Implications on the right can always be decomposed.
  intro h3
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_157983051197133121577465796718 : (((((p2 ∨ (p1 ∧ p2)) ∧ (p3 ∧ True)) ∨ p1) → ((((False ∧ (False ∨ p2)) ∨ p5) ∧ p4) ∧ False)) ∨ ((True ∧ ((p2 → p4) → p1)) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_247313482158470575536921551872 : ((False ∨ False) ∨ (((False ∨ (p3 ∧ p5)) → p3) ∧ (((((((p5 → False) → (p2 → p3)) → False) ∧ p1) ∨ (p3 → p2)) ∧ True) ∨ (p4 ∨ True)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
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
    -- One of the premise coincides with the conclusion.
    exact h4
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_173770273446794533040610002344 : ((((False ∧ (p2 ∧ p1)) → (((((p1 ∧ False) ∨ p3) ∧ p2) ∧ p2) → p1)) ∨ p3) → ((True ∧ (p3 ∨ p1)) → (((p4 ∧ p3) ∧ p2) ∨ True))) := by
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
    cases h1
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
  case inr h8 =>
    -- Disjunctions on the left can always be decomposed.
    cases h1
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



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_315856276287789438440346516009 : (p3 ∨ ((p3 → True) → (((((p3 ∨ (p1 ∨ p3)) ∨ (((((p4 ∨ p1) → p5) ∧ p3) ∧ p2) ∨ True)) ∨ p5) ∧ (p2 ∨ p2)) → (p5 → p5)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Implications on the right can always be decomposed.
  intro h3
  -- Conjunctions on the left can always be decomposed.
  let h4 := h2.left
  let h5 := h2.right
  -- Disjunctions on the left can always be decomposed.
  cases h4
  case inl h6 =>
    -- Disjunctions on the left can always be decomposed.
    cases h6
    case inl h7 =>
      -- Disjunctions on the left can always be decomposed.
      cases h7
      case inl h8 =>
        -- Disjunctions on the left can always be decomposed.
        cases h5
        case inl h9 =>
          -- One of the premise coincides with the conclusion.
          exact h3
        case inr h10 =>
          -- One of the premise coincides with the conclusion.
          exact h3
      case inr h11 =>
        -- Disjunctions on the left can always be decomposed.
        cases h11
        case inl h12 =>
          -- Disjunctions on the left can always be decomposed.
          cases h5
          case inl h13 =>
            -- One of the premise coincides with the conclusion.
            exact h3
          case inr h14 =>
            -- One of the premise coincides with the conclusion.
            exact h3
        case inr h15 =>
          -- Disjunctions on the left can always be decomposed.
          cases h5
          case inl h16 =>
            -- One of the premise coincides with the conclusion.
            exact h3
          case inr h17 =>
            -- One of the premise coincides with the conclusion.
            exact h3
    case inr h18 =>
      -- Disjunctions on the left can always be decomposed.
      cases h18
      case inl h19 =>
        -- Conjunctions on the left can always be decomposed.
        let h20 := h19.left
        let h21 := h19.right
        -- Conjunctions on the left can always be decomposed.
        let h22 := h20.left
        let h23 := h20.right
        -- Disjunctions on the left can always be decomposed.
        cases h5
        case inl h24 =>
          -- One of the premise coincides with the conclusion.
          exact h3
        case inr h25 =>
          -- One of the premise coincides with the conclusion.
          exact h3
      case inr h26 =>
        -- Disjunctions on the left can always be decomposed.
        cases h5
        case inl h27 =>
          -- One of the premise coincides with the conclusion.
          exact h3
        case inr h28 =>
          -- One of the premise coincides with the conclusion.
          exact h3
  case inr h29 =>
    -- Disjunctions on the left can always be decomposed.
    cases h5
    case inl h30 =>
      -- One of the premise coincides with the conclusion.
      exact h29
    case inr h31 =>
      -- One of the premise coincides with the conclusion.
      exact h29



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_37344264029414024491325874007 : (((((p4 ∨ (((p1 ∨ p2) ∧ p2) ∨ (p1 ∨ ((p1 ∨ False) → ((False ∧ p2) ∧ (p2 ∧ (p3 ∧ (p4 → False)))))))) ∧ p5) ∨ p4) ∧ p1) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_216808759296012486245461653156 : (((p2 ∧ (p1 ∨ p1)) ∧ p1) → ((((p2 ∨ (((True ∨ p1) → p4) ∨ True)) ∨ False) → ((p2 ∨ (p5 ∨ p1)) ∧ ((p4 ∧ p5) ∧ p2))) ∨ True)) := by
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
theorem thm_5_vars_732426048248400393977833780946 : ((((False ∧ p3) ∧ ((p3 → p4) → (((p4 ∧ True) ∨ False) ∧ (p3 ∧ (((p3 ∧ p4) ∨ (True ∧ ((True → p2) ∨ p1))) ∧ (p2 ∨ True)))))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_140916728354279624856674061297 : ((((True ∨ False) → ((p3 → p4) → (p1 ∨ (True ∨ False)))) ∧ (False ∨ (((p5 → p5) → (p4 → (False ∧ p2))) ∧ p1))) → (p4 ∨ (p2 → p2))) := by
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
    -- Conjunctions on the left can always be decomposed.
    let h6 := h5.left
    let h7 := h5.right
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h8
    -- One of the premise coincides with the conclusion.
    exact h8



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_38191504702659287979427089879 : ((((((True ∨ ((False → ((p3 ∨ p1) ∨ (p4 → p3))) ∧ (p4 → (p5 → (p5 ∨ True))))) ∧ p4) ∧ p1) → (p4 ∧ (p3 ∨ p5))) ∧ p5) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_150684475487993601394318230698 : (((p2 → (((p2 → p3) ∨ p3) ∨ (((p5 ∧ p3) ∧ (((True ∨ False) ∨ True) → (p3 → p3))) ∨ True))) ∧ p5) → (True ∧ ((p5 → p1) ∨ True))) := by
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
theorem thm_5_vars_317781728826689439113787664056 : (p4 ∨ ((((p4 → True) ∧ ((p1 ∧ ((p2 ∧ p5) ∧ p4)) → (p1 ∧ p3))) ∨ (p4 ∧ (((p5 ∨ p5) ∨ p5) ∨ (False ∨ (p2 ∧ p4))))) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_134030716160571796796174834270 : ((((((p5 ∧ ((p5 → p4) ∧ (p2 ∨ p4))) ∧ ((p4 ∨ (p3 → (p2 ∨ p4))) ∧ p3)) ∨ (p3 → p5)) ∨ True) ∨ True) ∨ (p2 ∧ (True ∨ p2))) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_46255539465063329243056078745 : (((((p4 ∧ ((((p2 ∨ p1) ∨ (p5 → p2)) ∨ (True ∧ True)) ∨ ((p5 ∧ True) ∨ p3))) ∨ (p3 ∧ p1)) → (p3 ∨ p4)) ∧ (True ∨ True)) ∨ p5) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
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
          cases h7
          case inl h8 =>
            -- Show the right disjunct based on <expert-advice>.
            apply Or.inr
            -- One of the premise coincides with the conclusion.
            exact h3
          case inr h9 =>
            -- Show the right disjunct based on <expert-advice>.
            apply Or.inr
            -- One of the premise coincides with the conclusion.
            exact h3
        case inr h10 =>
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- One of the premise coincides with the conclusion.
          exact h3
      case inr h11 =>
        -- Conjunctions on the left can always be decomposed.
        let h12 := h11.left
        let h13 := h11.right
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- One of the premise coincides with the conclusion.
        exact h3
    case inr h14 =>
      -- Disjunctions on the left can always be decomposed.
      cases h14
      case inl h15 =>
        -- Conjunctions on the left can always be decomposed.
        let h16 := h15.left
        let h17 := h15.right
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- One of the premise coincides with the conclusion.
        exact h3
      case inr h18 =>
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- One of the premise coincides with the conclusion.
        exact h18
  case inr h19 =>
    -- Conjunctions on the left can always be decomposed.
    let h20 := h19.left
    let h21 := h19.right
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- One of the premise coincides with the conclusion.
    exact h20
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_208039748410504324549478082805 : (((p3 ∧ (True ∨ p5)) ∨ (p3 → True)) → (p4 → (((False → (True ∨ True)) → (True → (p3 ∨ False))) → (((False ∧ (p3 → p3)) ∨ p1) ∨ True)))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Implications on the right can always be decomposed.
  intro h3
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h4 =>
    -- Conjunctions on the left can always be decomposed.
    let h5 := h4.left
    let h6 := h4.right
    -- Disjunctions on the left can always be decomposed.
    cases h6
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
  case inr h9 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_55572131690609570197673113208 : (((True ∨ (p1 → ((True ∧ p5) → True))) → (((((p4 → p2) ∨ p3) ∧ p2) → (((p1 → ((p3 → p3) ∨ p5)) → p3) ∧ p2)) ∨ True)) ∨ p4) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
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
theorem thm_5_vars_625657818675103754042764023609 : ((((p1 → ((p2 ∧ (p5 ∧ ((p1 ∧ (p1 ∧ ((False → p4) → False))) ∨ ((((p4 ∨ True) ∧ p5) ∨ p4) ∧ p1)))) ∨ (p1 ∨ p2))) ∨ p3) ∨ False) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- One of the premise coincides with the conclusion.
  exact h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_111836314238198812264127747522 : ((((((p5 ∧ False) → ((((False ∨ (p5 ∧ (True → True))) → p3) ∨ p5) ∨ True)) → (p4 ∨ p3)) ∨ (p5 → (p5 ∨ True))) ∨ False) ∨ (True → p4)) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_113862609678892563694061514692 : (((p3 → ((True ∧ p2) ∧ ((((((p4 ∧ (p4 ∨ p4)) ∧ p1) ∨ (True ∧ p1)) ∨ (p5 ∧ p4)) ∧ p2) ∧ False))) → (True ∧ p1)) ∨ (True ∨ p5)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_227981684261563326014357094299 : ((p3 ∧ (p2 ∨ p2)) ∨ (((p4 ∧ ((p1 ∨ (((p1 ∨ (p1 → p4)) ∧ (p4 → ((p2 ∧ False) → p3))) ∨ p3)) ∨ False)) ∨ True) ∨ (p4 ∧ p4))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_748155259087843493734435374920 : ((((p1 → p4) → (((p5 ∧ (p1 ∨ p4)) → (p2 ∧ ((((False ∨ False) ∧ ((p5 ∨ p4) ∧ True)) ∨ p1) ∨ (True → p5)))) ∨ (True ∨ p4))) ∨ p3) ∧ True) := by
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
theorem thm_5_vars_159290985832897160151062980890 : ((p4 → (False ∧ (((p4 → ((((True ∧ p3) → p2) ∧ ((p5 ∨ p3) ∨ p3)) ∧ p5)) → p3) ∧ p2))) ∨ (False ∨ (False → (p4 → (False ∨ True))))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_41554640996714408193020161905 : ((((((((True ∧ p5) ∧ False) → True) ∨ (p1 ∨ True)) ∨ p4) → (p1 ∨ (((((p1 → p4) ∧ p3) ∨ p3) → (True ∧ p3)) → p5))) ∨ False) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_179161368174773423748453990420 : ((p2 ∧ (((True ∧ p2) ∨ p2) ∧ ((p5 ∨ (p2 ∨ (p5 → True))) ∨ True))) ∨ (p2 → ((p3 ∨ ((p3 ∧ p5) ∨ (False → (p5 → p4)))) ∨ False))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h2
  -- Implications on the right can always be decomposed.
  intro h3
  -- False on the left can always be used.
  apply False.elim h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_113205102962532425806141551490 : ((((((p5 ∧ (p1 ∨ (True ∨ (p3 ∧ (((p4 → p4) → p3) ∧ p2))))) → (p5 → False)) → (False ∧ p3)) ∨ p3) ∧ (p3 → p4)) ∨ (p3 → True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_46998150680763731682892336986 : ((((((p3 ∨ (p3 ∧ p2)) → p5) ∨ (p5 ∨ ((p5 → (((p2 → p2) ∧ p3) ∨ p5)) ∧ (p5 → (True ∧ p5))))) → False) ∨ (p3 → p1)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_310122775498185287033158998643 : (p2 ∨ ((((((p4 → p5) → p1) ∨ (True ∧ False)) ∨ p4) → (p4 ∨ (p2 ∧ p2))) ∨ (p5 → (p5 ∧ ((p1 ∨ p3) ∨ (p1 → (p4 → p1))))))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
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
  -- One of the premise coincides with the conclusion.
  exact h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_306202120193542508684127392482 : (p1 ∨ ((p3 → (p5 ∧ True)) ∨ ((((p4 ∨ (False → p3)) ∧ (((p5 → p5) → p3) ∧ (p1 ∧ (p1 ∧ p4)))) → ((p2 → p5) ∨ p3)) ∧ True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h1
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
    -- Conjunctions on the left can always be decomposed.
    let h9 := h8.left
    let h10 := h8.right
    -- We want to use the implication h5 based on <expert-advice>. So we show its premise.
    have h11 : (p5 → p5) := by
      -- Implications on the right can always be decomposed.
      intro h12
      -- One of the premise coincides with the conclusion.
      exact h12
    -- We have shown the premise of h5, we can now drive its conclusion.
    let h13 := h5 h11
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h13
  case inr h14 =>
    -- Conjunctions on the left can always be decomposed.
    let h15 := h3.left
    let h16 := h3.right
    -- Conjunctions on the left can always be decomposed.
    let h17 := h16.left
    let h18 := h16.right
    -- Conjunctions on the left can always be decomposed.
    let h19 := h18.left
    let h20 := h18.right
    -- We want to use the implication h15 based on <expert-advice>. So we show its premise.
    have h21 : (p5 → p5) := by
      -- Implications on the right can always be decomposed.
      intro h22
      -- One of the premise coincides with the conclusion.
      exact h22
    -- We have shown the premise of h15, we can now drive its conclusion.
    let h23 := h15 h21
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h23
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_137418650451673327440347898506 : ((p4 ∧ (((((p2 ∧ (p3 ∧ p3)) ∧ p2) ∧ (((p3 ∧ (p3 → p5)) ∨ (p3 ∧ (p4 ∨ p3))) ∨ True)) ∨ False) ∨ p4)) ∨ ((False ∧ p5) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_328913995832072844834894232826 : (True → ((((False ∧ p3) → ((p4 ∨ p3) ∨ p3)) → False) → ((p5 → False) → (p1 ∨ (((p2 ∨ False) → p5) → (p5 ∧ (p5 ∧ (p5 ∨ True)))))))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Implications on the right can always be decomposed.
  intro h3
  -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
  have h4 : ((False ∧ p3) → ((p4 ∨ p3) ∨ p3)) := by
    -- Implications on the right can always be decomposed.
    intro h5
    -- Conjunctions on the left can always be decomposed.
    let h6 := h5.left
    let h7 := h5.right
    -- False on the left can always be used.
    apply False.elim h6
  -- We have shown the premise of h2, we can now drive its conclusion.
  let h8 := h2 h4
  -- False on the left can always be used.
  apply False.elim h8



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_47218511848972890173139326216 : ((((((p2 ∨ p1) → (False ∧ (p1 → p3))) ∧ (True ∨ True)) → ((((p5 ∧ ((p1 ∧ False) ∧ True)) ∧ p1) → p3) ∧ p1)) ∨ (True → True)) ∨ p1) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_324555864309653875209540693744 : (p5 ∨ ((p1 ∨ ((p1 ∨ p3) ∨ p5)) → ((((p2 → (p5 ∧ (((p2 ∨ (p4 → (p3 ∧ False))) ∧ p4) ∨ (p4 → True)))) ∧ False) ∨ True) ∨ True))) := by
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
theorem thm_5_vars_325635112526991703457844007262 : (p5 ∨ (False ∨ ((p4 ∨ (((p5 ∧ (p5 ∨ (p2 ∨ (True ∧ p4)))) ∧ p4) ∧ True)) → (((((p4 ∨ p5) → True) ∧ True) ∧ (False ∨ p1)) ∨ True)))) := by
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
    -- True on the right can always be proven directly.
    apply True.intro
  case inr h3 =>
    -- Conjunctions on the left can always be decomposed.
    let h4 := h3.left
    let h5 := h3.right
    -- Conjunctions on the left can always be decomposed.
    let h6 := h4.left
    let h7 := h4.right
    -- Conjunctions on the left can always be decomposed.
    let h8 := h6.left
    let h9 := h6.right
    -- Disjunctions on the left can always be decomposed.
    cases h9
    case inl h10 =>
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
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- True on the right can always be proven directly.
        apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_684382747553726510010991696931 : (((((((((p5 ∧ (p4 ∧ True)) ∧ p5) ∧ p1) → p2) ∧ p2) → (p5 ∧ (p1 → (p5 ∧ p3)))) ∨ (((p2 ∨ True) ∨ p2) ∨ (p2 → p4))) ∨ p5) ∧ True) := by
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
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_61138769215266947578078137293 : ((False ∧ ((p3 ∧ ((False → (p4 ∨ p5)) ∧ p4)) ∧ (p5 ∨ ((p5 ∨ ((p3 ∨ p5) → p4)) ∧ (p1 ∨ ((p5 → True) → (False ∧ p5))))))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_138896742430468135148838482267 : (((False → ((True ∨ (((False → ((p1 ∧ True) ∧ p4)) → (p5 ∧ ((False → p2) → False))) ∨ (p1 ∨ p4))) → p4)) ∧ p1) → (True ∧ (p2 ∨ True))) := by
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
theorem thm_5_vars_160844094257197329132324195625 : ((((p4 → (p5 ∧ True)) ∧ True) ∧ (((True ∧ (p3 → p1)) ∨ (True ∨ True)) ∧ (p4 ∨ (p3 ∧ p1)))) → (p5 ∨ ((False ∧ p5) → (p4 → p4)))) := by
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
    -- Conjunctions on the left can always be decomposed.
    let h9 := h8.left
    let h10 := h8.right
    -- Disjunctions on the left can always be decomposed.
    cases h7
    case inl h11 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Implications on the right can always be decomposed.
      intro h12
      -- Implications on the right can always be decomposed.
      intro h13
      -- Conjunctions on the left can always be decomposed.
      let h14 := h12.left
      let h15 := h12.right
      -- False on the left can always be used.
      apply False.elim h14
    case inr h16 =>
      -- Conjunctions on the left can always be decomposed.
      let h17 := h16.left
      let h18 := h16.right
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Implications on the right can always be decomposed.
      intro h19
      -- Implications on the right can always be decomposed.
      intro h20
      -- Conjunctions on the left can always be decomposed.
      let h21 := h19.left
      let h22 := h19.right
      -- False on the left can always be used.
      apply False.elim h21
  case inr h23 =>
    -- Disjunctions on the left can always be decomposed.
    cases h23
    case inl h24 =>
      -- Disjunctions on the left can always be decomposed.
      cases h7
      case inl h25 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- Implications on the right can always be decomposed.
        intro h26
        -- Implications on the right can always be decomposed.
        intro h27
        -- Conjunctions on the left can always be decomposed.
        let h28 := h26.left
        let h29 := h26.right
        -- False on the left can always be used.
        apply False.elim h28
      case inr h30 =>
        -- Conjunctions on the left can always be decomposed.
        let h31 := h30.left
        let h32 := h30.right
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- Implications on the right can always be decomposed.
        intro h33
        -- Implications on the right can always be decomposed.
        intro h34
        -- Conjunctions on the left can always be decomposed.
        let h35 := h33.left
        let h36 := h33.right
        -- False on the left can always be used.
        apply False.elim h35
    case inr h37 =>
      -- Disjunctions on the left can always be decomposed.
      cases h7
      case inl h38 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- Implications on the right can always be decomposed.
        intro h39
        -- Implications on the right can always be decomposed.
        intro h40
        -- Conjunctions on the left can always be decomposed.
        let h41 := h39.left
        let h42 := h39.right
        -- False on the left can always be used.
        apply False.elim h41
      case inr h43 =>
        -- Conjunctions on the left can always be decomposed.
        let h44 := h43.left
        let h45 := h43.right
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- Implications on the right can always be decomposed.
        intro h46
        -- Implications on the right can always be decomposed.
        intro h47
        -- Conjunctions on the left can always be decomposed.
        let h48 := h46.left
        let h49 := h46.right
        -- False on the left can always be used.
        apply False.elim h48



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_609470637124494249763600834438 : (((((False ∧ ((((p5 ∧ p3) ∨ p1) ∧ (((False ∧ p4) ∨ p3) → False)) ∧ (((True → p3) ∧ (True → p4)) → (p3 ∧ p2)))) ∨ True) ∨ p2) ∨ p4) ∧ True) := by
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
theorem thm_5_vars_116544742810802117708971610522 : (((False ∨ p3) ∧ (False ∨ (((True ∧ (p3 ∨ p3)) ∨ (p1 ∨ (p3 → (((False → p3) ∨ p1) ∨ ((p4 → False) ∨ p1))))) ∨ p2))) ∨ (p2 ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_49116016854604302327788827278 : ((((p2 → ((((False ∨ p5) ∧ ((p4 ∧ True) → p5)) ∧ (p1 ∨ True)) ∧ p1)) ∨ (((p5 ∨ False) ∧ True) ∨ p2)) ∨ ((False → p5) ∨ p3)) ∨ p3) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_122827477894750358918180760164 : ((((((((p5 → p4) ∧ True) ∧ ((True ∧ p5) → p3)) ∧ p4) ∧ (p5 ∨ (p3 → (p4 ∧ p3)))) → True) ∧ (p4 ∧ (p3 → False))) → (p5 → p4)) := by
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
  -- One of the premise coincides with the conclusion.
  exact h5



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_256917355797099656125718563185 : ((p1 ∨ p4) → ((True → p2) → ((((p1 → False) → (((p3 ∨ p1) → p3) → ((p4 → False) ∧ False))) ∧ p3) ∨ (False ∨ ((True ∨ False) ∨ p5))))) := by
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
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- True on the right can always be proven directly.
    apply True.intro
  case inr h4 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- True on the right can always be proven directly.
    apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_157753319731481713738966242541 : (((((p4 → p5) ∨ (p4 ∨ p1)) ∧ (p4 ∨ ((p2 ∧ True) ∧ p1))) ∧ (False ∨ ((p3 ∧ False) ∨ p1))) ∨ ((p5 → True) → ((True ∧ True) ∨ p2))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_225906603030201035631945415705 : (((p1 ∧ p4) ∨ p2) ∨ ((((p3 ∨ (p4 → False)) ∧ ((True ∨ p4) → ((((p2 ∧ p4) ∨ p1) → (p5 ∧ True)) → p2))) ∨ (True ∨ p1)) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_52035647665866844337405096866 : (((p4 ∨ ((p4 ∧ p1) → (((True ∧ False) ∧ p2) ∨ (((p5 ∨ p2) ∨ True) ∨ False)))) ∨ ((p5 ∨ (p3 ∧ p4)) ∨ ((p3 → True) ∨ False))) ∨ p4) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
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



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_115453266191186226080508566270 : ((((p2 ∨ p3) ∧ ((p3 ∨ (p1 ∧ False)) → False)) ∨ ((p1 ∧ (((p2 ∧ ((p5 ∨ (p3 → p3)) → p1)) ∨ False) → p3)) → p3)) ∨ (False → False)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_633343190143669108496234205623 : ((((((((((p4 → ((p2 ∨ p3) ∧ (p4 ∨ p1))) ∧ False) ∧ (False ∨ p4)) → p5) → ((p3 → p1) ∧ True)) ∨ p3) ∨ (p1 → True)) → p2) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_815940333684363857469263431787 : (((((((((False ∧ (p2 ∨ ((True → p1) ∨ p5))) ∨ True) ∨ p2) → (p3 → (((p2 ∨ (p1 ∧ p4)) ∨ p5) ∧ False))) ∨ True) → False) ∧ p5) → p3) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
  have h4 : (((((False ∧ (p2 ∨ ((True → p1) ∨ p5))) ∨ True) ∨ p2) → (p3 → (((p2 ∨ (p1 ∧ p4)) ∨ p5) ∧ False))) ∨ True) := by
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h2, we can now drive its conclusion.
  let h5 := h2 h4
  -- False on the left can always be used.
  apply False.elim h5
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_193196450675483928182817496483 : ((((False → p1) → (p1 ∨ p3)) → ((True ∨ p4) ∧ p2)) → (p1 ∨ (p3 → (((((p2 → False) → (p2 → (False ∧ p3))) → False) ∧ p2) ∨ True)))) := by
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
theorem thm_5_vars_785007726656172867816176261893 : (((p3 ∨ (p5 → ((False ∨ (p4 ∧ ((True → (((p4 → p2) → p5) ∨ (False ∨ (p3 → (p3 ∧ p3))))) ∧ p5))) ∧ (True ∨ (True ∨ p4))))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_219031875297853813685616287215 : ((p5 ∧ ((p2 ∧ False) ∨ p4)) → ((((((p4 → p3) ∧ (((p2 → p4) ∧ True) → (p3 ∧ False))) ∧ p2) ∨ p3) ∧ p4) ∨ (p1 → (True ∨ p4)))) := by
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
    -- False on the left can always be used.
    apply False.elim h6
  case inr h7 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h8
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- True on the right can always be proven directly.
    apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_38997644285179338867666401417 : ((((p1 ∨ False) ∧ (p5 ∧ (True → ((p3 → ((p3 → p1) ∧ ((((p4 → True) → p2) → p2) ∧ ((p5 ∧ True) ∨ p2)))) ∨ p3)))) ∧ p5) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_210540924094279671901632005325 : ((((p4 ∧ False) ∧ p3) → False) ∧ ((((p3 ∨ p2) ∧ (False ∨ p3)) ∧ ((p4 ∨ p3) ∨ p5)) → ((p5 ∨ (p5 ∨ p5)) ∨ ((p1 ∧ p5) → p5)))) := by
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
  -- False on the left can always be used.
  apply False.elim h5
  -- Implications on the right can always be decomposed.
  intro h6
  -- Conjunctions on the left can always be decomposed.
  let h7 := h6.left
  let h8 := h6.right
  -- Conjunctions on the left can always be decomposed.
  let h9 := h7.left
  let h10 := h7.right
  -- Disjunctions on the left can always be decomposed.
  cases h9
  case inl h11 =>
    -- Disjunctions on the left can always be decomposed.
    cases h10
    case inl h12 =>
      -- False on the left can always be used.
      apply False.elim h12
    case inr h13 =>
      -- Disjunctions on the left can always be decomposed.
      cases h8
      case inl h14 =>
        -- Disjunctions on the left can always be decomposed.
        cases h14
        case inl h15 =>
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- Implications on the right can always be decomposed.
          intro h16
          -- Conjunctions on the left can always be decomposed.
          let h17 := h16.left
          let h18 := h16.right
          -- One of the premise coincides with the conclusion.
          exact h18
        case inr h19 =>
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- Implications on the right can always be decomposed.
          intro h20
          -- Conjunctions on the left can always be decomposed.
          let h21 := h20.left
          let h22 := h20.right
          -- One of the premise coincides with the conclusion.
          exact h22
      case inr h23 =>
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- One of the premise coincides with the conclusion.
        exact h23
  case inr h24 =>
    -- Disjunctions on the left can always be decomposed.
    cases h10
    case inl h25 =>
      -- False on the left can always be used.
      apply False.elim h25
    case inr h26 =>
      -- Disjunctions on the left can always be decomposed.
      cases h8
      case inl h27 =>
        -- Disjunctions on the left can always be decomposed.
        cases h27
        case inl h28 =>
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- Implications on the right can always be decomposed.
          intro h29
          -- Conjunctions on the left can always be decomposed.
          let h30 := h29.left
          let h31 := h29.right
          -- One of the premise coincides with the conclusion.
          exact h31
        case inr h32 =>
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- Implications on the right can always be decomposed.
          intro h33
          -- Conjunctions on the left can always be decomposed.
          let h34 := h33.left
          let h35 := h33.right
          -- One of the premise coincides with the conclusion.
          exact h35
      case inr h36 =>
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- One of the premise coincides with the conclusion.
        exact h36



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_477802023621867147211508116274 : (((((p3 ∨ ((p2 → True) → p1)) ∨ (p5 ∧ (p2 ∧ True))) → ((p2 → p3) ∨ ((p4 ∨ True) ∨ (((p2 ∧ (p3 ∧ p1)) → False) → True)))) ∧ True) ∧ True) := by
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
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- True on the right can always be proven directly.
      apply True.intro
    case inr h4 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- True on the right can always be proven directly.
      apply True.intro
  case inr h5 =>
    -- Conjunctions on the left can always be decomposed.
    let h6 := h5.left
    let h7 := h5.right
    -- Conjunctions on the left can always be decomposed.
    let h8 := h7.left
    let h9 := h7.right
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
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_264430278784817837995792346874 : (True ∧ (((p5 ∧ (True ∨ p2)) ∨ p2) → (p4 → (((p5 ∧ False) ∨ True) → (p3 → (p4 → ((p4 ∧ p1) ∨ (((p4 ∨ p1) → False) → p1)))))))) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- True on the right can always be proven directly.
  apply True.intro
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
  cases h3
  case inl h6 =>
    -- Conjunctions on the left can always be decomposed.
    let h7 := h6.left
    let h8 := h6.right
    -- False on the left can always be used.
    apply False.elim h8
  case inr h9 =>
    -- Disjunctions on the left can always be decomposed.
    cases h1
    case inl h10 =>
      -- Conjunctions on the left can always be decomposed.
      let h11 := h10.left
      let h12 := h10.right
      -- Disjunctions on the left can always be decomposed.
      cases h12
      case inl h13 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- Implications on the right can always be decomposed.
        intro h14
        -- We want to use the implication h14 based on <expert-advice>. So we show its premise.
        have h15 : (p4 ∨ p1) := by
          -- Show the left disjunct based on <expert-advice>.
          apply Or.inl
          -- One of the premise coincides with the conclusion.
          exact h2
        -- We have shown the premise of h14, we can now drive its conclusion.
        let h16 := h14 h15
        -- False on the left can always be used.
        apply False.elim h16
      case inr h17 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- Implications on the right can always be decomposed.
        intro h18
        -- We want to use the implication h18 based on <expert-advice>. So we show its premise.
        have h19 : (p4 ∨ p1) := by
          -- Show the left disjunct based on <expert-advice>.
          apply Or.inl
          -- One of the premise coincides with the conclusion.
          exact h2
        -- We have shown the premise of h18, we can now drive its conclusion.
        let h20 := h18 h19
        -- False on the left can always be used.
        apply False.elim h20
    case inr h21 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Implications on the right can always be decomposed.
      intro h22
      -- We want to use the implication h22 based on <expert-advice>. So we show its premise.
      have h23 : (p4 ∨ p1) := by
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- One of the premise coincides with the conclusion.
        exact h2
      -- We have shown the premise of h22, we can now drive its conclusion.
      let h24 := h22 h23
      -- False on the left can always be used.
      apply False.elim h24



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_48888512025966885636881576675 : (((p1 → ((True ∧ (p2 ∧ p1)) ∨ ((False ∧ (p5 ∧ (p2 → (p4 → False)))) ∧ (((p4 ∨ p3) ∧ p3) ∨ p2)))) ∧ (p4 ∨ (p3 ∧ True))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_619648140362974960293708992144 : (((((p3 ∧ False) ∧ ((p3 → False) ∧ ((p5 ∧ (((((p3 → (p5 ∧ p3)) → p2) → p2) → ((p5 → p1) ∧ p5)) ∨ p5)) ∨ False))) ∨ True) ∨ p1) ∧ True) := by
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
theorem thm_5_vars_256043295296884994003024582064 : ((True ∨ p4) → (((p4 → False) ∨ ((p3 ∨ (((p4 ∧ (p2 ∨ (p2 ∨ ((p4 ∨ (True → False)) → p1)))) ∨ p2) ∨ True)) ∧ p2)) ∨ (p2 → p2))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h2 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h3
    -- One of the premise coincides with the conclusion.
    exact h3
  case inr h4 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h5
    -- One of the premise coincides with the conclusion.
    exact h5



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_305008719193020252755803477775 : (p1 ∨ (((((p5 → p5) ∧ True) → (p5 ∨ (True ∧ p1))) ∨ ((True ∨ (p3 → p3)) → ((False ∨ (p1 ∨ p2)) → False))) ∨ (p1 ∨ (p1 → True)))) := by
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
theorem thm_5_vars_119307127068106130053061780694 : ((p3 → (((p2 ∨ False) ∨ (((p2 ∧ (((p2 ∨ p5) ∨ p2) ∨ False)) ∧ ((False ∨ p2) ∨ (p5 → p3))) ∧ p1)) ∨ (False → p2))) ∨ (p1 ∨ p4)) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h2
  -- False on the left can always be used.
  apply False.elim h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_328301670379071155621052794078 : (True → (((p1 ∨ p5) → (p2 ∨ (p1 ∧ ((p1 ∧ (((p1 → (False ∧ (p2 → False))) ∨ p2) ∨ False)) ∧ True)))) ∨ (p3 ∨ (p5 → (True ∨ True))))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h2
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_879556828142271832716324315889 : ((((True → ((p3 ∧ (((p5 → (((False ∨ (p2 ∨ ((p1 → (p3 → p3)) ∧ p4))) ∨ p5) ∧ False)) ∧ False) ∧ False)) ∧ p3)) ∧ (True ∧ p3)) → p4) ∧ True) := by
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
  -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
  have h6 : True := by
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h2, we can now drive its conclusion.
  let h7 := h2 h6
  -- We need to get the left conjuct of h7 based on <expert-advice>.
  let h8 := h7.left
  -- We need to get the right conjuct of h8 based on <expert-advice>.
  let h9 := h8.right
  -- We need to get the right conjuct of h9 based on <expert-advice>.
  let h10 := h9.right
  -- False on the left can always be used.
  apply False.elim h10
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_642964251042751977821242227376 : ((((p2 ∧ (((((p2 ∧ p3) ∨ p1) → True) ∨ p3) ∧ ((p2 ∧ p3) → ((((p4 ∧ ((True ∧ p3) ∧ p5)) ∨ False) → p5) ∨ p3)))) → p5) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_64547419982568667017230875911 : ((p1 ∨ ((p5 ∨ ((p1 ∨ p3) ∨ (p2 → p3))) → (False ∨ (p2 ∨ (True ∨ (p1 ∨ ((p1 ∨ False) → ((p1 ∨ (True → p1)) → True)))))))) ∨ False) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h2 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- True on the right can always be proven directly.
    apply True.intro
  case inr h3 =>
    -- Disjunctions on the left can always be decomposed.
    cases h3
    case inl h4 =>
      -- Disjunctions on the left can always be decomposed.
      cases h4
      case inl h5 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- True on the right can always be proven directly.
        apply True.intro
      case inr h6 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- True on the right can always be proven directly.
        apply True.intro
    case inr h7 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- True on the right can always be proven directly.
      apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_522652717510649437772098595942 : ((((p5 → p2) → ((((p2 → (False → p5)) → (((p4 ∧ (p1 → p4)) ∧ p5) ∨ p4)) → (p3 ∨ p4)) ∧ (((p1 → p2) ∧ p2) → True))) ∧ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h2
  -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
  have h3 : (p2 → (False → p5)) := by
    -- Implications on the right can always be decomposed.
    intro h4
    -- Implications on the right can always be decomposed.
    intro h5
    -- False on the left can always be used.
    apply False.elim h5
  -- We have shown the premise of h2, we can now drive its conclusion.
  let h6 := h2 h3
  -- Disjunctions on the left can always be decomposed.
  cases h6
  case inl h7 =>
    -- Conjunctions on the left can always be decomposed.
    let h8 := h7.left
    let h9 := h7.right
    -- Conjunctions on the left can always be decomposed.
    let h10 := h8.left
    let h11 := h8.right
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h10
  case inr h12 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h12
  -- Implications on the right can always be decomposed.
  intro h13
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_937787245006555666874756403134 : ((((p5 ∧ ((p1 → (True ∧ True)) → False)) ∧ ((False ∨ (p1 ∨ (p1 ∨ (True ∨ True)))) ∧ (p2 → ((p3 → p4) ∧ (p1 ∨ (p3 → p1)))))) → p4) ∧ True) := by
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
    -- False on the left can always be used.
    apply False.elim h8
  case inr h9 =>
    -- Disjunctions on the left can always be decomposed.
    cases h9
    case inl h10 =>
      -- We want to use the implication h5 based on <expert-advice>. So we show its premise.
      have h11 : (p1 → (True ∧ True)) := by
        -- Implications on the right can always be decomposed.
        intro h12
        -- Conjunctions on the right can always be decomposed.
        apply And.intro
        -- True on the right can always be proven directly.
        apply True.intro
        -- True on the right can always be proven directly.
        apply True.intro
      -- We have shown the premise of h5, we can now drive its conclusion.
      let h13 := h5 h11
      -- False on the left can always be used.
      apply False.elim h13
    case inr h14 =>
      -- Disjunctions on the left can always be decomposed.
      cases h14
      case inl h15 =>
        -- We want to use the implication h5 based on <expert-advice>. So we show its premise.
        have h16 : (p1 → (True ∧ True)) := by
          -- Implications on the right can always be decomposed.
          intro h17
          -- Conjunctions on the right can always be decomposed.
          apply And.intro
          -- True on the right can always be proven directly.
          apply True.intro
          -- True on the right can always be proven directly.
          apply True.intro
        -- We have shown the premise of h5, we can now drive its conclusion.
        let h18 := h5 h16
        -- False on the left can always be used.
        apply False.elim h18
      case inr h19 =>
        -- Disjunctions on the left can always be decomposed.
        cases h19
        case inl h20 =>
          -- We want to use the implication h5 based on <expert-advice>. So we show its premise.
          have h21 : (p1 → (True ∧ True)) := by
            -- Implications on the right can always be decomposed.
            intro h22
            -- Conjunctions on the right can always be decomposed.
            apply And.intro
            -- True on the right can always be proven directly.
            apply True.intro
            -- True on the right can always be proven directly.
            apply True.intro
          -- We have shown the premise of h5, we can now drive its conclusion.
          let h23 := h5 h21
          -- False on the left can always be used.
          apply False.elim h23
        case inr h24 =>
          -- We want to use the implication h5 based on <expert-advice>. So we show its premise.
          have h25 : (p1 → (True ∧ True)) := by
            -- Implications on the right can always be decomposed.
            intro h26
            -- Conjunctions on the right can always be decomposed.
            apply And.intro
            -- True on the right can always be proven directly.
            apply True.intro
            -- True on the right can always be proven directly.
            apply True.intro
          -- We have shown the premise of h5, we can now drive its conclusion.
          let h27 := h5 h25
          -- False on the left can always be used.
          apply False.elim h27
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_112758268307634560898956679975 : ((((p4 ∨ ((((False → True) → p4) → False) ∨ (p1 ∧ p4))) ∧ (p4 ∨ ((False ∨ (((p5 ∨ p5) ∨ p4) ∨ p3)) → True))) → False) ∨ (p5 → p5)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- One of the premise coincides with the conclusion.
  exact h1



