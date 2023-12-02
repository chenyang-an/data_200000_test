variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_112767717877442658005181835408 : ((((((p1 ∧ (False ∧ p4)) ∧ (True ∧ p5)) ∧ (p5 ∨ p5)) → ((p2 → False) ∧ (p5 → ((p3 ∧ (p5 ∧ False)) ∧ p2)))) → p3) ∨ (False → p2)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_64417373824964743077192295787 : ((p1 ∨ ((False ∨ (((p5 ∧ ((p2 → p3) → ((p5 ∨ p1) ∧ (((p2 ∨ p5) ∧ (False ∧ p2)) → p2)))) → p1) ∧ (p2 ∧ p4))) → p1)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_116094030760145591044859295580 : ((((False → True) ∨ p5) ∧ (((p2 ∧ ((((p5 ∨ False) ∨ p5) ∧ (p4 → p2)) ∧ False)) → p3) → (((True ∧ False) ∨ p3) ∧ p4))) ∨ (True ∧ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_321352365069056593591304142759 : (p4 ∨ (True → (((((False ∧ False) ∨ ((p2 ∧ (((True ∧ (p1 ∧ p3)) ∨ (p3 ∧ (False ∨ p3))) → p1)) ∨ (p4 ∨ False))) ∨ p2) ∨ p3) ∨ True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_51183052413983446006255700471 : ((((((p4 → (((False ∧ (p4 ∨ False)) ∧ p5) ∨ p5)) → p2) ∨ p1) ∧ ((p4 ∨ p3) ∨ p2)) ∨ ((True → p5) ∨ ((True ∨ p3) ∨ p3))) ∨ p3) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
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
theorem thm_5_vars_303150490542719712763535763075 : (False ∨ (p3 → (p4 ∨ (((p2 ∨ p5) ∨ ((p1 → (p4 ∧ ((p3 ∧ p2) ∨ p1))) ∨ ((p5 ∨ ((p3 ∨ p2) ∨ p2)) ∨ (True → False)))) ∨ p4)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
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
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_677283139331363120911156442669 : ((((((True ∨ p5) ∧ ((((p5 → p4) ∧ ((p2 ∧ True) ∧ (True ∨ (p2 → False)))) → False) ∨ False)) ∧ p5) ∨ ((p3 ∧ (p3 ∧ p1)) ∨ p3)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_219245448907090516977907278832 : ((p1 ∨ ((p3 ∨ False) → p1)) → (((p2 ∨ p2) ∨ (p4 → p4)) → ((p4 ∨ True) → ((p1 ∨ p3) → ((p1 ∨ p1) ∨ ((p2 ∨ p5) → p1)))))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Implications on the right can always be decomposed.
  intro h3
  -- Implications on the right can always be decomposed.
  intro h4
  -- Disjunctions on the left can always be decomposed.
  cases h4
  case inl h5 =>
    -- Disjunctions on the left can always be decomposed.
    cases h3
    case inl h6 =>
      -- Disjunctions on the left can always be decomposed.
      cases h2
      case inl h7 =>
        -- Disjunctions on the left can always be decomposed.
        cases h7
        case inl h8 =>
          -- Disjunctions on the left can always be decomposed.
          cases h1
          case inl h9 =>
            -- Show the left disjunct based on <expert-advice>.
            apply Or.inl
            -- Show the left disjunct based on <expert-advice>.
            apply Or.inl
            -- One of the premise coincides with the conclusion.
            exact h9
          case inr h10 =>
            -- Show the left disjunct based on <expert-advice>.
            apply Or.inl
            -- Show the left disjunct based on <expert-advice>.
            apply Or.inl
            -- One of the premise coincides with the conclusion.
            exact h5
        case inr h11 =>
          -- Disjunctions on the left can always be decomposed.
          cases h1
          case inl h12 =>
            -- Show the left disjunct based on <expert-advice>.
            apply Or.inl
            -- Show the left disjunct based on <expert-advice>.
            apply Or.inl
            -- One of the premise coincides with the conclusion.
            exact h12
          case inr h13 =>
            -- Show the left disjunct based on <expert-advice>.
            apply Or.inl
            -- Show the left disjunct based on <expert-advice>.
            apply Or.inl
            -- One of the premise coincides with the conclusion.
            exact h5
      case inr h14 =>
        -- Disjunctions on the left can always be decomposed.
        cases h1
        case inl h15 =>
          -- Show the left disjunct based on <expert-advice>.
          apply Or.inl
          -- Show the left disjunct based on <expert-advice>.
          apply Or.inl
          -- One of the premise coincides with the conclusion.
          exact h15
        case inr h16 =>
          -- Show the left disjunct based on <expert-advice>.
          apply Or.inl
          -- Show the left disjunct based on <expert-advice>.
          apply Or.inl
          -- One of the premise coincides with the conclusion.
          exact h5
    case inr h17 =>
      -- Disjunctions on the left can always be decomposed.
      cases h2
      case inl h18 =>
        -- Disjunctions on the left can always be decomposed.
        cases h18
        case inl h19 =>
          -- Disjunctions on the left can always be decomposed.
          cases h1
          case inl h20 =>
            -- Show the left disjunct based on <expert-advice>.
            apply Or.inl
            -- Show the left disjunct based on <expert-advice>.
            apply Or.inl
            -- One of the premise coincides with the conclusion.
            exact h20
          case inr h21 =>
            -- Show the left disjunct based on <expert-advice>.
            apply Or.inl
            -- Show the left disjunct based on <expert-advice>.
            apply Or.inl
            -- One of the premise coincides with the conclusion.
            exact h5
        case inr h22 =>
          -- Disjunctions on the left can always be decomposed.
          cases h1
          case inl h23 =>
            -- Show the left disjunct based on <expert-advice>.
            apply Or.inl
            -- Show the left disjunct based on <expert-advice>.
            apply Or.inl
            -- One of the premise coincides with the conclusion.
            exact h23
          case inr h24 =>
            -- Show the left disjunct based on <expert-advice>.
            apply Or.inl
            -- Show the left disjunct based on <expert-advice>.
            apply Or.inl
            -- One of the premise coincides with the conclusion.
            exact h5
      case inr h25 =>
        -- Disjunctions on the left can always be decomposed.
        cases h1
        case inl h26 =>
          -- Show the left disjunct based on <expert-advice>.
          apply Or.inl
          -- Show the left disjunct based on <expert-advice>.
          apply Or.inl
          -- One of the premise coincides with the conclusion.
          exact h26
        case inr h27 =>
          -- Show the left disjunct based on <expert-advice>.
          apply Or.inl
          -- Show the left disjunct based on <expert-advice>.
          apply Or.inl
          -- One of the premise coincides with the conclusion.
          exact h5
  case inr h28 =>
    -- Disjunctions on the left can always be decomposed.
    cases h3
    case inl h29 =>
      -- Disjunctions on the left can always be decomposed.
      cases h2
      case inl h30 =>
        -- Disjunctions on the left can always be decomposed.
        cases h30
        case inl h31 =>
          -- Disjunctions on the left can always be decomposed.
          cases h1
          case inl h32 =>
            -- Show the left disjunct based on <expert-advice>.
            apply Or.inl
            -- Show the left disjunct based on <expert-advice>.
            apply Or.inl
            -- One of the premise coincides with the conclusion.
            exact h32
          case inr h33 =>
            -- We want to use the implication h33 based on <expert-advice>. So we show its premise.
            have h34 : (p3 ∨ False) := by
              -- Show the left disjunct based on <expert-advice>.
              apply Or.inl
              -- One of the premise coincides with the conclusion.
              exact h28
            -- We have shown the premise of h33, we can now drive its conclusion.
            let h35 := h33 h34
            -- Show the left disjunct based on <expert-advice>.
            apply Or.inl
            -- Show the left disjunct based on <expert-advice>.
            apply Or.inl
            -- One of the premise coincides with the conclusion.
            exact h35
        case inr h36 =>
          -- Disjunctions on the left can always be decomposed.
          cases h1
          case inl h37 =>
            -- Show the left disjunct based on <expert-advice>.
            apply Or.inl
            -- Show the left disjunct based on <expert-advice>.
            apply Or.inl
            -- One of the premise coincides with the conclusion.
            exact h37
          case inr h38 =>
            -- We want to use the implication h38 based on <expert-advice>. So we show its premise.
            have h39 : (p3 ∨ False) := by
              -- Show the left disjunct based on <expert-advice>.
              apply Or.inl
              -- One of the premise coincides with the conclusion.
              exact h28
            -- We have shown the premise of h38, we can now drive its conclusion.
            let h40 := h38 h39
            -- Show the left disjunct based on <expert-advice>.
            apply Or.inl
            -- Show the left disjunct based on <expert-advice>.
            apply Or.inl
            -- One of the premise coincides with the conclusion.
            exact h40
      case inr h41 =>
        -- Disjunctions on the left can always be decomposed.
        cases h1
        case inl h42 =>
          -- Show the left disjunct based on <expert-advice>.
          apply Or.inl
          -- Show the left disjunct based on <expert-advice>.
          apply Or.inl
          -- One of the premise coincides with the conclusion.
          exact h42
        case inr h43 =>
          -- We want to use the implication h43 based on <expert-advice>. So we show its premise.
          have h44 : (p3 ∨ False) := by
            -- Show the left disjunct based on <expert-advice>.
            apply Or.inl
            -- One of the premise coincides with the conclusion.
            exact h28
          -- We have shown the premise of h43, we can now drive its conclusion.
          let h45 := h43 h44
          -- Show the left disjunct based on <expert-advice>.
          apply Or.inl
          -- Show the left disjunct based on <expert-advice>.
          apply Or.inl
          -- One of the premise coincides with the conclusion.
          exact h45
    case inr h46 =>
      -- Disjunctions on the left can always be decomposed.
      cases h2
      case inl h47 =>
        -- Disjunctions on the left can always be decomposed.
        cases h47
        case inl h48 =>
          -- Disjunctions on the left can always be decomposed.
          cases h1
          case inl h49 =>
            -- Show the left disjunct based on <expert-advice>.
            apply Or.inl
            -- Show the left disjunct based on <expert-advice>.
            apply Or.inl
            -- One of the premise coincides with the conclusion.
            exact h49
          case inr h50 =>
            -- We want to use the implication h50 based on <expert-advice>. So we show its premise.
            have h51 : (p3 ∨ False) := by
              -- Show the left disjunct based on <expert-advice>.
              apply Or.inl
              -- One of the premise coincides with the conclusion.
              exact h28
            -- We have shown the premise of h50, we can now drive its conclusion.
            let h52 := h50 h51
            -- Show the left disjunct based on <expert-advice>.
            apply Or.inl
            -- Show the left disjunct based on <expert-advice>.
            apply Or.inl
            -- One of the premise coincides with the conclusion.
            exact h52
        case inr h53 =>
          -- Disjunctions on the left can always be decomposed.
          cases h1
          case inl h54 =>
            -- Show the left disjunct based on <expert-advice>.
            apply Or.inl
            -- Show the left disjunct based on <expert-advice>.
            apply Or.inl
            -- One of the premise coincides with the conclusion.
            exact h54
          case inr h55 =>
            -- We want to use the implication h55 based on <expert-advice>. So we show its premise.
            have h56 : (p3 ∨ False) := by
              -- Show the left disjunct based on <expert-advice>.
              apply Or.inl
              -- One of the premise coincides with the conclusion.
              exact h28
            -- We have shown the premise of h55, we can now drive its conclusion.
            let h57 := h55 h56
            -- Show the left disjunct based on <expert-advice>.
            apply Or.inl
            -- Show the left disjunct based on <expert-advice>.
            apply Or.inl
            -- One of the premise coincides with the conclusion.
            exact h57
      case inr h58 =>
        -- Disjunctions on the left can always be decomposed.
        cases h1
        case inl h59 =>
          -- Show the left disjunct based on <expert-advice>.
          apply Or.inl
          -- Show the left disjunct based on <expert-advice>.
          apply Or.inl
          -- One of the premise coincides with the conclusion.
          exact h59
        case inr h60 =>
          -- We want to use the implication h60 based on <expert-advice>. So we show its premise.
          have h61 : (p3 ∨ False) := by
            -- Show the left disjunct based on <expert-advice>.
            apply Or.inl
            -- One of the premise coincides with the conclusion.
            exact h28
          -- We have shown the premise of h60, we can now drive its conclusion.
          let h62 := h60 h61
          -- Show the left disjunct based on <expert-advice>.
          apply Or.inl
          -- Show the left disjunct based on <expert-advice>.
          apply Or.inl
          -- One of the premise coincides with the conclusion.
          exact h62



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_314534451043465350751636712269 : (p3 ∨ (((((p2 → ((p4 ∨ p3) → False)) → ((p5 ∧ False) ∧ (True ∨ (p2 → p4)))) ∧ p1) ∨ True) ∨ (True → (p1 ∨ (p3 ∨ (True ∧ True)))))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_54571972030546705779184880859 : (((False ∨ (((p1 ∧ p5) ∧ (True ∨ p5)) ∨ p1)) ∨ (((False → ((False ∨ True) → p3)) → p4) ∨ (p4 → (p4 ∧ (True → (p4 ∨ p4)))))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_750947342137565255398010529941 : (((True ∧ ((((False ∧ (p2 ∨ p4)) ∧ p1) → p4) ∧ ((p5 → ((p5 ∧ (p2 ∧ (p4 ∨ p3))) ∧ (False ∨ p5))) → ((p5 → p4) → p5)))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_344589298006638052444851544093 : (p2 → (p1 → (((((p4 ∧ p1) ∨ p4) ∨ (((((p3 ∨ p3) → p2) ∨ (p1 ∧ (True ∨ p5))) ∧ p3) ∧ ((p1 ∨ p3) → p4))) ∨ p3) ∨ p1))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_356387465260319643830773114719 : (p5 → ((((p5 → p3) ∨ p5) ∨ ((((True → True) ∨ p4) ∧ (p5 → True)) ∧ True)) → ((False ∨ ((p3 ∨ p3) ∨ (p5 → p5))) ∨ (p2 ∧ p4)))) := by
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
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Implications on the right can always be decomposed.
      intro h5
      -- One of the premise coincides with the conclusion.
      exact h5
    case inr h6 =>
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Implications on the right can always be decomposed.
      intro h7
      -- One of the premise coincides with the conclusion.
      exact h7
  case inr h8 =>
    -- Conjunctions on the left can always be decomposed.
    let h9 := h8.left
    let h10 := h8.right
    -- Conjunctions on the left can always be decomposed.
    let h11 := h9.left
    let h12 := h9.right
    -- Disjunctions on the left can always be decomposed.
    cases h11
    case inl h13 =>
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Implications on the right can always be decomposed.
      intro h14
      -- One of the premise coincides with the conclusion.
      exact h14
    case inr h15 =>
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Implications on the right can always be decomposed.
      intro h16
      -- One of the premise coincides with the conclusion.
      exact h16



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_750245763290934362259669963115 : (((True ∧ ((((((p1 ∧ True) → p2) ∨ p5) ∨ (p1 ∧ (((p3 ∨ p5) → (True ∧ p1)) ∧ ((False ∧ False) → p5)))) → p2) ∨ (True ∨ p3))) ∨ p3) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
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
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_167000322243973527365714928443 : (((True → ((((((p3 → p2) ∨ p3) ∧ (p4 ∧ p4)) ∧ p5) ∧ (p3 ∨ p2)) ∧ True)) ∧ p5) → (((p2 ∨ False) → (p2 → (True ∧ p4))) ∧ p4)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h2
  -- Implications on the right can always be decomposed.
  intro h3
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- Disjunctions on the left can always be decomposed.
  cases h2
  case inl h4 =>
    -- Conjunctions on the left can always be decomposed.
    let h5 := h1.left
    let h6 := h1.right
    -- We want to use the implication h5 based on <expert-advice>. So we show its premise.
    have h7 : True := by
      -- True on the right can always be proven directly.
      apply True.intro
    -- We have shown the premise of h5, we can now drive its conclusion.
    let h8 := h5 h7
    -- We need to get the left conjuct of h8 based on <expert-advice>.
    let h9 := h8.left
    -- We need to get the left conjuct of h9 based on <expert-advice>.
    let h10 := h9.left
    -- We need to get the left conjuct of h10 based on <expert-advice>.
    let h11 := h10.left
    -- We need to get the right conjuct of h11 based on <expert-advice>.
    let h12 := h11.right
    -- We need to get the left conjuct of h12 based on <expert-advice>.
    let h13 := h12.left
    -- One of the premise coincides with the conclusion.
    exact h13
  case inr h14 =>
    -- False on the left can always be used.
    apply False.elim h14
  -- Conjunctions on the left can always be decomposed.
  let h15 := h1.left
  let h16 := h1.right
  -- We want to use the implication h15 based on <expert-advice>. So we show its premise.
  have h17 : True := by
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h15, we can now drive its conclusion.
  let h18 := h15 h17
  -- We need to get the left conjuct of h18 based on <expert-advice>.
  let h19 := h18.left
  -- We need to get the left conjuct of h19 based on <expert-advice>.
  let h20 := h19.left
  -- We need to get the left conjuct of h20 based on <expert-advice>.
  let h21 := h20.left
  -- We need to get the right conjuct of h21 based on <expert-advice>.
  let h22 := h21.right
  -- We need to get the left conjuct of h22 based on <expert-advice>.
  let h23 := h22.left
  -- One of the premise coincides with the conclusion.
  exact h23



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_615908746911936739116178775872 : (((((p1 ∨ (p2 → ((((p3 → ((p5 ∨ p2) ∨ p1)) → p3) ∧ p2) → p5))) ∨ (True ∧ (p2 → (p2 ∧ ((p2 → False) → p5))))) ∨ True) ∨ p2) ∧ True) := by
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
theorem thm_5_vars_157957819601657728730382575249 : ((((((p2 ∧ (p2 ∨ p2)) ∧ p4) ∨ p4) → False) ∨ ((p4 → (p2 ∧ (p5 ∨ p5))) ∨ (True ∧ True))) ∨ (((False → (p4 ∧ p4)) → p5) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_148772026997914966360348958863 : (((((p5 ∧ (p1 → p4)) → p3) → p4) ∨ ((p5 ∨ p1) ∨ (((p5 ∨ (p1 ∧ p4)) ∧ (True ∨ p4)) ∧ p3))) ∨ (p2 → (p5 → (p1 ∨ True)))) := by
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
theorem thm_5_vars_174095133038677037938170519111 : ((((p2 ∧ (p5 → (False ∧ p1))) ∧ ((p1 ∨ p1) ∧ (p2 ∨ p2))) ∧ (p2 → p5)) → (p4 ∧ (p4 ∧ ((p3 ∨ (p4 ∧ p3)) → (p5 ∧ p4))))) := by
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
  let h6 := h4.left
  let h7 := h4.right
  -- Conjunctions on the left can always be decomposed.
  let h8 := h5.left
  let h9 := h5.right
  -- Disjunctions on the left can always be decomposed.
  cases h8
  case inl h10 =>
    -- Disjunctions on the left can always be decomposed.
    cases h9
    case inl h11 =>
      -- We want to use the implication h3 based on <expert-advice>. So we show its premise.
      have h12 : p2 := by
        -- One of the premise coincides with the conclusion.
        exact h11
      -- We have shown the premise of h3, we can now drive its conclusion.
      let h13 := h3 h12
      -- We want to use the implication h7 based on <expert-advice>. So we show its premise.
      have h14 : p5 := by
        -- One of the premise coincides with the conclusion.
        exact h13
      -- We have shown the premise of h7, we can now drive its conclusion.
      let h15 := h7 h14
      -- We need to get the left conjuct of h15 based on <expert-advice>.
      let h16 := h15.left
      -- False on the left can always be used.
      apply False.elim h16
    case inr h17 =>
      -- We want to use the implication h3 based on <expert-advice>. So we show its premise.
      have h18 : p2 := by
        -- One of the premise coincides with the conclusion.
        exact h17
      -- We have shown the premise of h3, we can now drive its conclusion.
      let h19 := h3 h18
      -- We want to use the implication h7 based on <expert-advice>. So we show its premise.
      have h20 : p5 := by
        -- One of the premise coincides with the conclusion.
        exact h19
      -- We have shown the premise of h7, we can now drive its conclusion.
      let h21 := h7 h20
      -- We need to get the left conjuct of h21 based on <expert-advice>.
      let h22 := h21.left
      -- False on the left can always be used.
      apply False.elim h22
  case inr h23 =>
    -- Disjunctions on the left can always be decomposed.
    cases h9
    case inl h24 =>
      -- We want to use the implication h3 based on <expert-advice>. So we show its premise.
      have h25 : p2 := by
        -- One of the premise coincides with the conclusion.
        exact h24
      -- We have shown the premise of h3, we can now drive its conclusion.
      let h26 := h3 h25
      -- We want to use the implication h7 based on <expert-advice>. So we show its premise.
      have h27 : p5 := by
        -- One of the premise coincides with the conclusion.
        exact h26
      -- We have shown the premise of h7, we can now drive its conclusion.
      let h28 := h7 h27
      -- We need to get the left conjuct of h28 based on <expert-advice>.
      let h29 := h28.left
      -- False on the left can always be used.
      apply False.elim h29
    case inr h30 =>
      -- We want to use the implication h3 based on <expert-advice>. So we show its premise.
      have h31 : p2 := by
        -- One of the premise coincides with the conclusion.
        exact h30
      -- We have shown the premise of h3, we can now drive its conclusion.
      let h32 := h3 h31
      -- We want to use the implication h7 based on <expert-advice>. So we show its premise.
      have h33 : p5 := by
        -- One of the premise coincides with the conclusion.
        exact h32
      -- We have shown the premise of h7, we can now drive its conclusion.
      let h34 := h7 h33
      -- We need to get the left conjuct of h34 based on <expert-advice>.
      let h35 := h34.left
      -- False on the left can always be used.
      apply False.elim h35
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Conjunctions on the left can always be decomposed.
  let h36 := h1.left
  let h37 := h1.right
  -- Conjunctions on the left can always be decomposed.
  let h38 := h36.left
  let h39 := h36.right
  -- Conjunctions on the left can always be decomposed.
  let h40 := h38.left
  let h41 := h38.right
  -- Conjunctions on the left can always be decomposed.
  let h42 := h39.left
  let h43 := h39.right
  -- Disjunctions on the left can always be decomposed.
  cases h42
  case inl h44 =>
    -- Disjunctions on the left can always be decomposed.
    cases h43
    case inl h45 =>
      -- We want to use the implication h37 based on <expert-advice>. So we show its premise.
      have h46 : p2 := by
        -- One of the premise coincides with the conclusion.
        exact h45
      -- We have shown the premise of h37, we can now drive its conclusion.
      let h47 := h37 h46
      -- We want to use the implication h41 based on <expert-advice>. So we show its premise.
      have h48 : p5 := by
        -- One of the premise coincides with the conclusion.
        exact h47
      -- We have shown the premise of h41, we can now drive its conclusion.
      let h49 := h41 h48
      -- We need to get the left conjuct of h49 based on <expert-advice>.
      let h50 := h49.left
      -- False on the left can always be used.
      apply False.elim h50
    case inr h51 =>
      -- We want to use the implication h37 based on <expert-advice>. So we show its premise.
      have h52 : p2 := by
        -- One of the premise coincides with the conclusion.
        exact h51
      -- We have shown the premise of h37, we can now drive its conclusion.
      let h53 := h37 h52
      -- We want to use the implication h41 based on <expert-advice>. So we show its premise.
      have h54 : p5 := by
        -- One of the premise coincides with the conclusion.
        exact h53
      -- We have shown the premise of h41, we can now drive its conclusion.
      let h55 := h41 h54
      -- We need to get the left conjuct of h55 based on <expert-advice>.
      let h56 := h55.left
      -- False on the left can always be used.
      apply False.elim h56
  case inr h57 =>
    -- Disjunctions on the left can always be decomposed.
    cases h43
    case inl h58 =>
      -- We want to use the implication h37 based on <expert-advice>. So we show its premise.
      have h59 : p2 := by
        -- One of the premise coincides with the conclusion.
        exact h58
      -- We have shown the premise of h37, we can now drive its conclusion.
      let h60 := h37 h59
      -- We want to use the implication h41 based on <expert-advice>. So we show its premise.
      have h61 : p5 := by
        -- One of the premise coincides with the conclusion.
        exact h60
      -- We have shown the premise of h41, we can now drive its conclusion.
      let h62 := h41 h61
      -- We need to get the left conjuct of h62 based on <expert-advice>.
      let h63 := h62.left
      -- False on the left can always be used.
      apply False.elim h63
    case inr h64 =>
      -- We want to use the implication h37 based on <expert-advice>. So we show its premise.
      have h65 : p2 := by
        -- One of the premise coincides with the conclusion.
        exact h64
      -- We have shown the premise of h37, we can now drive its conclusion.
      let h66 := h37 h65
      -- We want to use the implication h41 based on <expert-advice>. So we show its premise.
      have h67 : p5 := by
        -- One of the premise coincides with the conclusion.
        exact h66
      -- We have shown the premise of h41, we can now drive its conclusion.
      let h68 := h41 h67
      -- We need to get the left conjuct of h68 based on <expert-advice>.
      let h69 := h68.left
      -- False on the left can always be used.
      apply False.elim h69
  -- Implications on the right can always be decomposed.
  intro h70
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Disjunctions on the left can always be decomposed.
  cases h70
  case inl h71 =>
    -- Conjunctions on the left can always be decomposed.
    let h72 := h1.left
    let h73 := h1.right
    -- Conjunctions on the left can always be decomposed.
    let h74 := h72.left
    let h75 := h72.right
    -- Conjunctions on the left can always be decomposed.
    let h76 := h74.left
    let h77 := h74.right
    -- Conjunctions on the left can always be decomposed.
    let h78 := h75.left
    let h79 := h75.right
    -- Disjunctions on the left can always be decomposed.
    cases h78
    case inl h80 =>
      -- Disjunctions on the left can always be decomposed.
      cases h79
      case inl h81 =>
        -- We want to use the implication h73 based on <expert-advice>. So we show its premise.
        have h82 : p2 := by
          -- One of the premise coincides with the conclusion.
          exact h81
        -- We have shown the premise of h73, we can now drive its conclusion.
        let h83 := h73 h82
        -- One of the premise coincides with the conclusion.
        exact h83
      case inr h84 =>
        -- We want to use the implication h73 based on <expert-advice>. So we show its premise.
        have h85 : p2 := by
          -- One of the premise coincides with the conclusion.
          exact h84
        -- We have shown the premise of h73, we can now drive its conclusion.
        let h86 := h73 h85
        -- One of the premise coincides with the conclusion.
        exact h86
    case inr h87 =>
      -- Disjunctions on the left can always be decomposed.
      cases h79
      case inl h88 =>
        -- We want to use the implication h73 based on <expert-advice>. So we show its premise.
        have h89 : p2 := by
          -- One of the premise coincides with the conclusion.
          exact h88
        -- We have shown the premise of h73, we can now drive its conclusion.
        let h90 := h73 h89
        -- One of the premise coincides with the conclusion.
        exact h90
      case inr h91 =>
        -- We want to use the implication h73 based on <expert-advice>. So we show its premise.
        have h92 : p2 := by
          -- One of the premise coincides with the conclusion.
          exact h91
        -- We have shown the premise of h73, we can now drive its conclusion.
        let h93 := h73 h92
        -- One of the premise coincides with the conclusion.
        exact h93
  case inr h94 =>
    -- Conjunctions on the left can always be decomposed.
    let h95 := h94.left
    let h96 := h94.right
    -- Conjunctions on the left can always be decomposed.
    let h97 := h1.left
    let h98 := h1.right
    -- Conjunctions on the left can always be decomposed.
    let h99 := h97.left
    let h100 := h97.right
    -- Conjunctions on the left can always be decomposed.
    let h101 := h99.left
    let h102 := h99.right
    -- Conjunctions on the left can always be decomposed.
    let h103 := h100.left
    let h104 := h100.right
    -- Disjunctions on the left can always be decomposed.
    cases h103
    case inl h105 =>
      -- Disjunctions on the left can always be decomposed.
      cases h104
      case inl h106 =>
        -- We want to use the implication h98 based on <expert-advice>. So we show its premise.
        have h107 : p2 := by
          -- One of the premise coincides with the conclusion.
          exact h106
        -- We have shown the premise of h98, we can now drive its conclusion.
        let h108 := h98 h107
        -- One of the premise coincides with the conclusion.
        exact h108
      case inr h109 =>
        -- We want to use the implication h98 based on <expert-advice>. So we show its premise.
        have h110 : p2 := by
          -- One of the premise coincides with the conclusion.
          exact h109
        -- We have shown the premise of h98, we can now drive its conclusion.
        let h111 := h98 h110
        -- One of the premise coincides with the conclusion.
        exact h111
    case inr h112 =>
      -- Disjunctions on the left can always be decomposed.
      cases h104
      case inl h113 =>
        -- We want to use the implication h98 based on <expert-advice>. So we show its premise.
        have h114 : p2 := by
          -- One of the premise coincides with the conclusion.
          exact h113
        -- We have shown the premise of h98, we can now drive its conclusion.
        let h115 := h98 h114
        -- One of the premise coincides with the conclusion.
        exact h115
      case inr h116 =>
        -- We want to use the implication h98 based on <expert-advice>. So we show its premise.
        have h117 : p2 := by
          -- One of the premise coincides with the conclusion.
          exact h116
        -- We have shown the premise of h98, we can now drive its conclusion.
        let h118 := h98 h117
        -- One of the premise coincides with the conclusion.
        exact h118
  -- Disjunctions on the left can always be decomposed.
  cases h70
  case inl h119 =>
    -- Conjunctions on the left can always be decomposed.
    let h120 := h1.left
    let h121 := h1.right
    -- Conjunctions on the left can always be decomposed.
    let h122 := h120.left
    let h123 := h120.right
    -- Conjunctions on the left can always be decomposed.
    let h124 := h122.left
    let h125 := h122.right
    -- Conjunctions on the left can always be decomposed.
    let h126 := h123.left
    let h127 := h123.right
    -- Disjunctions on the left can always be decomposed.
    cases h126
    case inl h128 =>
      -- Disjunctions on the left can always be decomposed.
      cases h127
      case inl h129 =>
        -- We want to use the implication h121 based on <expert-advice>. So we show its premise.
        have h130 : p2 := by
          -- One of the premise coincides with the conclusion.
          exact h129
        -- We have shown the premise of h121, we can now drive its conclusion.
        let h131 := h121 h130
        -- We want to use the implication h125 based on <expert-advice>. So we show its premise.
        have h132 : p5 := by
          -- One of the premise coincides with the conclusion.
          exact h131
        -- We have shown the premise of h125, we can now drive its conclusion.
        let h133 := h125 h132
        -- We need to get the left conjuct of h133 based on <expert-advice>.
        let h134 := h133.left
        -- False on the left can always be used.
        apply False.elim h134
      case inr h135 =>
        -- We want to use the implication h121 based on <expert-advice>. So we show its premise.
        have h136 : p2 := by
          -- One of the premise coincides with the conclusion.
          exact h135
        -- We have shown the premise of h121, we can now drive its conclusion.
        let h137 := h121 h136
        -- We want to use the implication h125 based on <expert-advice>. So we show its premise.
        have h138 : p5 := by
          -- One of the premise coincides with the conclusion.
          exact h137
        -- We have shown the premise of h125, we can now drive its conclusion.
        let h139 := h125 h138
        -- We need to get the left conjuct of h139 based on <expert-advice>.
        let h140 := h139.left
        -- False on the left can always be used.
        apply False.elim h140
    case inr h141 =>
      -- Disjunctions on the left can always be decomposed.
      cases h127
      case inl h142 =>
        -- We want to use the implication h121 based on <expert-advice>. So we show its premise.
        have h143 : p2 := by
          -- One of the premise coincides with the conclusion.
          exact h142
        -- We have shown the premise of h121, we can now drive its conclusion.
        let h144 := h121 h143
        -- We want to use the implication h125 based on <expert-advice>. So we show its premise.
        have h145 : p5 := by
          -- One of the premise coincides with the conclusion.
          exact h144
        -- We have shown the premise of h125, we can now drive its conclusion.
        let h146 := h125 h145
        -- We need to get the left conjuct of h146 based on <expert-advice>.
        let h147 := h146.left
        -- False on the left can always be used.
        apply False.elim h147
      case inr h148 =>
        -- We want to use the implication h121 based on <expert-advice>. So we show its premise.
        have h149 : p2 := by
          -- One of the premise coincides with the conclusion.
          exact h148
        -- We have shown the premise of h121, we can now drive its conclusion.
        let h150 := h121 h149
        -- We want to use the implication h125 based on <expert-advice>. So we show its premise.
        have h151 : p5 := by
          -- One of the premise coincides with the conclusion.
          exact h150
        -- We have shown the premise of h125, we can now drive its conclusion.
        let h152 := h125 h151
        -- We need to get the left conjuct of h152 based on <expert-advice>.
        let h153 := h152.left
        -- False on the left can always be used.
        apply False.elim h153
  case inr h154 =>
    -- Conjunctions on the left can always be decomposed.
    let h155 := h154.left
    let h156 := h154.right
    -- Conjunctions on the left can always be decomposed.
    let h157 := h1.left
    let h158 := h1.right
    -- Conjunctions on the left can always be decomposed.
    let h159 := h157.left
    let h160 := h157.right
    -- Conjunctions on the left can always be decomposed.
    let h161 := h159.left
    let h162 := h159.right
    -- Conjunctions on the left can always be decomposed.
    let h163 := h160.left
    let h164 := h160.right
    -- Disjunctions on the left can always be decomposed.
    cases h163
    case inl h165 =>
      -- Disjunctions on the left can always be decomposed.
      cases h164
      case inl h166 =>
        -- One of the premise coincides with the conclusion.
        exact h155
      case inr h167 =>
        -- One of the premise coincides with the conclusion.
        exact h155
    case inr h168 =>
      -- Disjunctions on the left can always be decomposed.
      cases h164
      case inl h169 =>
        -- One of the premise coincides with the conclusion.
        exact h155
      case inr h170 =>
        -- One of the premise coincides with the conclusion.
        exact h155



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_15255577683783287697790853049 : (((p5 → ((((False ∧ (p4 ∧ p2)) → (True ∨ (p5 ∨ True))) ∧ (((p1 ∨ ((False ∧ p3) → p4)) ∧ p3) → False)) ∨ p4)) ∨ (False ∨ True)) ∧ True) := by
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



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_160694980433888372812540322766 : (((p4 ∨ (p1 → ((p1 ∨ p2) ∧ (False ∧ p3)))) ∧ ((p4 ∨ (p2 ∧ True)) ∨ (p4 ∨ (p4 ∨ p3)))) → ((p5 → p3) → (True → (False ∨ True)))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Implications on the right can always be decomposed.
  intro h3
  -- Conjunctions on the left can always be decomposed.
  let h4 := h1.left
  let h5 := h1.right
  -- Disjunctions on the left can always be decomposed.
  cases h4
  case inl h6 =>
    -- Disjunctions on the left can always be decomposed.
    cases h5
    case inl h7 =>
      -- Disjunctions on the left can always be decomposed.
      cases h7
      case inl h8 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- True on the right can always be proven directly.
        apply True.intro
      case inr h9 =>
        -- Conjunctions on the left can always be decomposed.
        let h10 := h9.left
        let h11 := h9.right
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- True on the right can always be proven directly.
        apply True.intro
    case inr h12 =>
      -- Disjunctions on the left can always be decomposed.
      cases h12
      case inl h13 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- True on the right can always be proven directly.
        apply True.intro
      case inr h14 =>
        -- Disjunctions on the left can always be decomposed.
        cases h14
        case inl h15 =>
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- True on the right can always be proven directly.
          apply True.intro
        case inr h16 =>
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- True on the right can always be proven directly.
          apply True.intro
  case inr h17 =>
    -- Disjunctions on the left can always be decomposed.
    cases h5
    case inl h18 =>
      -- Disjunctions on the left can always be decomposed.
      cases h18
      case inl h19 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- True on the right can always be proven directly.
        apply True.intro
      case inr h20 =>
        -- Conjunctions on the left can always be decomposed.
        let h21 := h20.left
        let h22 := h20.right
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- True on the right can always be proven directly.
        apply True.intro
    case inr h23 =>
      -- Disjunctions on the left can always be decomposed.
      cases h23
      case inl h24 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- True on the right can always be proven directly.
        apply True.intro
      case inr h25 =>
        -- Disjunctions on the left can always be decomposed.
        cases h25
        case inl h26 =>
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- True on the right can always be proven directly.
          apply True.intro
        case inr h27 =>
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- True on the right can always be proven directly.
          apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_263388144817296447796225394801 : (True ∧ ((((p4 → ((p4 → p1) ∧ ((p2 ∨ p2) → ((p3 ∨ (p4 → (p1 ∧ p3))) ∧ False)))) ∨ True) ∨ (p4 ∨ p3)) ∨ (p4 ∧ (p3 → False)))) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_768991562761340113951378081270 : (((p5 ∧ ((p3 ∧ (False → p5)) ∧ ((p1 → ((p5 ∨ p3) ∨ ((True ∧ (((p5 ∧ True) ∧ False) → False)) ∧ (p5 → (p5 → False))))) ∧ True))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_191764924282698677413733531549 : ((p1 ∨ ((p1 ∨ ((p2 ∨ p2) ∧ (p2 ∧ p2))) ∨ p3)) ∨ (((True ∨ True) ∧ (((p3 ∧ (False ∧ False)) → ((p3 ∧ p2) ∧ True)) ∨ p2)) ∨ p2)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- Conjunctions on the left can always be decomposed.
  let h4 := h3.left
  let h5 := h3.right
  -- False on the left can always be used.
  apply False.elim h4
  -- Conjunctions on the left can always be decomposed.
  let h6 := h1.left
  let h7 := h1.right
  -- Conjunctions on the left can always be decomposed.
  let h8 := h7.left
  let h9 := h7.right
  -- False on the left can always be used.
  apply False.elim h8
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_829038834227415680275755824 : ((p5 ∧ ((((p5 ∨ (p3 ∨ (p1 ∧ (p5 ∨ ((p4 ∨ p3) ∧ ((True → p1) ∧ p1)))))) → True) → (p1 ∧ p2)) ∧ (p2 → p1))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_759889197720360057098079956002 : (((p2 ∧ ((p2 ∨ (p3 ∧ (p1 ∧ (False ∧ p1)))) ∧ ((p2 ∨ (p4 ∨ (p2 ∨ p5))) → ((True ∨ p2) → ((p4 ∨ p1) ∧ (p1 ∨ p5)))))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_234331139662932934100563356127 : ((p1 → (p4 ∧ p3)) → (((((p1 ∨ p5) ∨ (True ∧ p3)) ∧ False) ∧ (False ∨ p5)) ∨ (p2 → ((False → (p3 → True)) ∨ ((p4 ∧ p1) ∨ p1))))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h2
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h3
  -- Implications on the right can always be decomposed.
  intro h4
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_301009930004460172995784749390 : (False ∨ ((p2 → ((p4 ∨ (p5 ∧ False)) ∨ (((p5 → True) ∧ False) ∨ p1))) → ((p5 ∧ ((p5 → p2) ∧ True)) ∨ (p3 ∨ (p1 ∨ (p2 → p2)))))) := by
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
  -- Implications on the right can always be decomposed.
  intro h2
  -- One of the premise coincides with the conclusion.
  exact h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_194217175463088201442882837647 : ((p3 → (p4 ∧ ((((p5 ∧ p5) ∨ True) → p4) → p3))) → (((((p3 → p4) ∨ p3) ∨ ((p3 → ((p2 → True) → p2)) ∧ p4)) → p1) → p1)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
  have h3 : (((p3 → p4) ∨ p3) ∨ ((p3 → ((p2 → True) → p2)) ∧ p4)) := by
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Implications on the right can always be decomposed.
    intro h4
    -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
    have h5 : p3 := by
      -- One of the premise coincides with the conclusion.
      exact h4
    -- We have shown the premise of h1, we can now drive its conclusion.
    let h6 := h1 h5
    -- We need to get the left conjuct of h6 based on <expert-advice>.
    let h7 := h6.left
    -- One of the premise coincides with the conclusion.
    exact h7
  -- We have shown the premise of h2, we can now drive its conclusion.
  let h8 := h2 h3
  -- One of the premise coincides with the conclusion.
  exact h8



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_609312821620347301641182563187 : ((((((p5 ∨ p2) ∧ (p5 ∧ (False ∧ ((p1 → p3) → ((p5 ∧ ((p1 → p4) ∨ False)) ∧ (((p4 ∧ p1) → False) → p5)))))) ∨ p2) ∨ True) ∨ p4) ∧ True) := by
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
theorem thm_5_vars_717217058997035386126619538186 : ((((p2 ∨ (p1 ∨ (p2 ∧ p3))) ∧ ((p3 ∧ ((((True ∨ p3) ∨ (p1 ∧ (p4 ∨ (((p3 ∧ p3) ∧ True) → p4)))) ∨ p2) ∧ p3)) ∧ True)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_174942025818976269260731554356 : (((p4 → p1) → (p4 → ((False ∧ p4) ∨ (True → (p4 ∨ ((True → p3) ∨ False)))))) → ((p5 ∧ (p5 ∧ p5)) ∨ ((p3 ∧ p3) ∨ (p1 → True)))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h2
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_755132538590900476501368429115 : (((False ∧ (p2 → ((((p5 ∧ p1) ∨ False) ∧ (p5 ∧ ((((True → True) ∨ (p4 ∧ p5)) ∧ p4) ∨ (True ∧ p5)))) ∨ (p3 ∨ (p3 → True))))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_207770897549810177473769790023 : (((p3 ∨ (False ∧ (True ∨ True))) → p5) → (((p4 ∧ (((((p1 ∨ p1) ∨ (p2 ∨ p5)) ∨ ((p1 → True) ∧ p5)) ∧ p2) → p3)) ∨ p1) ∨ True)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_345938729400113192242781902501 : (p3 → (((((p1 ∧ p5) ∧ (False ∧ p4)) ∨ ((True ∧ ((p1 ∨ p1) ∨ True)) ∧ p3)) → (p4 ∧ ((False ∧ False) ∨ (p5 → (p1 → True))))) → p4)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
  have h3 : (((p1 ∧ p5) ∧ (False ∧ p4)) ∨ ((True ∧ ((p1 ∨ p1) ∨ True)) ∧ p3)) := by
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Conjunctions on the right can always be decomposed.
    apply And.intro
    -- Conjunctions on the right can always be decomposed.
    apply And.intro
    -- True on the right can always be proven directly.
    apply True.intro
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro
    -- One of the premise coincides with the conclusion.
    exact h1
  -- We have shown the premise of h2, we can now drive its conclusion.
  let h4 := h2 h3
  -- We need to get the left conjuct of h4 based on <expert-advice>.
  let h5 := h4.left
  -- One of the premise coincides with the conclusion.
  exact h5



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_110220998478324829920953462614 : ((p1 → (p4 → ((p4 ∨ ((((p1 → True) ∧ (((p2 → p4) ∨ False) ∨ True)) ∨ p4) ∧ (p1 ∨ p1))) → (p4 ∧ (p2 ∨ True))))) ∧ (p3 → True)) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Implications on the right can always be decomposed.
  intro h3
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Disjunctions on the left can always be decomposed.
  cases h3
  case inl h4 =>
    -- One of the premise coincides with the conclusion.
    exact h2
  case inr h5 =>
    -- Conjunctions on the left can always be decomposed.
    let h6 := h5.left
    let h7 := h5.right
    -- Disjunctions on the left can always be decomposed.
    cases h6
    case inl h8 =>
      -- Conjunctions on the left can always be decomposed.
      let h9 := h8.left
      let h10 := h8.right
      -- Disjunctions on the left can always be decomposed.
      cases h10
      case inl h11 =>
        -- Disjunctions on the left can always be decomposed.
        cases h11
        case inl h12 =>
          -- Disjunctions on the left can always be decomposed.
          cases h7
          case inl h13 =>
            -- One of the premise coincides with the conclusion.
            exact h2
          case inr h14 =>
            -- One of the premise coincides with the conclusion.
            exact h2
        case inr h15 =>
          -- False on the left can always be used.
          apply False.elim h15
      case inr h16 =>
        -- Disjunctions on the left can always be decomposed.
        cases h7
        case inl h17 =>
          -- One of the premise coincides with the conclusion.
          exact h2
        case inr h18 =>
          -- One of the premise coincides with the conclusion.
          exact h2
    case inr h19 =>
      -- Disjunctions on the left can always be decomposed.
      cases h7
      case inl h20 =>
        -- One of the premise coincides with the conclusion.
        exact h2
      case inr h21 =>
        -- One of the premise coincides with the conclusion.
        exact h2
  -- Disjunctions on the left can always be decomposed.
  cases h3
  case inl h22 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro
  case inr h23 =>
    -- Conjunctions on the left can always be decomposed.
    let h24 := h23.left
    let h25 := h23.right
    -- Disjunctions on the left can always be decomposed.
    cases h24
    case inl h26 =>
      -- Conjunctions on the left can always be decomposed.
      let h27 := h26.left
      let h28 := h26.right
      -- Disjunctions on the left can always be decomposed.
      cases h28
      case inl h29 =>
        -- Disjunctions on the left can always be decomposed.
        cases h29
        case inl h30 =>
          -- Disjunctions on the left can always be decomposed.
          cases h25
          case inl h31 =>
            -- Show the right disjunct based on <expert-advice>.
            apply Or.inr
            -- True on the right can always be proven directly.
            apply True.intro
          case inr h32 =>
            -- Show the right disjunct based on <expert-advice>.
            apply Or.inr
            -- True on the right can always be proven directly.
            apply True.intro
        case inr h33 =>
          -- False on the left can always be used.
          apply False.elim h33
      case inr h34 =>
        -- Disjunctions on the left can always be decomposed.
        cases h25
        case inl h35 =>
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- True on the right can always be proven directly.
          apply True.intro
        case inr h36 =>
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- True on the right can always be proven directly.
          apply True.intro
    case inr h37 =>
      -- Disjunctions on the left can always be decomposed.
      cases h25
      case inl h38 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- True on the right can always be proven directly.
        apply True.intro
      case inr h39 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- True on the right can always be proven directly.
        apply True.intro
  -- Implications on the right can always be decomposed.
  intro h40
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_657143177637877307165105327276 : (((((False ∧ (p2 → p4)) ∨ ((((((((p3 ∧ p2) ∨ (False ∧ p5)) ∧ p3) → p3) ∧ p3) → p1) ∧ p4) → (p1 ∨ p2))) ∨ (p4 ∧ p4)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_767336222513313234506107954571 : (((p5 ∧ (((((True → p2) → p3) ∧ p4) ∨ ((p1 ∧ p4) ∧ (True → ((((False → p5) ∧ (p1 ∧ p2)) → True) ∨ (False ∨ p1))))) ∧ p2)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_150249709719412569260183626969 : ((p3 → (((((((((False ∧ p4) ∧ p5) ∨ p5) ∧ p4) ∧ p4) → p1) ∨ True) ∨ p5) ∧ (p5 → (p1 → p4)))) ∨ ((False ∧ (p2 ∧ p5)) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_83974992766883289320544988804 : ((((((True ∨ p1) → (False ∨ (((p5 ∨ p1) ∨ False) ∧ (True → p3)))) → False) ∧ p3) ∧ ((((p5 ∨ True) → True) → p1) ∨ (p5 ∨ p1))) → p5) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- Conjunctions on the left can always be decomposed.
  let h4 := h2.left
  let h5 := h2.right
  -- Disjunctions on the left can always be decomposed.
  cases h3
  case inl h6 =>
    -- We want to use the implication h6 based on <expert-advice>. So we show its premise.
    have h7 : ((p5 ∨ True) → True) := by
      -- Implications on the right can always be decomposed.
      intro h8
      -- True on the right can always be proven directly.
      apply True.intro
    -- We have shown the premise of h6, we can now drive its conclusion.
    let h9 := h6 h7
    -- We want to use the implication h4 based on <expert-advice>. So we show its premise.
    have h10 : ((True ∨ p1) → (False ∨ (((p5 ∨ p1) ∨ False) ∧ (True → p3)))) := by
      -- Implications on the right can always be decomposed.
      intro h11
      -- Disjunctions on the left can always be decomposed.
      cases h11
      case inl h12 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- Conjunctions on the right can always be decomposed.
        apply And.intro
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- One of the premise coincides with the conclusion.
        exact h9
        -- Implications on the right can always be decomposed.
        intro h13
        -- One of the premise coincides with the conclusion.
        exact h5
      case inr h14 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- Conjunctions on the right can always be decomposed.
        apply And.intro
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- One of the premise coincides with the conclusion.
        exact h14
        -- Implications on the right can always be decomposed.
        intro h15
        -- One of the premise coincides with the conclusion.
        exact h5
    -- We have shown the premise of h4, we can now drive its conclusion.
    let h16 := h4 h10
    -- False on the left can always be used.
    apply False.elim h16
  case inr h17 =>
    -- Disjunctions on the left can always be decomposed.
    cases h17
    case inl h18 =>
      -- One of the premise coincides with the conclusion.
      exact h18
    case inr h19 =>
      -- We want to use the implication h4 based on <expert-advice>. So we show its premise.
      have h20 : ((True ∨ p1) → (False ∨ (((p5 ∨ p1) ∨ False) ∧ (True → p3)))) := by
        -- Implications on the right can always be decomposed.
        intro h21
        -- Disjunctions on the left can always be decomposed.
        cases h21
        case inl h22 =>
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- Conjunctions on the right can always be decomposed.
          apply And.intro
          -- Show the left disjunct based on <expert-advice>.
          apply Or.inl
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- One of the premise coincides with the conclusion.
          exact h19
          -- Implications on the right can always be decomposed.
          intro h23
          -- One of the premise coincides with the conclusion.
          exact h5
        case inr h24 =>
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- Conjunctions on the right can always be decomposed.
          apply And.intro
          -- Show the left disjunct based on <expert-advice>.
          apply Or.inl
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- One of the premise coincides with the conclusion.
          exact h24
          -- Implications on the right can always be decomposed.
          intro h25
          -- One of the premise coincides with the conclusion.
          exact h5
      -- We have shown the premise of h4, we can now drive its conclusion.
      let h26 := h4 h20
      -- False on the left can always be used.
      apply False.elim h26



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_134831727758839926826518006339 : (((p2 ∨ (((p4 ∨ p2) → (((((p1 → True) → ((p2 → p4) → (p2 → p1))) ∨ p1) ∨ p1) ∨ True)) → False)) → p3) ∨ (p4 → (p3 ∨ True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_148724059928675720264120110115 : (((p2 ∨ (((p2 ∧ p5) ∧ p5) ∨ (True ∧ p5))) → ((p2 ∧ (p5 ∧ (p2 → ((p4 ∨ p3) ∧ p3)))) ∧ False)) ∨ ((True → (p2 ∧ p3)) → True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_53762943741783282686720835683 : ((((p4 ∨ ((p5 ∧ (p4 → (p3 → True))) ∨ False)) ∧ True) ∨ ((((p1 ∧ ((p5 ∧ p1) → p4)) ∨ p4) → (p3 ∨ (p1 ∨ p2))) ∨ False)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_136510973971341053929982851210 : (((p4 ∧ (p5 ∧ p1)) ∧ (p3 ∧ (p5 ∨ (p2 ∨ ((p3 → p1) → ((p1 → False) ∧ ((p5 → (p4 → p3)) ∧ p3))))))) ∨ (p3 ∨ (True ∧ True))) := by
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
theorem thm_5_vars_174161113689507995687057440495 : (((((p3 ∨ p4) ∧ p1) ∧ (((p3 → p2) ∨ p1) ∨ (p2 → p4))) ∨ (p1 → p4)) → (((p5 ∧ (False ∧ False)) ∨ (p1 ∨ (p5 ∨ p4))) ∨ True)) := by
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
      -- Disjunctions on the left can always be decomposed.
      cases h4
      case inl h8 =>
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
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- True on the right can always be proven directly.
        apply True.intro
    case inr h12 =>
      -- Disjunctions on the left can always be decomposed.
      cases h4
      case inl h13 =>
        -- Disjunctions on the left can always be decomposed.
        cases h13
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
      case inr h16 =>
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
theorem thm_5_vars_345342489415418614287849090190 : (p3 → (((p3 ∧ (p4 ∨ ((((((p5 → False) ∧ (((p1 ∧ p4) → False) → True)) ∨ p2) ∧ (p1 ∨ p4)) ∧ (p1 ∧ p5)) → False))) ∧ p4) ∨ p3)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_64866119890334435994693458021 : ((p2 ∨ ((((p4 ∨ (p3 ∨ (False ∨ p4))) → p5) ∨ ((((False ∧ (p1 → p2)) ∧ p2) ∧ p1) ∧ ((p3 ∧ p2) ∧ False))) ∨ (False → p1))) ∨ p4) := by
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
theorem thm_5_vars_181664295003991570006890339175 : ((p4 → ((True → ((p3 ∨ (True ∧ ((p1 ∧ p2) ∨ True))) → p4)) ∧ p2)) → (p3 ∨ ((((p4 ∧ p4) ∧ ((p2 ∧ p4) → p1)) → p1) ∨ True))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_257491579995446635025921374729 : ((p3 ∨ False) → ((False ∨ ((((True ∨ p4) ∨ p5) → (((p2 → p5) ∧ p1) ∧ (((p2 ∨ p4) → False) ∧ p4))) ∧ ((p5 ∧ p4) → p5))) ∨ p3)) := by
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
    -- False on the left can always be used.
    apply False.elim h3



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_693155083737610406187508121315 : ((((p5 ∧ ((p4 ∨ (p4 ∨ (p4 ∨ p3))) → ((True ∨ (False ∨ p2)) ∨ p4))) ∧ (((p2 ∨ (p2 ∧ p5)) ∧ p3) ∨ ((True ∨ True) → p5))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_655141002683485232379702236447 : (((((False → (((((p2 → (p4 ∨ p5)) → (True ∨ (p4 ∨ False))) → ((False ∨ p1) → True)) ∨ p2) → (p3 → p3))) → p2) ∨ (p2 ∧ False)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_306175669308546655499050955464 : (p1 ∨ ((False ∧ (p2 ∨ False)) ∨ ((p4 → (((p5 ∧ p4) → (p3 ∨ p4)) ∨ (p2 → (p1 ∨ False)))) ∨ ((p3 ∨ p3) → ((p4 → p1) ∧ True))))) := by
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
  -- Implications on the right can always be decomposed.
  intro h2
  -- Conjunctions on the left can always be decomposed.
  let h3 := h2.left
  let h4 := h2.right
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h4



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_65716833376879579769316395976 : ((p4 ∨ ((((p3 ∧ p1) → (p4 ∨ p5)) → ((((p1 ∨ ((p2 ∧ False) → (False → (p5 → False)))) → p2) → p2) → p3)) ∨ (True ∨ p2))) ∨ False) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_594590229726750854451595754629 : (((((p3 ∨ ((p4 ∨ (p5 ∨ ((p1 → (((p2 ∧ p2) ∧ p3) ∨ p3)) ∧ p2))) ∨ False)) ∨ (p4 → ((False ∧ p1) ∨ (p1 ∧ p5)))) ∧ False) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_35182410469033938338254760006 : ((p1 → (((p2 ∨ p3) ∧ p4) ∨ ((True ∧ (p1 ∧ ((p3 ∨ (True ∨ p5)) ∧ p2))) ∨ ((p5 → ((p4 ∧ p1) → (True → p5))) ∨ p4)))) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h2
  -- Implications on the right can always be decomposed.
  intro h3
  -- Implications on the right can always be decomposed.
  intro h4
  -- Conjunctions on the left can always be decomposed.
  let h5 := h3.left
  let h6 := h3.right
  -- One of the premise coincides with the conclusion.
  exact h2
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_593133793968765552921231269554 : (((((((p4 → p1) → ((p2 ∧ (p5 ∨ (p3 → (False ∧ p2)))) ∧ True)) → (((False ∨ p4) ∧ p1) ∧ p5)) ∨ (p2 → (p5 → True))) ∧ p3) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_324158748868554565594390210836 : (p5 ∨ ((((p2 → True) → (p1 ∨ ((p1 → False) ∨ True))) ∧ True) ∨ (p1 ∧ ((p2 ∨ p1) ∧ ((p5 ∨ p5) ∨ ((p3 ∨ (p1 → p4)) ∧ p1)))))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_622547624200890431605328066580 : ((((p4 ∧ ((((p2 ∧ ((True → False) ∧ ((True → p4) ∨ (True ∨ p1)))) ∨ (p3 ∨ p5)) ∧ (((False ∧ True) → p5) ∨ p1)) ∧ p1)) ∨ True) ∨ p5) ∧ True) := by
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
theorem thm_5_vars_726587259248111441050369764013 : (((((True ∧ p5) → False) ∨ (((False ∧ (p4 ∧ p4)) ∨ p4) ∨ ((p1 → ((False → (p5 ∧ False)) ∨ ((p2 ∧ p2) → p2))) → (p3 → p2)))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_183833462796037480070571033177 : ((((p2 → ((p3 ∨ True) ∧ ((p3 → p1) ∨ False))) → p4) ∧ False) ∨ ((((p3 → (p2 ∧ (p1 ∨ p1))) → (p1 ∧ p2)) ∧ (p2 ∧ p1)) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_62941862862218590580320273087 : ((p4 ∧ (p4 ∧ (((p4 → (True → ((((p3 ∧ p1) ∨ ((p4 → (p4 ∧ p4)) → (p1 ∧ (p4 ∨ p3)))) ∨ p5) ∨ True))) → p2) → p4))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_138745216371503262340393729764 : (((((p2 ∧ p1) → p4) ∧ (False → (((False ∨ False) ∧ (((False ∨ (p2 ∧ (True → p3))) ∨ True) ∧ p3)) → p1))) ∧ p3) → ((p4 ∨ p4) ∨ True)) := by
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
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_157721525207014902401088180556 : ((((p4 ∧ p5) ∨ (p4 ∧ ((p2 → (True ∧ p1)) ∧ (False → (p4 ∧ p1))))) → (True → (p5 ∧ p5))) ∨ (((p2 ∨ p1) ∧ (False ∨ p3)) → True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_37440821614097402279892369158 : ((((((True ∧ True) ∨ ((p2 ∨ p3) ∨ ((p3 ∨ (p5 → p4)) ∨ ((p2 ∨ p5) → p3)))) → ((p5 ∨ (True ∨ p2)) ∧ p5)) ∨ p1) ∧ p3) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_139322572754032895575481868070 : (((p1 ∨ ((((p1 ∨ p2) → (True ∨ (p2 ∨ (p5 ∧ ((p4 → (p5 → p2)) ∧ False))))) ∨ False) ∨ (p2 ∧ p3))) ∨ p4) → (p4 ∨ (p1 ∨ True))) := by
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
      -- One of the premise coincides with the conclusion.
      exact h3
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
          -- True on the right can always be proven directly.
          apply True.intro
        case inr h7 =>
          -- False on the left can always be used.
          apply False.elim h7
      case inr h8 =>
        -- Conjunctions on the left can always be decomposed.
        let h9 := h8.left
        let h10 := h8.right
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- True on the right can always be proven directly.
        apply True.intro
  case inr h11 =>
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- One of the premise coincides with the conclusion.
    exact h11



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_184864554564129228459582148866 : ((((p1 → False) ∨ False) ∧ (((p3 → p2) → p5) → (p3 ∨ p4))) ∨ (((p1 → p5) → False) ∨ (((p1 ∧ p2) ∧ (False ∧ p3)) → (p2 → p5)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
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
  let h7 := h4.left
  let h8 := h4.right
  -- False on the left can always be used.
  apply False.elim h7



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_173330714563892006853790948862 : ((p2 → (((p2 → (p4 ∨ False)) → True) → (((p5 ∨ True) → p3) → (p3 ∨ True)))) ∨ (((True ∨ ((p4 → p2) ∧ p1)) → p1) ∧ (True ∨ True))) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Implications on the right can always be decomposed.
  intro h3
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_692684654134489590332017887691 : (((((((p1 ∨ False) ∧ p3) ∧ (p2 ∧ p2)) ∨ (p2 → ((p3 ∧ p2) ∧ p4))) ∧ (p3 ∨ (p2 ∧ (((p4 ∨ p2) → p4) ∨ (p1 → p1))))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_114552118951607918967534681128 : ((((((p1 ∧ p4) ∧ ((p1 ∨ (p2 ∧ (p5 → True))) ∨ (p3 → p5))) → p3) ∨ p1) ∧ (p1 ∨ ((p5 ∧ (p3 ∧ p5)) ∨ p4))) ∨ (False → False)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_647594012471058801947306696706 : ((((p5 → (((((p4 ∧ ((p4 ∨ ((((p4 ∨ p1) ∨ True) ∨ True) ∨ False)) → p5)) ∨ True) ∧ p4) ∧ (False ∨ p5)) → (p2 → p5))) → p2) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_238740814237386064946236269310 : ((p1 ∨ True) ∧ (((p3 ∧ (((p3 → ((p4 → (p4 ∨ p1)) → (False ∧ (p5 ∨ p2)))) → p3) ∧ False)) ∨ p2) ∨ (True ∨ (p4 ∧ (False ∧ p4))))) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_707538674013791323592493146451 : ((((((False ∧ p2) → p1) → ((p1 → p5) ∧ True)) ∨ ((True ∧ ((p1 ∨ (p5 ∨ (p3 ∧ p4))) ∨ False)) ∨ (p5 → (p3 ∨ (p1 → p3))))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_57763651597610373795058485737 : ((((p4 → p3) → p1) → ((((p3 ∧ False) ∨ p1) ∧ ((((p3 ∨ False) ∨ (False ∧ ((p4 ∧ (False ∨ False)) ∧ False))) ∨ p3) → False)) ∧ False)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_221733064802340519171717888838 : (((False ∧ p4) → False) ∧ ((True ∨ True) ∧ (p2 ∨ (p3 → (p5 ∨ (((p3 ∧ p2) → (p1 ∨ (p3 ∨ p2))) ∧ ((p5 ∨ (p3 → p5)) ∨ True))))))) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- False on the left can always be used.
  apply False.elim h2
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h4
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h5
  -- Conjunctions on the left can always be decomposed.
  let h6 := h5.left
  let h7 := h5.right
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- One of the premise coincides with the conclusion.
  exact h6
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_147769556208765012830428982439 : ((((p3 → p4) ∧ (((p5 → (True → ((True ∧ False) → p4))) ∨ ((p2 ∨ (p2 ∧ p5)) → p5)) → p4)) → p5) ∨ ((p4 → True) ∨ (False ∧ p3))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_674493283438195058296644742802 : ((((p4 ∨ ((p3 ∨ False) → (p4 → ((((True ∨ True) ∧ ((True ∧ p1) ∨ ((p5 ∧ p4) → p3))) ∧ p5) → p3)))) → (p2 ∧ (p5 ∨ p2))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_180079435730462973981730608063 : (((p5 → ((False ∧ ((p2 ∧ (p1 ∧ p3)) ∧ (p5 ∧ True))) ∨ p1)) ∨ False) → ((p2 ∨ (((False ∧ p5) ∧ ((False ∨ p2) → p5)) ∨ p2)) ∨ True)) := by
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
    -- False on the left can always be used.
    apply False.elim h3



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_612613552107096480624192939262 : (((((((p5 ∧ (((p4 ∨ False) ∨ (((p3 → (True ∨ p2)) ∨ p2) ∧ False)) ∧ p4)) ∨ (p5 ∧ p3)) ∨ (True ∨ p2)) ∨ (p5 ∨ p5)) ∨ p2) ∨ p4) ∧ True) := by
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
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_138644898776467783101388674989 : ((((p5 → ((p5 ∨ ((p2 → (p5 ∧ ((p5 ∧ p5) ∧ False))) ∨ p1)) ∨ (False → True))) ∧ ((False → p3) ∨ p3)) ∧ p1) → ((p3 ∧ p5) ∨ True)) := by
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
theorem thm_5_vars_75649478492484671791890469042 : (((((((p3 ∧ p2) ∧ True) ∧ ((True ∧ (p2 ∨ (p5 ∧ ((p2 → (False ∨ p3)) ∨ ((p5 ∧ p3) → True))))) ∨ False)) ∧ False) ∨ True) → p5) → p5) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h2 : (((((p3 ∧ p2) ∧ True) ∧ ((True ∧ (p2 ∨ (p5 ∧ ((p2 → (False ∨ p3)) ∨ ((p5 ∧ p3) → True))))) ∨ False)) ∧ False) ∨ True) := by
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h3 := h1 h2
  -- One of the premise coincides with the conclusion.
  exact h3



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_219172552889679435463109936978 : ((False ∨ ((p4 → p1) ∨ True)) → ((p4 ∨ p4) ∨ (((((True → (False → ((p5 ∨ p1) ∧ p1))) ∧ p5) ∧ (p4 ∧ False)) ∨ p4) ∨ (p4 → True)))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h2 =>
    -- False on the left can always be used.
    apply False.elim h2
  case inr h3 =>
    -- Disjunctions on the left can always be decomposed.
    cases h3
    case inl h4 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Implications on the right can always be decomposed.
      intro h5
      -- True on the right can always be proven directly.
      apply True.intro
    case inr h6 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Implications on the right can always be decomposed.
      intro h7
      -- True on the right can always be proven directly.
      apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_198396649811061417005885680682 : ((p3 ∧ (p5 ∨ (((p2 → p2) ∨ p5) ∨ False))) ∨ (p5 ∨ ((((((p3 → p3) ∨ ((p1 → p3) ∧ p4)) → p1) ∨ False) ∨ (True ∨ False)) ∨ p1))) := by
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
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_315464586770071031874594360531 : (p3 ∨ (((p1 ∧ True) ∨ p1) → (((True → p5) → p4) ∨ ((p2 → False) ∨ ((((p4 ∨ (p3 → (p1 ∧ p4))) → (p4 ∧ p2)) ∧ p3) → p1))))) := by
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
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h5
    -- Conjunctions on the left can always be decomposed.
    let h6 := h5.left
    let h7 := h5.right
    -- One of the premise coincides with the conclusion.
    exact h3
  case inr h8 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h9
    -- Conjunctions on the left can always be decomposed.
    let h10 := h9.left
    let h11 := h9.right
    -- One of the premise coincides with the conclusion.
    exact h8



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_709428086244220131458261290160 : ((((p2 ∧ (((p4 → (p5 ∨ p2)) ∨ p3) ∧ True)) → ((False → ((p2 ∧ p5) ∨ (((p3 ∧ False) ∧ p3) ∧ ((p3 ∨ p1) → True)))) → p5)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_68930789867930447855186419204 : ((p4 → (p3 ∨ (p3 ∨ ((((((True ∨ (p1 ∧ p5)) ∨ True) ∨ p4) ∧ ((True ∨ False) ∨ False)) ∨ ((p3 ∧ (True → p1)) ∨ p1)) ∧ p2)))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_135987320629410182589851252801 : (((((p5 ∨ True) ∨ (p3 → p1)) ∧ ((p2 ∧ p4) ∧ p3)) ∨ ((p2 ∨ p2) ∧ ((True ∧ (p4 → (True ∧ True))) ∧ True))) ∨ (p4 ∨ (False → False))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_785756659042206574060600650962 : (((p4 ∨ ((((True ∧ p2) ∨ True) → ((p4 ∨ ((p4 → p1) ∧ ((p5 ∨ p3) ∨ False))) ∧ (((p2 ∨ True) → False) ∧ (p3 ∨ p5)))) → p5)) ∨ p1) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h2 : ((True ∧ p2) ∨ True) := by
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h3 := h1 h2
  -- We need to get the right conjuct of h3 based on <expert-advice>.
  let h4 := h3.right
  -- We need to get the left conjuct of h4 based on <expert-advice>.
  let h5 := h4.left
  -- We want to use the implication h5 based on <expert-advice>. So we show its premise.
  have h6 : (p2 ∨ True) := by
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h5, we can now drive its conclusion.
  let h7 := h5 h6
  -- False on the left can always be used.
  apply False.elim h7
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_157091182093075188478055060577 : (((True → (((((p1 ∧ (p4 ∨ p3)) ∨ p1) ∨ p4) ∨ p2) → (((True → p1) ∧ False) ∧ p4))) ∨ p3) ∨ (False → ((True ∧ False) ∨ (p5 → p2)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_115037359492896232035877744378 : (((((p1 → False) ∧ ((p5 ∨ ((p5 ∧ p3) ∧ p2)) → p5)) ∧ False) ∨ (p4 → ((p5 → ((True → (p5 ∨ p3)) ∧ False)) ∨ p2))) ∨ (False → True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_664788509379219214633845226879 : ((((p1 → ((p2 → (((p5 → p3) ∧ p1) ∨ (False ∨ p1))) ∨ ((p1 ∧ (((False ∧ p5) ∧ True) ∨ (p3 ∧ False))) ∨ True))) → (p2 → False)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_677439544226007517200439572183 : (((((((((p4 ∨ False) ∨ (p5 → True)) → ((p4 → (p2 ∧ True)) ∨ p4)) → p4) → (p2 ∧ False)) ∨ p5) ∨ (p4 → ((False ∨ p4) ∨ p2))) ∨ p3) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_264984905656569215250942119703 : (True ∧ ((True → p5) → (((p1 ∨ (p1 ∨ (p3 → (p3 ∨ ((((p5 ∧ p5) → p1) → ((p3 ∨ p4) ∧ (True → False))) ∧ p5))))) → p4) ∨ True))) := by
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
theorem thm_5_vars_524252964069948172609284192206 : (((True ∧ (((False → p5) ∧ ((p5 → (p2 ∧ ((p5 ∨ p1) ∨ p5))) ∧ p3)) ∨ ((p5 → ((p3 ∧ p1) → p4)) → ((p4 ∨ p4) → p4)))) ∧ True) ∧ True) := by
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
  -- Implications on the right can always be decomposed.
  intro h1
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
theorem thm_5_vars_167822082308362522165991272540 : (((True ∨ ((p1 ∨ ((p1 ∨ (p3 → p5)) ∧ p3)) ∨ p4)) ∧ ((False ∨ p5) → (p3 ∨ p4))) → (p2 → ((p1 ∧ p1) ∨ (p2 → (p2 ∧ True))))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Conjunctions on the left can always be decomposed.
  let h3 := h1.left
  let h4 := h1.right
  -- Disjunctions on the left can always be decomposed.
  cases h3
  case inl h5 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h6
    -- Conjunctions on the right can always be decomposed.
    apply And.intro
    -- One of the premise coincides with the conclusion.
    exact h6
    -- True on the right can always be proven directly.
    apply True.intro
  case inr h7 =>
    -- Disjunctions on the left can always be decomposed.
    cases h7
    case inl h8 =>
      -- Disjunctions on the left can always be decomposed.
      cases h8
      case inl h9 =>
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- Conjunctions on the right can always be decomposed.
        apply And.intro
        -- One of the premise coincides with the conclusion.
        exact h9
        -- One of the premise coincides with the conclusion.
        exact h9
      case inr h10 =>
        -- Conjunctions on the left can always be decomposed.
        let h11 := h10.left
        let h12 := h10.right
        -- Disjunctions on the left can always be decomposed.
        cases h11
        case inl h13 =>
          -- Show the left disjunct based on <expert-advice>.
          apply Or.inl
          -- Conjunctions on the right can always be decomposed.
          apply And.intro
          -- One of the premise coincides with the conclusion.
          exact h13
          -- One of the premise coincides with the conclusion.
          exact h13
        case inr h14 =>
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- Implications on the right can always be decomposed.
          intro h15
          -- Conjunctions on the right can always be decomposed.
          apply And.intro
          -- One of the premise coincides with the conclusion.
          exact h15
          -- True on the right can always be proven directly.
          apply True.intro
    case inr h16 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Implications on the right can always be decomposed.
      intro h17
      -- Conjunctions on the right can always be decomposed.
      apply And.intro
      -- One of the premise coincides with the conclusion.
      exact h17
      -- True on the right can always be proven directly.
      apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_664926491018453877626688006032 : ((((p3 → ((p2 ∨ (p3 ∨ (p4 ∨ (False ∧ (p5 → ((False → p4) ∨ ((p2 ∧ p3) ∨ (p4 → p1)))))))) ∧ (p2 ∧ p4))) → (p3 → False)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_776429538111019487516012782171 : (((p1 ∨ (((p5 ∨ (((p4 → (((False ∧ p4) → ((p5 ∧ p2) → p4)) ∨ p2)) → p5) ∧ ((p5 ∧ (p1 ∨ p3)) ∧ p1))) ∨ p5) ∨ True)) ∨ p5) ∧ True) := by
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
theorem thm_5_vars_672046559377759695383204183709 : ((((((False ∨ ((p2 ∧ p2) → ((False → (p4 ∧ p3)) → ((True ∧ True) → p2)))) → ((p2 ∨ False) ∨ p2)) ∨ p1) → (False ∨ (p1 ∧ p5))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_191625657308713042351985956817 : ((p3 ∧ (False → ((p1 ∧ (p3 ∧ (True ∧ p1))) → p4))) ∨ (p2 → (((p5 ∧ True) ∨ (((p4 → p4) ∨ (p1 ∨ p2)) → (p5 ∨ p2))) ∨ True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_111789662318100666094550574106 : (((((p5 ∧ p4) ∧ (p4 → ((p4 → (((p1 ∨ ((True → p1) ∧ p2)) → p1) ∧ False)) ∨ (True → False)))) ∨ (p4 → p3)) ∨ p2) ∨ (False → p5)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_62647514729376488926911420496 : ((p4 ∧ ((((p3 → p4) → (((p5 ∧ True) ∧ False) ∧ ((p1 → (((p4 ∨ (p5 → p4)) ∧ p4) ∧ (p4 ∧ p4))) ∨ False))) ∧ p3) ∨ p5)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



