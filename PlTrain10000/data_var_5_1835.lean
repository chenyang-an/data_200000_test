variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_198564066427552747876605227465 : ((p1 ∨ ((p1 → ((False → p3) ∧ p2)) → False)) ∨ (((True ∨ p1) ∨ (False ∨ (True ∨ (p4 ∨ ((True → p5) ∨ (p4 ∧ p2)))))) ∧ (p1 → True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_148263345703927965954962764093 : (((p3 ∨ ((((p1 → p2) ∧ p4) ∨ p4) → (p5 ∧ (p2 ∧ (False ∧ (p4 ∧ True)))))) ∨ ((p1 ∧ p3) ∨ p5)) ∨ (True ∨ (p4 → (p4 → p1)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_41208859600284105921241373445 : ((((p3 → ((False ∧ ((p3 ∧ (p1 ∨ (p2 ∧ False))) → ((p3 ∨ p4) ∨ ((p3 ∧ p3) ∨ p5)))) ∨ p1)) → ((p1 ∨ p3) → False)) ∨ True) ∨ p2) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_233617494806458348384486412371 : ((p2 ∨ (p3 ∧ p4)) → (((True → ((((p1 → (p5 ∧ (p1 ∧ False))) ∨ (p5 → p2)) ∨ p4) ∧ ((p2 ∨ (True ∧ p3)) ∨ p2))) ∨ p1) ∨ p2)) := by
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
    -- Conjunctions on the left can always be decomposed.
    let h4 := h3.left
    let h5 := h3.right
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Implications on the right can always be decomposed.
    intro h6
    -- Conjunctions on the right can always be decomposed.
    apply And.intro
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h5
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Conjunctions on the right can always be decomposed.
    apply And.intro
    -- True on the right can always be proven directly.
    apply True.intro
    -- One of the premise coincides with the conclusion.
    exact h4



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_179200438470828271229669846924 : ((p3 ∧ (p4 ∨ (((True ∧ ((p1 ∨ (True ∧ p2)) → p2)) ∨ p5) ∧ p5))) ∨ ((False ∨ True) ∨ (p2 ∧ (((p2 ∧ False) ∨ True) ∧ (p3 ∧ True))))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_608738932660026759951260999210 : (((((((False ∨ ((p3 ∨ p5) ∨ ((p2 ∧ (p2 ∨ False)) ∧ (((p1 ∧ False) → p5) → p3)))) ∧ p4) ∧ (p1 ∧ (p3 ∧ p5))) ∨ p2) ∨ True) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_149542027402123816389651502655 : ((p2 ∧ (((True → ((((p3 ∧ True) ∨ (p1 ∧ ((p2 → p4) → p5))) ∧ True) → p5)) ∨ (False → p1)) → p1)) ∨ (p4 ∨ (p2 → (p5 ∨ True)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_56121387349996736030935516775 : ((((p2 ∨ p5) ∨ (p2 ∨ p5)) ∨ (((p2 ∧ (p4 → (p4 → ((((p1 ∧ (p2 ∨ p1)) → p2) ∨ True) ∧ p2)))) ∨ (p2 ∨ True)) → p2)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_56027548083683128482950250579 : ((((p3 ∧ (p3 ∨ p2)) ∨ p3) ∨ (((p1 ∨ p5) ∨ ((p4 ∨ (False → (p2 → ((p2 ∨ ((p4 → p2) → p3)) → p5)))) → p2)) ∧ p2)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_655937289292561478143817406454 : (((((((True → p1) ∧ p5) ∧ (p4 → (p5 ∨ (p5 ∧ ((p5 ∨ p4) → (p1 → p4)))))) ∧ (((False ∨ True) ∧ True) ∨ p4)) ∨ (True ∧ p5)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_105715333385593151736348496356 : ((((False ∨ (((p5 ∧ p3) ∧ p3) ∨ ((p4 ∨ p3) → (p1 → p2)))) ∧ (p2 ∨ p1)) ∨ ((p4 → (True ∧ (True ∧ True))) ∨ True)) ∧ (p3 ∨ True)) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_325627808364385468664712700481 : (p5 ∨ (False ∨ ((((p2 ∧ True) ∨ p3) ∧ ((((p5 → ((p4 ∧ p2) → p4)) ∧ p4) → ((True → p4) → p1)) ∧ p1)) ∨ (p3 → (False → False))))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
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
theorem thm_5_vars_42575729548967696853947132762 : (((p2 ∨ ((((p4 ∨ (p1 ∧ p4)) ∨ ((True ∨ p5) ∨ (((p2 → (p5 → True)) ∧ (p2 ∨ p1)) → p5))) → p1) ∧ (True ∨ False))) ∨ p1) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_204156321347141188656758620563 : (((((p3 ∨ False) ∨ p3) ∨ p1) ∧ p5) ∨ (p3 → (((((((False ∨ p5) → ((p4 ∨ p3) ∨ p4)) ∧ (False ∧ p3)) ∧ p5) → False) ∧ p1) → True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_347306475382662911300724408277 : (p3 → ((((p4 ∧ (False ∧ (p4 → p4))) → (False ∧ p2)) ∨ p2) → (((((((p4 ∨ p4) → p5) ∧ p3) ∧ (p3 ∨ p4)) ∧ True) ∨ True) ∨ p1))) := by
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
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_47881170859174097387474105399 : (((((p1 ∧ ((p4 ∨ ((p5 ∨ ((((p5 ∧ p1) ∧ (p2 ∨ True)) → p2) → p2)) → p3)) ∨ False)) ∧ p3) ∨ (p4 ∨ True)) → (p4 → p5)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_64308172678090956696274005169 : ((p1 ∨ ((((p5 ∨ (p3 ∧ False)) ∧ (((p5 ∧ p3) ∧ False) ∨ ((p1 ∧ ((p2 ∧ p4) → True)) ∧ ((p5 ∨ p5) → p2)))) ∧ p3) ∧ False)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_653796699275709816003330774166 : ((((((((p2 ∨ (True → (p3 ∧ (True → p5)))) ∧ ((p4 ∨ p1) → p1)) ∨ True) → ((True ∨ p4) ∧ (False ∧ p1))) ∧ p2) ∨ (p2 → p2)) ∨ False) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- One of the premise coincides with the conclusion.
  exact h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_712609891060525192403509708350 : (((((p3 ∨ (p2 → p4)) → (p3 ∧ p5)) ∨ ((p2 ∨ p5) → ((p5 ∧ (p3 ∧ (p1 ∧ (p3 → p3)))) ∨ (True ∧ ((p3 ∧ p3) → p5))))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_191829776254456598276277255498 : ((p3 ∨ ((False ∨ ((p2 ∨ (p4 → p5)) → False)) ∨ p4)) ∨ ((p1 ∧ p2) → ((p2 ∧ True) ∧ (p5 ∨ (True ∧ (((p4 ∨ p5) ∨ True) ∨ p4)))))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- One of the premise coincides with the conclusion.
  exact h3
  -- True on the right can always be proven directly.
  apply True.intro
  -- Conjunctions on the left can always be decomposed.
  let h4 := h1.left
  let h5 := h1.right
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_41524717332131345776418959202 : ((((p1 ∧ ((p4 ∨ p5) → (p2 → (p1 ∨ (p3 ∨ True))))) ∧ ((True → ((p3 ∧ (p2 ∨ p3)) ∧ (p4 ∨ p4))) ∧ (p1 ∧ p5))) ∨ True) ∨ p1) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_631020559132022679480357547736 : (((((((((False ∨ ((((((p2 ∧ (p1 ∧ True)) ∧ p5) ∧ p3) → False) ∧ False) ∨ (False → p5))) → False) → p1) → p2) ∨ True) → p1) → p1) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_230231253893936560979882021819 : (((True ∨ p3) ∧ p2) → ((True → p2) → (((p1 ∧ (((((p1 ∨ ((p5 → p5) ∧ (p4 → p5))) ∧ True) ∨ False) ∨ p2) ∧ p1)) → p5) ∨ True))) := by
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
    -- True on the right can always be proven directly.
    apply True.intro
  case inr h6 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_113295326139758865904839500498 : ((((p1 → ((p3 ∨ (p2 ∨ (p1 ∧ p1))) → p2)) ∨ (((p1 ∨ p1) → p1) ∧ ((p1 ∨ (p4 → p2)) → p2))) ∧ (p5 ∨ p4)) ∨ (p2 ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_160972377813641664879995445153 : (((p1 ∨ (p1 ∨ p4)) ∧ (((p4 → p4) → False) ∧ (True ∨ ((p2 ∨ (p3 → (False → p2))) ∨ p3)))) → ((((p4 → p3) → True) → p2) → p2)) := by
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
    -- Conjunctions on the left can always be decomposed.
    let h6 := h4.left
    let h7 := h4.right
    -- Disjunctions on the left can always be decomposed.
    cases h7
    case inl h8 =>
      -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
      have h9 : ((p4 → p3) → True) := by
        -- Implications on the right can always be decomposed.
        intro h10
        -- True on the right can always be proven directly.
        apply True.intro
      -- We have shown the premise of h2, we can now drive its conclusion.
      let h11 := h2 h9
      -- One of the premise coincides with the conclusion.
      exact h11
    case inr h12 =>
      -- Disjunctions on the left can always be decomposed.
      cases h12
      case inl h13 =>
        -- Disjunctions on the left can always be decomposed.
        cases h13
        case inl h14 =>
          -- One of the premise coincides with the conclusion.
          exact h14
        case inr h15 =>
          -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
          have h16 : ((p4 → p3) → True) := by
            -- Implications on the right can always be decomposed.
            intro h17
            -- True on the right can always be proven directly.
            apply True.intro
          -- We have shown the premise of h2, we can now drive its conclusion.
          let h18 := h2 h16
          -- One of the premise coincides with the conclusion.
          exact h18
      case inr h19 =>
        -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
        have h20 : ((p4 → p3) → True) := by
          -- Implications on the right can always be decomposed.
          intro h21
          -- True on the right can always be proven directly.
          apply True.intro
        -- We have shown the premise of h2, we can now drive its conclusion.
        let h22 := h2 h20
        -- One of the premise coincides with the conclusion.
        exact h22
  case inr h23 =>
    -- Disjunctions on the left can always be decomposed.
    cases h23
    case inl h24 =>
      -- Conjunctions on the left can always be decomposed.
      let h25 := h4.left
      let h26 := h4.right
      -- Disjunctions on the left can always be decomposed.
      cases h26
      case inl h27 =>
        -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
        have h28 : ((p4 → p3) → True) := by
          -- Implications on the right can always be decomposed.
          intro h29
          -- True on the right can always be proven directly.
          apply True.intro
        -- We have shown the premise of h2, we can now drive its conclusion.
        let h30 := h2 h28
        -- One of the premise coincides with the conclusion.
        exact h30
      case inr h31 =>
        -- Disjunctions on the left can always be decomposed.
        cases h31
        case inl h32 =>
          -- Disjunctions on the left can always be decomposed.
          cases h32
          case inl h33 =>
            -- One of the premise coincides with the conclusion.
            exact h33
          case inr h34 =>
            -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
            have h35 : ((p4 → p3) → True) := by
              -- Implications on the right can always be decomposed.
              intro h36
              -- True on the right can always be proven directly.
              apply True.intro
            -- We have shown the premise of h2, we can now drive its conclusion.
            let h37 := h2 h35
            -- One of the premise coincides with the conclusion.
            exact h37
        case inr h38 =>
          -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
          have h39 : ((p4 → p3) → True) := by
            -- Implications on the right can always be decomposed.
            intro h40
            -- True on the right can always be proven directly.
            apply True.intro
          -- We have shown the premise of h2, we can now drive its conclusion.
          let h41 := h2 h39
          -- One of the premise coincides with the conclusion.
          exact h41
    case inr h42 =>
      -- Conjunctions on the left can always be decomposed.
      let h43 := h4.left
      let h44 := h4.right
      -- Disjunctions on the left can always be decomposed.
      cases h44
      case inl h45 =>
        -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
        have h46 : ((p4 → p3) → True) := by
          -- Implications on the right can always be decomposed.
          intro h47
          -- True on the right can always be proven directly.
          apply True.intro
        -- We have shown the premise of h2, we can now drive its conclusion.
        let h48 := h2 h46
        -- One of the premise coincides with the conclusion.
        exact h48
      case inr h49 =>
        -- Disjunctions on the left can always be decomposed.
        cases h49
        case inl h50 =>
          -- Disjunctions on the left can always be decomposed.
          cases h50
          case inl h51 =>
            -- One of the premise coincides with the conclusion.
            exact h51
          case inr h52 =>
            -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
            have h53 : ((p4 → p3) → True) := by
              -- Implications on the right can always be decomposed.
              intro h54
              -- True on the right can always be proven directly.
              apply True.intro
            -- We have shown the premise of h2, we can now drive its conclusion.
            let h55 := h2 h53
            -- One of the premise coincides with the conclusion.
            exact h55
        case inr h56 =>
          -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
          have h57 : ((p4 → p3) → True) := by
            -- Implications on the right can always be decomposed.
            intro h58
            -- True on the right can always be proven directly.
            apply True.intro
          -- We have shown the premise of h2, we can now drive its conclusion.
          let h59 := h2 h57
          -- One of the premise coincides with the conclusion.
          exact h59



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_206458096886857838703610798662 : ((p4 ∨ (p1 ∧ ((p3 ∧ False) ∧ False))) ∨ (p1 ∨ (((False ∧ p2) ∧ (p1 → (p1 → (((p2 ∧ p1) → p2) ∧ ((p5 ∧ p4) ∨ p5))))) → p2))) := by
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
  -- False on the left can always be used.
  apply False.elim h4



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_159091860473935773018029103090 : ((True → (((((p4 → p1) → p5) → ((p1 ∨ p1) ∨ True)) ∧ (p2 ∧ p4)) ∨ (p2 ∨ (p2 → p1)))) ∨ (p3 → (False → ((p3 ∧ True) ∧ p3)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- False on the left can always be used.
  apply False.elim h2
  -- True on the right can always be proven directly.
  apply True.intro
  -- False on the left can always be used.
  apply False.elim h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_350920405065603281197874693369 : (p4 → (((((False → False) → (True → p5)) → (p2 ∧ ((p1 → (False → p2)) → (False ∧ ((True → p3) ∨ (p5 ∧ p2)))))) ∨ p4) ∨ (p1 ∧ p1))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_40613183836495036715196691784 : (((((((True ∨ p4) ∨ (True ∧ p3)) ∨ (((p1 ∨ (False ∨ (p3 ∨ True))) ∨ False) ∨ (True ∧ ((p1 → p4) ∧ p3)))) ∨ p2) → p3) ∨ True) ∨ p4) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_311882498586348001085126178544 : (p2 ∨ (p2 ∨ ((p2 ∧ ((p2 ∧ (p4 → (((p1 ∨ (p5 ∨ (p1 → p2))) ∨ True) → (p4 ∨ True)))) ∧ p1)) ∨ ((True ∨ p1) → (p4 → p4))))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
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
    -- One of the premise coincides with the conclusion.
    exact h2
  case inr h4 =>
    -- One of the premise coincides with the conclusion.
    exact h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_137048225913485217945624355194 : (((False → p4) → ((((True → (False ∧ p5)) ∨ ((p1 ∧ (True ∧ (p1 ∨ p5))) → (True → False))) ∨ p1) ∨ (p1 ∧ p5))) ∨ (p3 ∨ (p2 → p2))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_160643286591178506763013889516 : ((((((p1 → (p2 ∧ False)) ∨ p4) ∧ (p4 ∨ p5)) ∧ True) → (p4 ∧ (False → (p5 → (p4 → p3))))) → (((p4 ∧ p2) → p5) ∨ (p2 → True))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h2
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_83259745336881703859342274554 : ((((p5 → ((p4 ∧ p3) ∨ ((((p1 ∧ p5) → False) → ((p5 → p2) ∧ p4)) → False))) → False) ∧ (False ∨ ((p1 ∨ p5) → (p2 ∧ False)))) → p2) := by
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
    -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
    have h6 : (p5 → ((p4 ∧ p3) ∨ ((((p1 ∧ p5) → False) → ((p5 → p2) ∧ p4)) → False))) := by
      -- Implications on the right can always be decomposed.
      intro h7
      -- We want to use the implication h5 based on <expert-advice>. So we show its premise.
      have h8 : (p1 ∨ p5) := by
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- One of the premise coincides with the conclusion.
        exact h7
      -- We have shown the premise of h5, we can now drive its conclusion.
      let h9 := h5 h8
      -- We need to get the right conjuct of h9 based on <expert-advice>.
      let h10 := h9.right
      -- False on the left can always be used.
      apply False.elim h10
    -- We have shown the premise of h2, we can now drive its conclusion.
    let h11 := h2 h6
    -- False on the left can always be used.
    apply False.elim h11



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_117406121888388610185528486924 : ((p1 ∧ ((((False ∨ (True ∨ p5)) ∨ ((((True ∧ (p5 → p4)) ∨ p5) ∧ p1) ∧ p1)) ∧ (p2 → ((p4 ∧ True) ∧ p5))) → p4)) ∨ (True ∨ False)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_134599797395273022256922753229 : (((((p1 ∨ p2) ∨ (p3 → ((p1 → (True ∧ ((p3 ∧ p2) ∨ p2))) ∧ (p3 ∨ (p1 → p1))))) → (p5 ∨ p3)) → p1) ∨ (False → (False ∨ p2))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_317837574449765637150569534492 : (p4 ∨ ((((True → True) → p1) ∨ (p1 → ((p4 ∨ (((p5 → True) ∧ p5) → False)) ∨ ((((p5 → p2) ∨ (False → p2)) ∨ p1) → p4)))) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_257672930955782499725178456761 : ((p3 ∨ p3) → (((p4 ∨ False) ∨ ((((p5 → (p2 → p2)) ∧ p5) ∧ p5) ∨ (p5 → (((p4 ∨ True) ∧ (p5 ∨ (p1 ∨ p3))) ∨ p5)))) ∨ p5)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h2 =>
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
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
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h5
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h5



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_257973183008150435567591711736 : ((p4 ∨ p1) → (((p1 ∨ ((p2 ∧ (False ∨ ((p3 → ((p1 ∧ ((p3 → p1) ∧ True)) ∧ ((p2 ∧ True) ∨ p4))) → p1))) → p1)) ∧ p1) ∨ True)) := by
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
theorem thm_5_vars_673839806352845760182870666421 : (((((p3 → True) ∨ (((((p2 ∨ (p1 → p3)) → (((p2 → p4) ∧ p5) ∧ (p3 → False))) ∧ p1) ∧ p5) ∨ p1)) → ((p2 ∨ False) ∧ p5)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_111230909176591557180509277535 : ((((p4 ∧ True) ∧ (p3 ∨ ((p5 → True) ∧ ((p3 → (p5 ∧ (p3 ∧ (p1 ∨ (((p1 → False) ∧ p3) ∧ p3))))) ∧ p3)))) ∧ p3) ∨ (True ∨ p1)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_3438193469311991913216649403 : (True ∧ (((p1 → p4) ∨ (((True → ((p1 → (p5 → False)) → p3)) ∧ p4) → p5)) → ((p3 ∧ False) ∨ (p2 → ((True → p1) → True))))) := by
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
    -- Implications on the right can always be decomposed.
    intro h3
    -- Implications on the right can always be decomposed.
    intro h4
    -- True on the right can always be proven directly.
    apply True.intro
  case inr h5 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h6
    -- Implications on the right can always be decomposed.
    intro h7
    -- True on the right can always be proven directly.
    apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_167907321645358047710845420540 : ((((p3 → p3) ∨ ((False ∨ (p1 → p2)) ∨ False)) ∧ (p3 ∨ (p4 ∧ (False → (p5 ∨ p5))))) → (((p3 ∧ (p1 ∨ p3)) ∧ (p4 ∨ p2)) ∨ True)) := by
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
      -- True on the right can always be proven directly.
      apply True.intro
    case inr h6 =>
      -- Conjunctions on the left can always be decomposed.
      let h7 := h6.left
      let h8 := h6.right
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- True on the right can always be proven directly.
      apply True.intro
  case inr h9 =>
    -- Disjunctions on the left can always be decomposed.
    cases h9
    case inl h10 =>
      -- Disjunctions on the left can always be decomposed.
      cases h10
      case inl h11 =>
        -- False on the left can always be used.
        apply False.elim h11
      case inr h12 =>
        -- Disjunctions on the left can always be decomposed.
        cases h3
        case inl h13 =>
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- True on the right can always be proven directly.
          apply True.intro
        case inr h14 =>
          -- Conjunctions on the left can always be decomposed.
          let h15 := h14.left
          let h16 := h14.right
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- True on the right can always be proven directly.
          apply True.intro
    case inr h17 =>
      -- False on the left can always be used.
      apply False.elim h17



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_149960240120844239867688064701 : ((p4 ∨ ((False ∨ (p1 ∨ ((False ∧ ((False ∨ ((p4 → p4) ∧ p1)) → p3)) ∧ ((True ∨ p1) → p1)))) ∨ True)) ∨ (((p1 ∨ p5) ∨ p5) → p4)) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_69041755327842746653986960401 : ((p5 → ((((((True ∧ p2) ∨ p2) ∧ p1) ∧ (False ∧ p1)) ∧ (((p5 ∧ False) → False) → (p3 ∨ (p1 ∧ (True ∧ (p3 ∧ p2)))))) ∨ p5)) ∨ p5) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_301889128372020239238173821637 : (False ∨ ((True ∧ p3) → ((((p4 ∨ ((False → ((False ∧ (p4 → p5)) ∧ True)) → (p3 ∨ p4))) → ((p2 → False) → p1)) ∨ p2) → (p1 ∨ p3)))) := by
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
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h5
  case inr h6 =>
    -- Conjunctions on the left can always be decomposed.
    let h7 := h1.left
    let h8 := h1.right
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h8



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_53183468510314382134968847082 : ((((p1 ∨ ((((True ∨ (True ∨ True)) ∨ p2) → p1) → False)) → False) ∨ (p3 → (((p1 ∧ p1) ∧ (False → (False → p5))) → (True ∨ p1)))) ∨ False) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Conjunctions on the left can always be decomposed.
  let h3 := h2.left
  let h4 := h2.right
  -- Conjunctions on the left can always be decomposed.
  let h5 := h3.left
  let h6 := h3.right
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_192039000209349933525447423592 : ((p2 → ((p1 ∨ True) → (p3 ∨ (p5 ∨ (p3 ∨ p2))))) ∨ (((True ∧ p2) ∨ (((p4 → True) ∧ ((True → p4) ∧ (True → p1))) ∨ p4)) ∧ p2)) := by
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
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h1
  case inr h4 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_657073813269651037222895416792 : (((((p2 ∨ (p1 ∨ False)) ∧ (p1 ∨ ((False ∨ (((p2 ∨ p4) ∧ p3) → True)) → (False ∧ (p5 ∨ (True ∧ (p1 ∧ True))))))) ∨ (False → p5)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_321542488707063034826558341970 : (p4 ∨ (p2 → (((True → (False ∧ (p2 ∧ (p1 ∨ (False ∧ False))))) ∧ ((True → (p1 ∨ ((p1 ∨ p1) → (p2 ∨ p5)))) ∧ (p4 ∧ True))) → p1))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Conjunctions on the left can always be decomposed.
  let h3 := h2.left
  let h4 := h2.right
  -- Conjunctions on the left can always be decomposed.
  let h5 := h4.left
  let h6 := h4.right
  -- Conjunctions on the left can always be decomposed.
  let h7 := h6.left
  let h8 := h6.right
  -- We want to use the implication h3 based on <expert-advice>. So we show its premise.
  have h9 : True := by
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h3, we can now drive its conclusion.
  let h10 := h3 h9
  -- We need to get the left conjuct of h10 based on <expert-advice>.
  let h11 := h10.left
  -- False on the left can always be used.
  apply False.elim h11



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_324416823591659349280260113054 : (p5 ∨ ((p5 ∧ (((False → p4) ∨ p2) → p2)) → ((p3 → p5) ∧ ((False ∧ ((p2 → True) ∧ (p1 ∨ p5))) ∨ (p2 ∧ ((p2 ∧ False) ∨ p2)))))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h2
  -- Conjunctions on the left can always be decomposed.
  let h3 := h1.left
  let h4 := h1.right
  -- One of the premise coincides with the conclusion.
  exact h3
  -- Conjunctions on the left can always be decomposed.
  let h5 := h1.left
  let h6 := h1.right
  -- We want to use the implication h6 based on <expert-advice>. So we show its premise.
  have h7 : ((False → p4) ∨ p2) := by
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Implications on the right can always be decomposed.
    intro h8
    -- False on the left can always be used.
    apply False.elim h8
  -- We have shown the premise of h6, we can now drive its conclusion.
  let h9 := h6 h7
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- One of the premise coincides with the conclusion.
  exact h9
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h9



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_635776956732083943818505993263 : (((((((p2 ∨ p2) ∨ ((p4 ∧ (p5 → ((p5 ∧ p4) → True))) ∨ (p1 ∨ p5))) ∨ (False → p4)) → ((p5 ∧ p2) ∧ (False ∧ False))) → p3) ∨ p3) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h2 : (((p2 ∨ p2) ∨ ((p4 ∧ (p5 → ((p5 ∧ p4) → True))) ∨ (p1 ∨ p5))) ∨ (False → p4)) := by
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h3
    -- False on the left can always be used.
    apply False.elim h3
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h4 := h1 h2
  -- We need to get the right conjuct of h4 based on <expert-advice>.
  let h5 := h4.right
  -- We need to get the left conjuct of h5 based on <expert-advice>.
  let h6 := h5.left
  -- False on the left can always be used.
  apply False.elim h6
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_252682781988110842488687973378 : ((p5 → p4) ∨ (p4 → (p1 → (((p4 → ((((p2 → (p2 ∧ False)) → p1) → p5) ∧ p3)) ∧ (p2 ∨ (True ∨ (p2 ∧ p3)))) ∨ (p4 ∨ True))))) := by
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
theorem thm_5_vars_42397756334870453587794847256 : (((p4 ∧ (p2 ∧ ((((p5 ∨ (((p1 → p1) ∧ ((p3 ∨ p3) → p1)) ∧ (p3 → p3))) ∨ p3) ∨ p2) ∨ (p5 ∨ (p5 ∧ p3))))) ∨ True) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_61877583880530366720717043357 : ((p2 ∧ (((((True → (p1 ∧ p5)) ∨ (((p2 ∨ ((False → p4) ∧ p5)) → False) ∨ p2)) ∧ p1) ∨ (p1 ∧ (p2 → p4))) ∧ (p1 ∨ True))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_341737308264660573780391946318 : (p2 → (((p3 ∨ p1) ∨ ((p5 ∧ ((((p4 → ((p5 → True) → True)) ∧ p5) → ((p2 → True) ∧ p1)) ∨ (p1 → p4))) ∧ p4)) ∨ (False → p3))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h2
  -- False on the left can always be used.
  apply False.elim h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_228186980109070785373970887307 : ((p5 ∧ (p3 ∧ p5)) ∨ (p3 ∨ ((p3 ∧ p3) ∨ (((True → False) → ((p5 ∨ p1) ∨ p3)) ∨ ((p2 ∧ p3) → (((p4 ∧ p5) → False) ∨ False)))))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
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
  -- False on the left can always be used.
  apply False.elim h3



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_10236861569908520363723643149 : (((p2 ∨ (p2 ∨ (((p3 → (((p5 ∨ ((p4 ∧ False) → p5)) ∧ (p1 ∧ p4)) ∨ (p4 ∨ p5))) ∧ (p5 → p4)) ∧ (True ∨ p2)))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_609799567618136488005096156445 : (((((True → ((p2 ∨ ((((p3 ∨ p4) ∧ ((((p5 ∨ p4) ∧ p3) → True) ∨ ((p4 → p2) → p3))) ∨ p5) ∧ p5)) → p4)) ∨ p5) ∨ p4) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_353876911953239666716129476542 : (p4 → (p1 → (p4 ∧ ((((((False → p1) ∧ p4) ∨ (p5 ∧ p2)) ∨ (p1 ∨ (True → True))) → ((True → ((False ∨ p2) ∧ True)) ∨ p2)) ∨ p1)))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- One of the premise coincides with the conclusion.
  exact h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_67931610695264224722049107533 : ((p2 → (((((p4 ∨ (p4 ∨ p3)) ∨ p3) ∨ p5) ∧ p2) ∨ (((((p5 ∧ p5) ∨ ((p4 → p3) → p2)) → False) ∨ False) → (False → p2)))) ∨ p3) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h2
  -- Implications on the right can always be decomposed.
  intro h3
  -- False on the left can always be used.
  apply False.elim h3



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_136936265648403779653589697994 : (((p3 → p4) ∨ (((p3 ∨ (p3 → ((p3 ∧ True) ∨ p4))) → p3) → ((((p4 → (p4 → p5)) → p5) → False) ∧ p4))) ∨ ((False ∨ False) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_660848299613517160980916699478 : (((((p3 ∧ (((p3 → ((p3 ∨ p3) ∧ p4)) → (p2 → p5)) ∧ (((p4 → (p1 ∧ False)) → (p1 ∧ p4)) → p1))) → False) → (p2 ∧ p3)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_936959292062846715485143316975 : ((((((False → True) ∨ (True → p2)) → False) ∧ ((((p5 → ((p5 → ((p4 ∧ True) ∨ (p2 ∧ (p3 → p5)))) → p4)) ∨ p3) → p3) ∧ p2)) → p5) ∧ True) := by
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
  have h6 : ((False → True) ∨ (True → p2)) := by
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Implications on the right can always be decomposed.
    intro h7
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h2, we can now drive its conclusion.
  let h8 := h2 h6
  -- False on the left can always be used.
  apply False.elim h8
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_115126884252164748355228985091 : ((((True ∧ ((p3 → p4) → p2)) ∧ (True ∨ (p3 ∨ (p2 → p1)))) → (((((p2 ∧ p2) ∨ (p5 ∨ p3)) ∨ True) ∧ p4) → p4)) ∨ (True → p5)) := by
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
    cases h5
    case inl h6 =>
      -- Conjunctions on the left can always be decomposed.
      let h7 := h6.left
      let h8 := h6.right
      -- Conjunctions on the left can always be decomposed.
      let h9 := h1.left
      let h10 := h1.right
      -- Conjunctions on the left can always be decomposed.
      let h11 := h9.left
      let h12 := h9.right
      -- Disjunctions on the left can always be decomposed.
      cases h10
      case inl h13 =>
        -- One of the premise coincides with the conclusion.
        exact h4
      case inr h14 =>
        -- Disjunctions on the left can always be decomposed.
        cases h14
        case inl h15 =>
          -- One of the premise coincides with the conclusion.
          exact h4
        case inr h16 =>
          -- One of the premise coincides with the conclusion.
          exact h4
    case inr h17 =>
      -- Disjunctions on the left can always be decomposed.
      cases h17
      case inl h18 =>
        -- Conjunctions on the left can always be decomposed.
        let h19 := h1.left
        let h20 := h1.right
        -- Conjunctions on the left can always be decomposed.
        let h21 := h19.left
        let h22 := h19.right
        -- Disjunctions on the left can always be decomposed.
        cases h20
        case inl h23 =>
          -- One of the premise coincides with the conclusion.
          exact h4
        case inr h24 =>
          -- Disjunctions on the left can always be decomposed.
          cases h24
          case inl h25 =>
            -- One of the premise coincides with the conclusion.
            exact h4
          case inr h26 =>
            -- One of the premise coincides with the conclusion.
            exact h4
      case inr h27 =>
        -- Conjunctions on the left can always be decomposed.
        let h28 := h1.left
        let h29 := h1.right
        -- Conjunctions on the left can always be decomposed.
        let h30 := h28.left
        let h31 := h28.right
        -- Disjunctions on the left can always be decomposed.
        cases h29
        case inl h32 =>
          -- One of the premise coincides with the conclusion.
          exact h4
        case inr h33 =>
          -- Disjunctions on the left can always be decomposed.
          cases h33
          case inl h34 =>
            -- One of the premise coincides with the conclusion.
            exact h4
          case inr h35 =>
            -- One of the premise coincides with the conclusion.
            exact h4
  case inr h36 =>
    -- Conjunctions on the left can always be decomposed.
    let h37 := h1.left
    let h38 := h1.right
    -- Conjunctions on the left can always be decomposed.
    let h39 := h37.left
    let h40 := h37.right
    -- Disjunctions on the left can always be decomposed.
    cases h38
    case inl h41 =>
      -- One of the premise coincides with the conclusion.
      exact h4
    case inr h42 =>
      -- Disjunctions on the left can always be decomposed.
      cases h42
      case inl h43 =>
        -- One of the premise coincides with the conclusion.
        exact h4
      case inr h44 =>
        -- One of the premise coincides with the conclusion.
        exact h4



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_117587469369047917961205390770 : ((p2 ∧ (p2 ∧ (((((True ∨ (((True → p4) ∧ p1) ∨ p4)) → (p3 ∧ (True ∨ (p5 ∨ p3)))) ∨ (True → p1)) ∧ True) ∨ p4))) ∨ (True ∨ p2)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_342573725133279722559053756182 : (p2 → (((((p3 ∧ True) ∧ True) ∨ (p5 → p2)) → ((p2 ∧ p5) ∧ False)) ∨ (p3 ∨ (p3 ∨ (((False → p5) ∨ (p5 ∧ p4)) ∧ (p2 ∧ p2)))))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h2
  -- False on the left can always be used.
  apply False.elim h2
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- One of the premise coincides with the conclusion.
  exact h1
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_147748173091003752460311548464 : (((((p4 → False) → p3) ∧ (p2 ∨ ((p2 ∨ False) → (p4 ∨ (((p2 ∧ p1) → p2) ∧ (p2 ∧ False)))))) → p2) ∨ (((p5 ∧ p3) ∧ p1) → p5)) := by
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
  exact h4



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_62883013337510334282026571516 : ((p4 ∧ ((p5 ∧ p4) ∧ (((p1 → ((p3 ∨ p4) ∧ ((True ∧ True) → (p1 ∨ p3)))) → ((p5 → (p2 → p3)) ∧ (p1 → p1))) ∧ p4))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_308487715360364332067604808134 : (p2 ∨ ((((p1 ∧ ((False ∨ p1) ∧ ((p2 → False) ∨ p1))) ∨ ((False ∨ ((False → p5) → False)) → (p5 ∧ p5))) ∨ (p4 → (False → p5))) ∨ p4)) := by
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
theorem thm_5_vars_45992602454573908743951823881 : ((((((p1 ∨ p2) ∨ (p2 → ((((p3 ∧ True) ∧ p2) ∨ (p4 → (((p5 ∧ p3) ∧ False) ∧ p2))) ∧ p1))) → False) ∧ p2) ∧ (p3 ∧ p3)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_227729431538963056798921900060 : ((p1 ∧ (True ∨ p3)) ∨ (((((p2 ∨ False) ∨ (p3 → (p5 ∨ ((True ∨ p5) → p2)))) ∧ p4) ∨ ((p2 → p2) ∨ (False ∨ p4))) ∧ (p4 ∨ True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- One of the premise coincides with the conclusion.
  exact h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_215819835406074731935970023613 : ((p2 ∨ ((False → True) ∧ False)) ∨ ((p1 ∨ p2) → ((((False → True) ∧ False) ∨ (p5 ∨ (p2 → p2))) ∨ (((p3 → p1) → (p1 ∨ p5)) ∨ False)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h2 =>
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h3
    -- One of the premise coincides with the conclusion.
    exact h3
  case inr h4 =>
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



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_262394474050479726603066260958 : (True ∧ (((p2 ∧ p1) → ((True ∧ ((p2 → ((((p1 ∨ p2) ∨ False) → False) ∨ (((p1 ∨ True) ∨ (p3 ∧ True)) ∨ p2))) → False)) ∨ p1)) ∨ p3)) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
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
theorem thm_5_vars_310042569257205131779814267095 : (p2 ∨ ((p2 ∨ ((False ∨ False) ∨ (p4 ∨ (((False ∧ ((p3 ∨ p5) ∧ False)) ∨ False) → p2)))) ∨ ((p2 ∨ (True ∧ ((p2 ∨ p3) ∨ p3))) ∧ True))) := by
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
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h2 =>
    -- Conjunctions on the left can always be decomposed.
    let h3 := h2.left
    let h4 := h2.right
    -- False on the left can always be used.
    apply False.elim h3
  case inr h5 =>
    -- False on the left can always be used.
    apply False.elim h5



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_50293050273780476853010250253 : ((((False ∧ (p5 ∧ (((p5 ∧ False) ∧ p4) ∨ (p4 ∨ (p4 ∧ (p2 ∨ True)))))) ∧ (p2 ∧ (False → p2))) ∨ (((p5 ∧ p5) ∧ p3) → True)) ∨ False) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_157091461360914521155129221189 : (((True → ((p4 ∧ (False ∧ (p3 ∨ True))) ∨ (((True ∧ ((p5 ∨ True) → False)) ∨ p1) → p1))) ∨ True) ∨ (True ∧ (p2 → (False → (p5 ∧ p4))))) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_306220010130171246030547102696 : (p1 ∨ (((p3 ∧ p5) ∨ p3) → (((p2 → ((p4 → p1) ∨ p1)) ∨ (((p3 ∧ p3) ∨ p5) ∨ ((p1 ∧ (True → p4)) → False))) ∨ (p3 ∧ p1)))) := by
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
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h4
  case inr h5 =>
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
    -- One of the premise coincides with the conclusion.
    exact h5
    -- One of the premise coincides with the conclusion.
    exact h5



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_192142966807029484231774386266 : ((p5 → (p3 ∨ (((p3 ∨ p4) → False) ∧ (p5 ∨ False)))) ∨ (p1 ∨ ((((True → p1) ∧ p2) ∧ (True → (p5 ∧ p5))) → (p5 ∨ (p2 ∧ p3))))) := by
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
  -- We want to use the implication h3 based on <expert-advice>. So we show its premise.
  have h6 : True := by
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h3, we can now drive its conclusion.
  let h7 := h3 h6
  -- We need to get the left conjuct of h7 based on <expert-advice>.
  let h8 := h7.left
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- One of the premise coincides with the conclusion.
  exact h8



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_189055040769783449351230678666 : ((((True ∨ p3) ∨ p5) → (p5 ∨ ((p2 ∨ p1) ∨ True))) ∧ (((p2 ∨ ((p1 → (p3 → p3)) ∨ ((p4 → p5) ∨ (False ∧ False)))) → p1) → p1)) := by
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
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- True on the right can always be proven directly.
      apply True.intro
    case inr h4 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- True on the right can always be proven directly.
      apply True.intro
  case inr h5 =>
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- One of the premise coincides with the conclusion.
    exact h5
  -- Implications on the right can always be decomposed.
  intro h6
  -- We want to use the implication h6 based on <expert-advice>. So we show its premise.
  have h7 : (p2 ∨ ((p1 → (p3 → p3)) ∨ ((p4 → p5) ∨ (False ∧ False)))) := by
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Implications on the right can always be decomposed.
    intro h8
    -- Implications on the right can always be decomposed.
    intro h9
    -- One of the premise coincides with the conclusion.
    exact h9
  -- We have shown the premise of h6, we can now drive its conclusion.
  let h10 := h6 h7
  -- One of the premise coincides with the conclusion.
  exact h10



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_751978114351632435871980517981 : (((True ∧ (p4 ∨ (p1 ∨ ((p5 → (((p3 ∨ p1) ∧ ((((p5 ∧ True) → False) ∨ (p4 ∧ (p1 ∨ p4))) → (p5 ∨ True))) ∨ p4)) → p2)))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_60010261591308177096828526038 : (((p1 ∨ True) → ((((p1 ∨ (p5 → ((p1 → False) ∧ (p2 ∨ p3)))) ∨ p4) ∨ True) ∧ (p1 ∨ ((p2 → ((p3 ∨ p5) ∧ p4)) ∨ True)))) ∨ False) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
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
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h4 =>
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- One of the premise coincides with the conclusion.
    exact h4
  case inr h5 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_184592320611920620764759143574 : (((False → ((((p3 → p2) → p3) ∧ p1) → False)) → (p1 ∨ p2)) ∨ (((True ∧ (p4 ∨ p3)) ∨ True) → (p4 → (True ∨ (p1 ∨ (True → p5)))))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
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
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- True on the right can always be proven directly.
      apply True.intro
    case inr h7 =>
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- True on the right can always be proven directly.
      apply True.intro
  case inr h8 =>
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- True on the right can always be proven directly.
    apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_200119315729615583317799742393 : (((p1 ∨ (p4 ∨ False)) ∧ (p2 ∧ (p5 ∨ p3))) → ((((p4 ∨ p2) → ((p3 → p4) → (((p2 ∧ (p3 → True)) ∧ p1) ∧ False))) ∧ p4) ∨ True)) := by
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
    -- Disjunctions on the left can always be decomposed.
    cases h9
    case inl h10 =>
      -- Conjunctions on the left can always be decomposed.
      let h11 := h3.left
      let h12 := h3.right
      -- Disjunctions on the left can always be decomposed.
      cases h12
      case inl h13 =>
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
      -- False on the left can always be used.
      apply False.elim h15



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_755863856823287433853531540123 : (((p1 ∧ ((((p2 → (p4 ∧ ((p1 ∧ p4) → (((p4 → p3) ∨ p3) → p4)))) → (((p2 → (False → p1)) → p3) ∨ p4)) ∨ True) → False)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_871697420861506756066007650388 : ((((p3 ∨ ((p5 → (((p5 ∧ (p4 → p2)) ∧ p3) → p5)) → ((p2 ∨ (p4 ∨ (True ∨ (p3 → p3)))) ∨ ((p3 → p2) ∨ p5)))) → False) → p2) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h1
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h2 : (p3 ∨ ((p5 → (((p5 ∧ (p4 → p2)) ∧ p3) → p5)) → ((p2 ∨ (p4 ∨ (True ∨ (p3 → p3)))) ∨ ((p3 → p2) ∨ p5)))) := by
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h3
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
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h4 := h1 h2
  -- False on the left can always be used.
  apply False.elim h4
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_157746356288768732204576597294 : (((((True ∨ p3) → ((False → p3) ∨ ((p5 ∧ p5) ∨ True))) → False) ∧ (((p2 ∧ True) ∨ p3) ∧ p3)) ∨ (p5 ∨ ((True → (False ∧ p4)) → False))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
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
  -- We need to get the left conjuct of h3 based on <expert-advice>.
  let h4 := h3.left
  -- False on the left can always be used.
  apply False.elim h4



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_338736741005190814385865686837 : (p1 → ((p3 → p1) ∧ ((p4 ∨ (((p5 ∨ (((False → p1) → (p4 → False)) ∨ p4)) ∨ p3) ∨ (p5 → (((p5 ∧ True) → p1) → p1)))) ∧ True))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h2
  -- One of the premise coincides with the conclusion.
  exact h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h3
  -- Implications on the right can always be decomposed.
  intro h4
  -- One of the premise coincides with the conclusion.
  exact h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_302602454237481201669550089740 : (False ∨ (p1 ∨ (p2 ∨ ((p5 ∧ (p5 ∨ (p1 ∧ (True ∧ ((True ∧ (p3 ∨ p5)) → (p1 ∨ (p4 ∨ (p4 ∨ (p3 → p3))))))))) ∨ (True ∨ p5))))) := by
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
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_654297962919120544107213225865 : ((((((p4 → (((p1 → p4) → p5) → (p4 ∨ (p5 → ((((False ∨ p3) ∨ False) ∨ p4) ∨ p5))))) → (False ∧ p3)) ∨ p3) ∨ (p2 ∨ True)) ∨ p4) ∧ True) := by
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
theorem thm_5_vars_760365905399588841885840915376 : (((p2 ∧ ((p3 ∨ p4) → ((((p4 ∧ p5) → (p3 → (p3 ∨ p1))) ∧ ((False ∨ p3) ∨ ((p2 → False) → p2))) ∧ (False ∨ (p1 ∧ p3))))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_260305933452286198456066149219 : ((p2 → p4) → ((True ∧ (((p1 → (False ∧ p5)) ∨ (p2 → False)) → p2)) ∨ ((p1 → (p3 ∧ ((p3 ∨ p3) → (p3 → p4)))) → (p2 → p2)))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h2
  -- Implications on the right can always be decomposed.
  intro h3
  -- One of the premise coincides with the conclusion.
  exact h3



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_263084413118276295175136615360 : (True ∧ (((p2 ∧ (((p2 → ((p4 ∨ ((((p5 ∨ True) ∨ p3) ∨ p1) → True)) → ((p5 ∧ p3) → p4))) ∨ False) ∧ False)) ∨ p1) ∨ (p1 → True))) := by
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
theorem thm_5_vars_111350286825151076317836366883 : (((p4 ∧ ((((((p1 ∧ p2) → ((p2 ∧ p5) ∨ p5)) ∧ (p4 → p2)) → (p3 → p5)) ∧ False) ∨ ((p1 → p1) → p5))) ∧ p4) ∨ (False → p2)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_134727956003329118633360352279 : ((((p5 ∧ (p1 ∨ p1)) → ((p1 ∧ (p1 → (p1 → p3))) ∨ ((p1 ∨ p4) ∨ (p2 → (p5 ∧ (p2 ∧ p5)))))) → p5) ∨ ((p4 → p3) → True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_709160730921375657514288719720 : (((((p4 → (p1 → True)) → ((False ∨ p3) ∧ p1)) → (((((p3 ∧ p3) ∨ (True ∧ p1)) → (p2 ∨ (p2 ∨ p2))) → p2) ∧ (p4 ∨ p1))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_215997003083681026619140633392 : ((p4 ∨ (p4 ∨ (p3 ∨ False))) ∨ (p4 ∨ (((p4 → (((p3 ∧ (False ∨ (False ∨ (p3 ∧ True)))) ∨ False) ∧ p1)) ∨ True) ∨ (p5 ∧ (p4 ∨ p4))))) := by
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



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_135542107661204811362605746579 : (((((p2 ∧ ((p3 ∨ p5) → p2)) ∧ p1) ∨ (p3 ∨ ((False ∨ (True → p1)) → p4))) ∧ (p2 → ((p1 ∨ p5) ∨ p5))) ∨ (False → (p2 → p5))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_311022387214129885046014293206 : (p2 ∨ ((False ∧ p2) ∨ (p3 ∨ ((True ∨ ((True ∧ ((p1 ∧ (True ∨ (True → False))) → (p4 ∨ True))) ∧ (p4 ∨ p3))) ∧ (p4 ∨ (p1 → True)))))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_784720058412296488542215665601 : (((p3 ∨ (p5 ∨ (((p3 ∨ p5) ∨ ((p1 → (((p3 ∧ True) ∧ (p3 → p2)) ∧ False)) → (True ∨ (p3 ∨ (p1 ∨ (True → True)))))) ∧ p4))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_51266047374929554358024829198 : ((((False ∨ p5) → ((((p1 ∨ ((p1 ∨ p1) ∨ p2)) ∧ p5) ∨ ((p1 ∨ p5) ∨ p3)) ∧ p1)) ∨ (p5 → (((False → p4) → p4) ∨ p3))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



