variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_261377366180025309046818179740 : ((p5 → p1) → (((False ∧ p2) ∨ ((p2 ∧ False) ∨ ((p2 ∨ (((p3 ∨ p5) ∧ True) → ((p4 ∨ (p2 ∧ (p5 ∧ p4))) → p1))) ∨ p1))) ∨ True)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_264170793803956842844675518505 : (True ∧ (((False → p1) → ((p3 → (True → p5)) ∨ p1)) ∨ (p5 → (p3 ∨ (True ∧ ((p4 ∨ (p2 → p3)) → ((p5 ∨ (True → p1)) ∨ p4))))))) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- Implications on the right can always be decomposed.
  intro h2
  -- Disjunctions on the left can always be decomposed.
  cases h2
  case inl h3 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h3
  case inr h4 =>
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- One of the premise coincides with the conclusion.
    exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_734343655760520834365862653492 : ((((False ∨ p3) ∧ ((p4 ∧ ((p4 ∧ ((p3 ∨ p1) → ((((p3 ∨ p3) ∧ p2) → p4) → p1))) → p3)) → (((p4 ∨ p1) ∨ p5) → p1))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_306385382613973754724420516102 : (p1 ∨ ((p5 → True) ∧ (((p3 ∧ (p1 ∨ (p1 ∨ ((p3 ∨ True) → p4)))) ∧ p5) ∨ ((p4 → (((p3 ∨ p2) ∧ p5) ∨ p1)) ∨ (p2 → p2))))) := by
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
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h2
  -- One of the premise coincides with the conclusion.
  exact h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_57994275387609381142513840201 : (((p5 → (p1 ∨ p4)) → ((True ∧ (((((((p1 → ((p3 ∨ p4) ∨ p2)) ∧ p1) → p5) → p1) → True) ∨ p5) → (True ∧ p1))) ∧ p3)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_319675046237442607592223136551 : (p4 ∨ (((p3 ∨ (False → p5)) ∨ (False ∧ (False ∧ p5))) → (p5 → (((p3 ∧ (p4 → p1)) → True) ∧ (((p3 → (p4 ∧ p3)) ∨ p5) ∨ p1))))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h3
  -- True on the right can always be proven directly.
  apply True.intro
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h4 =>
    -- Disjunctions on the left can always be decomposed.
    cases h4
    case inl h5 =>
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- One of the premise coincides with the conclusion.
      exact h2
    case inr h6 =>
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- One of the premise coincides with the conclusion.
      exact h2
  case inr h7 =>
    -- Conjunctions on the left can always be decomposed.
    let h8 := h7.left
    let h9 := h7.right
    -- False on the left can always be used.
    apply False.elim h8



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_691129491957710082760553432908 : ((((((p4 ∧ p4) ∨ ((p2 ∧ (p2 ∨ p3)) ∧ False)) ∨ (p5 → (p3 ∧ (p1 ∧ p3)))) → ((p5 ∨ p5) ∨ (p4 ∨ (True ∨ (p1 → p1))))) ∨ p5) ∧ True) := by
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
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- One of the premise coincides with the conclusion.
      exact h5
    case inr h6 =>
      -- Conjunctions on the left can always be decomposed.
      let h7 := h6.left
      let h8 := h6.right
      -- Conjunctions on the left can always be decomposed.
      let h9 := h7.left
      let h10 := h7.right
      -- Disjunctions on the left can always be decomposed.
      cases h10
      case inl h11 =>
        -- False on the left can always be used.
        apply False.elim h8
      case inr h12 =>
        -- False on the left can always be used.
        apply False.elim h8
  case inr h13 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- True on the right can always be proven directly.
    apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_119097742906695322885584264184 : ((p1 → ((False ∧ ((p2 ∨ p4) ∧ (p3 ∧ p3))) ∨ ((p2 ∧ (p3 → p4)) ∨ ((False → ((p1 ∨ p4) ∨ p1)) ∨ (p1 ∧ p2))))) ∨ (p4 ∧ p3)) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
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
  -- False on the left can always be used.
  apply False.elim h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_168158245112398967613200003182 : ((((p4 ∨ p1) ∨ p4) ∧ (((False ∨ p4) ∨ True) ∧ (True ∨ ((p1 ∧ p3) → (True ∨ p1))))) → (p2 → (((False ∨ (p1 → p3)) ∧ False) ∨ p2))) := by
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
    -- Disjunctions on the left can always be decomposed.
    cases h5
    case inl h6 =>
      -- Conjunctions on the left can always be decomposed.
      let h7 := h4.left
      let h8 := h4.right
      -- Disjunctions on the left can always be decomposed.
      cases h7
      case inl h9 =>
        -- Disjunctions on the left can always be decomposed.
        cases h9
        case inl h10 =>
          -- False on the left can always be used.
          apply False.elim h10
        case inr h11 =>
          -- Disjunctions on the left can always be decomposed.
          cases h8
          case inl h12 =>
            -- Show the right disjunct based on <expert-advice>.
            apply Or.inr
            -- One of the premise coincides with the conclusion.
            exact h2
          case inr h13 =>
            -- Show the right disjunct based on <expert-advice>.
            apply Or.inr
            -- One of the premise coincides with the conclusion.
            exact h2
      case inr h14 =>
        -- Disjunctions on the left can always be decomposed.
        cases h8
        case inl h15 =>
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- One of the premise coincides with the conclusion.
          exact h2
        case inr h16 =>
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- One of the premise coincides with the conclusion.
          exact h2
    case inr h17 =>
      -- Conjunctions on the left can always be decomposed.
      let h18 := h4.left
      let h19 := h4.right
      -- Disjunctions on the left can always be decomposed.
      cases h18
      case inl h20 =>
        -- Disjunctions on the left can always be decomposed.
        cases h20
        case inl h21 =>
          -- False on the left can always be used.
          apply False.elim h21
        case inr h22 =>
          -- Disjunctions on the left can always be decomposed.
          cases h19
          case inl h23 =>
            -- Show the right disjunct based on <expert-advice>.
            apply Or.inr
            -- One of the premise coincides with the conclusion.
            exact h2
          case inr h24 =>
            -- Show the right disjunct based on <expert-advice>.
            apply Or.inr
            -- One of the premise coincides with the conclusion.
            exact h2
      case inr h25 =>
        -- Disjunctions on the left can always be decomposed.
        cases h19
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
  case inr h28 =>
    -- Conjunctions on the left can always be decomposed.
    let h29 := h4.left
    let h30 := h4.right
    -- Disjunctions on the left can always be decomposed.
    cases h29
    case inl h31 =>
      -- Disjunctions on the left can always be decomposed.
      cases h31
      case inl h32 =>
        -- False on the left can always be used.
        apply False.elim h32
      case inr h33 =>
        -- Disjunctions on the left can always be decomposed.
        cases h30
        case inl h34 =>
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- One of the premise coincides with the conclusion.
          exact h2
        case inr h35 =>
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- One of the premise coincides with the conclusion.
          exact h2
    case inr h36 =>
      -- Disjunctions on the left can always be decomposed.
      cases h30
      case inl h37 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- One of the premise coincides with the conclusion.
        exact h2
      case inr h38 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- One of the premise coincides with the conclusion.
        exact h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_45430792665762370658469812211 : (((True ∨ (((True → (((True → ((p2 ∨ (p2 → p1)) ∧ False)) ∧ (((p1 → p2) ∧ False) ∧ p4)) ∧ p4)) → (False ∧ False)) → p5)) → p5) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_134343910016133562581516316745 : (((p5 ∧ (((p5 ∧ p1) → (p2 ∨ (p4 ∨ ((p4 → p3) ∨ (p4 ∧ ((p1 ∧ True) → (p5 → p5))))))) → p4)) ∨ True) ∨ ((p4 → p2) → p2)) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_93719346060177450159848767632 : ((p1 ∧ (((p2 ∨ p1) → (((((p3 → p1) ∨ p3) ∧ ((False → ((p4 → p3) ∨ (p4 ∨ p3))) ∨ p1)) ∨ (True ∨ True)) ∧ p4)) ∧ True)) → p4) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- Conjunctions on the left can always be decomposed.
  let h4 := h3.left
  let h5 := h3.right
  -- We want to use the implication h4 based on <expert-advice>. So we show its premise.
  have h6 : (p2 ∨ p1) := by
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h2
  -- We have shown the premise of h4, we can now drive its conclusion.
  let h7 := h4 h6
  -- We need to get the right conjuct of h7 based on <expert-advice>.
  let h8 := h7.right
  -- One of the premise coincides with the conclusion.
  exact h8



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_57684734266624003096376266609 : ((((p4 → True) ∨ p5) → ((p4 ∨ ((p3 ∧ (p5 ∨ (p3 ∧ p5))) ∨ (p3 → (p3 → p3)))) → ((p5 ∨ ((p1 → p5) → p1)) ∨ True))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_56173042217956571848857344356 : (((p2 ∧ ((True → p1) ∧ p2)) ∨ ((p2 ∧ ((((p2 → (True → False)) ∧ p4) ∨ False) ∨ (False ∧ (p2 ∨ p3)))) ∨ ((False ∨ p1) → True))) ∨ p4) := by
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
theorem thm_5_vars_114274995421959007806149713939 : ((((((p2 ∧ (p4 ∨ p1)) → (((p1 ∧ p4) ∧ False) ∧ p2)) ∧ ((True ∧ False) ∨ p1)) ∨ p2) ∧ (p2 ∨ (p3 ∧ (True → True)))) ∨ (True ∨ p1)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_710736920450659452115282785156 : ((((((p2 → p2) ∨ p5) → (p3 ∧ p1)) ∧ ((p3 → (((p4 ∨ (p1 ∧ p4)) → (False → ((p4 ∧ p1) → p3))) → p1)) ∧ (False ∧ False))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_357532173343237996485351597922 : (p5 → (True ∧ (p1 ∨ (p4 → (((False ∧ ((False → ((p3 ∨ True) ∨ (p3 → (p2 → (p2 ∨ False))))) → p2)) ∧ True) ∨ ((p4 → p1) → True)))))) := by
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
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h3
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_265618225466571435116045001658 : (True ∧ (p1 ∨ (p2 ∨ (((p1 ∨ (((p1 ∧ p1) ∨ True) ∨ p2)) ∨ p1) ∧ ((p4 ∨ ((p4 ∧ ((p4 → p2) ∧ (True ∨ False))) → True)) ∨ False))))) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- True on the right can always be proven directly.
  apply True.intro
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
  -- True on the right can always be proven directly.
  apply True.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_778459736500597932867481203354 : (((p1 ∨ (p4 ∧ (((False → ((((False ∨ (((p1 ∨ True) → p5) → p1)) ∨ (p5 ∧ p4)) → p4) ∧ (p1 ∨ p1))) ∨ (p2 ∧ p4)) → p5))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_161210324604924948535679740851 : (((p1 → p5) ∨ (((True ∨ (p4 ∧ (p1 ∧ p2))) → (p3 → (True ∧ (p3 → (False ∧ p3))))) ∨ p3)) → (p2 ∨ (p2 ∨ (False ∨ (p5 → p5))))) := by
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
    -- Implications on the right can always be decomposed.
    intro h3
    -- One of the premise coincides with the conclusion.
    exact h3
  case inr h4 =>
    -- Disjunctions on the left can always be decomposed.
    cases h4
    case inl h5 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Implications on the right can always be decomposed.
      intro h6
      -- One of the premise coincides with the conclusion.
      exact h6
    case inr h7 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Implications on the right can always be decomposed.
      intro h8
      -- One of the premise coincides with the conclusion.
      exact h8



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_313235449998783181364848199595 : (p3 ∨ (((True ∧ p1) ∨ (p2 ∨ (((p5 → ((p5 ∧ (True → (((True ∧ p2) → p4) ∧ p4))) → p4)) → False) ∧ (p5 → (False ∨ p2))))) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_350926870571852054800848298381 : (p4 → ((((True ∨ (p5 → (p1 → (((p3 → p1) ∨ (p3 ∨ ((p3 ∧ (p2 ∧ p4)) → p4))) ∧ (False ∨ p1))))) ∨ True) → p2) ∨ (p1 → p1))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h2
  -- One of the premise coincides with the conclusion.
  exact h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_65110833499815441722394182166 : ((p2 ∨ (p4 ∨ (p1 → (((p4 ∧ p3) ∨ ((((True ∧ (((p2 → p3) ∨ p5) ∨ p4)) ∨ p2) ∧ (True → (p4 ∧ p4))) ∨ False)) → p4)))) ∨ False) := by
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
  cases h2
  case inl h3 =>
    -- Conjunctions on the left can always be decomposed.
    let h4 := h3.left
    let h5 := h3.right
    -- One of the premise coincides with the conclusion.
    exact h4
  case inr h6 =>
    -- Disjunctions on the left can always be decomposed.
    cases h6
    case inl h7 =>
      -- Conjunctions on the left can always be decomposed.
      let h8 := h7.left
      let h9 := h7.right
      -- Disjunctions on the left can always be decomposed.
      cases h8
      case inl h10 =>
        -- Conjunctions on the left can always be decomposed.
        let h11 := h10.left
        let h12 := h10.right
        -- Disjunctions on the left can always be decomposed.
        cases h12
        case inl h13 =>
          -- Disjunctions on the left can always be decomposed.
          cases h13
          case inl h14 =>
            -- We want to use the implication h9 based on <expert-advice>. So we show its premise.
            have h15 : True := by
              -- True on the right can always be proven directly.
              apply True.intro
            -- We have shown the premise of h9, we can now drive its conclusion.
            let h16 := h9 h15
            -- We need to get the left conjuct of h16 based on <expert-advice>.
            let h17 := h16.left
            -- One of the premise coincides with the conclusion.
            exact h17
          case inr h18 =>
            -- We want to use the implication h9 based on <expert-advice>. So we show its premise.
            have h19 : True := by
              -- True on the right can always be proven directly.
              apply True.intro
            -- We have shown the premise of h9, we can now drive its conclusion.
            let h20 := h9 h19
            -- We need to get the left conjuct of h20 based on <expert-advice>.
            let h21 := h20.left
            -- One of the premise coincides with the conclusion.
            exact h21
        case inr h22 =>
          -- One of the premise coincides with the conclusion.
          exact h22
      case inr h23 =>
        -- We want to use the implication h9 based on <expert-advice>. So we show its premise.
        have h24 : True := by
          -- True on the right can always be proven directly.
          apply True.intro
        -- We have shown the premise of h9, we can now drive its conclusion.
        let h25 := h9 h24
        -- We need to get the left conjuct of h25 based on <expert-advice>.
        let h26 := h25.left
        -- One of the premise coincides with the conclusion.
        exact h26
    case inr h27 =>
      -- False on the left can always be used.
      apply False.elim h27



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_699835675727300114278753883770 : (((((p3 ∧ (p1 ∨ ((p4 → p3) → (p5 ∧ p4)))) → (True → p5)) → (((p5 ∧ p4) ∨ p1) → (p4 ∧ (p2 → ((p3 → p5) ∨ p2))))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_906687282560969919731984512 : ((p5 → (((((True ∨ ((p3 → p3) → p1)) → False) ∨ (((p1 → (p2 → p1)) ∧ p1) → (p4 ∨ (p5 ∧ True)))) ∧ False) ∨ True)) ∨ p4) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_114763755431524710026265692292 : (((False → (((p4 ∨ ((False ∧ (p5 → (p5 ∨ True))) ∧ False)) ∨ (p2 ∧ p5)) ∨ p3)) → ((p4 ∨ p2) ∧ ((p1 → p5) ∨ p1))) ∨ (True → True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_225490494038092281446077755665 : (((p5 ∨ False) ∧ p2) ∨ (((((p3 → p2) → ((p2 → (False → True)) ∨ p2)) ∨ (p5 → (True ∧ ((p1 ∧ True) ∧ p2)))) → (p1 ∨ True)) ∨ False)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
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
theorem thm_5_vars_49958764486200653881568820609 : (((((p3 ∧ p1) ∧ (((p3 ∨ p5) ∨ p5) → (((p5 ∨ p3) ∨ p5) ∨ (True ∧ p1)))) → (p1 → p5)) ∧ ((p2 ∨ p4) ∧ (p5 → p2))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_658170268282604434193117634633 : ((((p4 ∧ (False ∧ (((((p4 → ((False ∧ False) ∧ False)) → ((True ∧ (p5 → p5)) → p4)) ∧ (p1 ∧ p5)) ∨ p5) ∨ p5))) ∨ (p3 ∧ False)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_38866240714202852955299424185 : ((((p3 ∨ (p3 ∧ False)) ∧ (((p3 ∨ (p1 → (((p4 → True) ∨ (p3 → True)) → (p5 ∨ (p2 ∧ (p4 → p2)))))) → p3) ∧ p1)) ∧ p2) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_356145657771965372330600798275 : (p5 → (((((((p3 → ((p1 ∨ p2) ∧ p1)) ∧ p5) ∨ ((p5 ∨ False) → True)) ∧ True) ∨ True) → p2) ∨ ((False → p5) ∨ ((p2 ∧ False) ∧ p1)))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h2
  -- False on the left can always be used.
  apply False.elim h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_658448250113979809228149807297 : ((((p1 ∨ ((p3 → ((p1 ∧ ((p3 ∧ (p5 ∨ p4)) → ((False ∨ False) → (p1 → p1)))) → (p3 ∧ p5))) ∨ (p5 ∨ p2))) ∨ (p2 ∨ p1)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_25410947890170046219552444523 : (((True ∧ (p5 ∧ p4)) → (((p2 ∨ ((p2 ∧ (True ∧ ((((False ∨ True) → (p5 ∧ p4)) ∨ p4) → p1))) → (p4 ∨ p3))) → p3) ∨ p4)) ∧ True) := by
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
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h5
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_675003045157473386036098393880 : ((((((p3 → False) ∨ (((p5 ∧ False) → (False → (((p2 → (p5 ∨ False)) → p1) ∨ p2))) → p4)) ∧ p5) ∧ (((p5 → p1) ∧ True) ∨ True)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_200200451223776747671935936540 : (((p5 ∨ (p2 ∧ p2)) ∨ (False ∨ (True → p3))) → (((((p1 → (p3 ∨ False)) → ((p2 ∧ p3) ∨ False)) ∧ (True ∨ p1)) ∨ (p3 ∨ p5)) ∨ p2)) := by
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
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- One of the premise coincides with the conclusion.
      exact h3
    case inr h4 =>
      -- Conjunctions on the left can always be decomposed.
      let h5 := h4.left
      let h6 := h4.right
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- One of the premise coincides with the conclusion.
      exact h6
  case inr h7 =>
    -- Disjunctions on the left can always be decomposed.
    cases h7
    case inl h8 =>
      -- False on the left can always be used.
      apply False.elim h8
    case inr h9 =>
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- We want to use the implication h9 based on <expert-advice>. So we show its premise.
      have h10 : True := by
        -- True on the right can always be proven directly.
        apply True.intro
      -- We have shown the premise of h9, we can now drive its conclusion.
      let h11 := h9 h10
      -- One of the premise coincides with the conclusion.
      exact h11



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_173887004696698813662616760433 : (((((p3 ∧ (p2 ∨ p2)) ∧ (False ∨ (((p2 ∧ p2) ∨ True) ∧ False))) ∨ p3) → p4) → (p3 ∨ ((((p3 → (p2 ∨ True)) ∨ True) → p3) ∨ True))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_71593161538274391697061449563 : (((True ∧ (p1 → (((True → ((((((False ∧ True) → (True ∧ (p2 → p2))) → False) ∧ p2) → True) ∧ p3)) ∧ (p1 → p3)) ∧ p5))) ∧ p1) → p3) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- Conjunctions on the left can always be decomposed.
  let h4 := h2.left
  let h5 := h2.right
  -- We want to use the implication h5 based on <expert-advice>. So we show its premise.
  have h6 : p1 := by
    -- One of the premise coincides with the conclusion.
    exact h3
  -- We have shown the premise of h5, we can now drive its conclusion.
  let h7 := h5 h6
  -- We need to get the left conjuct of h7 based on <expert-advice>.
  let h8 := h7.left
  -- We need to get the right conjuct of h8 based on <expert-advice>.
  let h9 := h8.right
  -- We want to use the implication h9 based on <expert-advice>. So we show its premise.
  have h10 : p1 := by
    -- One of the premise coincides with the conclusion.
    exact h3
  -- We have shown the premise of h9, we can now drive its conclusion.
  let h11 := h9 h10
  -- One of the premise coincides with the conclusion.
  exact h11



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_44632364395495109721225799244 : ((((p1 ∧ (((True ∧ False) → p2) → False)) ∧ ((((p3 ∨ (p4 ∨ (False ∨ p3))) → False) → True) ∨ ((p5 → (p3 ∨ p3)) ∧ p3))) → p4) ∨ False) := by
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
  -- Disjunctions on the left can always be decomposed.
  cases h3
  case inl h6 =>
    -- We want to use the implication h5 based on <expert-advice>. So we show its premise.
    have h7 : ((True ∧ False) → p2) := by
      -- Implications on the right can always be decomposed.
      intro h8
      -- Conjunctions on the left can always be decomposed.
      let h9 := h8.left
      let h10 := h8.right
      -- False on the left can always be used.
      apply False.elim h10
    -- We have shown the premise of h5, we can now drive its conclusion.
    let h11 := h5 h7
    -- False on the left can always be used.
    apply False.elim h11
  case inr h12 =>
    -- Conjunctions on the left can always be decomposed.
    let h13 := h12.left
    let h14 := h12.right
    -- We want to use the implication h5 based on <expert-advice>. So we show its premise.
    have h15 : ((True ∧ False) → p2) := by
      -- Implications on the right can always be decomposed.
      intro h16
      -- Conjunctions on the left can always be decomposed.
      let h17 := h16.left
      let h18 := h16.right
      -- False on the left can always be used.
      apply False.elim h18
    -- We have shown the premise of h5, we can now drive its conclusion.
    let h19 := h5 h15
    -- False on the left can always be used.
    apply False.elim h19



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_621150900686481247047809106032 : (((((p5 → p3) → ((p1 → True) → (((p4 ∧ p2) → p2) → (p4 ∨ (p1 ∨ (p3 ∧ (p1 ∨ (((p1 ∨ True) → p2) ∨ p3)))))))) ∨ True) ∨ p5) ∧ True) := by
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
theorem thm_5_vars_337459590570648188785888959871 : (p1 → ((p3 ∨ (((p5 ∨ p4) ∨ ((p5 → (False ∧ ((p1 ∨ p3) → (((p2 ∨ p1) → p2) ∨ False)))) ∧ p1)) ∨ True)) → (p4 ∨ (p4 ∨ True)))) := by
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
    -- True on the right can always be proven directly.
    apply True.intro
  case inr h4 =>
    -- Disjunctions on the left can always be decomposed.
    cases h4
    case inl h5 =>
      -- Disjunctions on the left can always be decomposed.
      cases h5
      case inl h6 =>
        -- Disjunctions on the left can always be decomposed.
        cases h6
        case inl h7 =>
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- True on the right can always be proven directly.
          apply True.intro
        case inr h8 =>
          -- Show the left disjunct based on <expert-advice>.
          apply Or.inl
          -- One of the premise coincides with the conclusion.
          exact h8
      case inr h9 =>
        -- Conjunctions on the left can always be decomposed.
        let h10 := h9.left
        let h11 := h9.right
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- True on the right can always be proven directly.
        apply True.intro
    case inr h12 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- True on the right can always be proven directly.
      apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_219876784519428078341292776195 : ((p3 → (p4 → (True → p5))) → (p2 → ((p3 ∧ (p1 → ((p1 ∧ p3) ∧ (p3 ∨ p5)))) ∨ ((True ∨ ((p2 → (False ∨ p2)) ∨ p4)) ∨ True)))) := by
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
theorem thm_5_vars_178991927672396297765751137435 : (((p4 → p5) ∨ (False ∨ (((p2 ∨ p5) → (p4 → (p1 ∨ False))) ∨ p1))) ∨ (False ∨ ((p3 ∨ (True → (p5 → p5))) ∨ (p5 → (p5 ∧ False))))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
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
  -- One of the premise coincides with the conclusion.
  exact h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_310507039916865769495463633495 : (p2 ∨ ((False ∧ (((p4 ∨ p1) ∨ p3) ∨ p1)) ∨ (((False ∧ (p5 → ((p2 → (True → p4)) ∨ False))) ∧ (False ∨ (p3 ∧ p4))) → (p2 ∨ p2)))) := by
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
theorem thm_5_vars_345567640413729304494995344084 : (p3 → ((((False → p4) ∧ p5) ∧ (((True ∨ p1) → p1) ∨ ((p4 → (True ∨ True)) ∧ (False ∨ ((p4 → ((False ∧ p1) → True)) → p2))))) ∨ True)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_113784577075765382141629870426 : ((((p4 ∧ (False → p2)) → (True ∧ (False → (((p4 ∧ False) ∨ (((True → p5) ∧ p3) ∨ (True → p2))) ∧ p3)))) → (p5 ∨ False)) ∨ (p4 → p4)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_116909822239872460560037154335 : (((p5 → p4) ∨ ((False ∨ p1) → ((((False → p4) → p2) → (((False ∧ True) → ((True ∨ True) ∧ (True ∧ p2))) → p5)) ∧ p1))) ∨ (p1 → p1)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_219648560089865529213703790153 : ((False → (True ∧ (False → p5))) → (p4 ∨ (((p4 → ((p1 ∧ (False ∧ ((p5 ∧ False) → p4))) → ((p3 → p5) → (False → False)))) → p5) ∨ True))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_684645218500950445321997769271 : ((((((p1 ∨ p5) ∨ p4) ∨ ((p1 ∨ (p3 ∨ ((p4 → p3) ∨ p1))) → ((p5 ∨ True) ∧ True))) ∨ ((p3 → p5) ∨ (p1 ∧ (p2 ∧ p5)))) ∨ p5) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
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
    -- Disjunctions on the left can always be decomposed.
    cases h3
    case inl h4 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- True on the right can always be proven directly.
      apply True.intro
    case inr h5 =>
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
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_199865921008243351559062955128 : (((True → ((p4 ∧ p4) ∨ p3)) ∧ (p1 → p1)) → ((p3 → (((False ∧ (p4 ∧ p1)) → ((p3 ∨ p2) ∨ p1)) → (p2 → False))) ∨ (False → True))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h4
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_166551180162020730988262759098 : ((p5 ∨ ((p4 → (((p1 → (p5 ∨ True)) ∨ False) ∧ True)) → ((p3 ∨ p4) → (p4 ∨ p4)))) ∨ (((True ∨ p2) ∧ True) → ((False ∧ p2) → p4))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Conjunctions on the left can always be decomposed.
  let h3 := h2.left
  let h4 := h2.right
  -- False on the left can always be used.
  apply False.elim h3



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_606369126982082924061743092539 : ((((((((((p2 ∧ (((p1 → p1) → p3) → p1)) ∧ p2) ∨ (True ∧ p4)) ∧ p5) ∧ (p3 → (p5 → (p3 ∧ p2)))) ∨ p4) ∧ False) ∨ True) ∨ p3) ∧ True) := by
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
theorem thm_5_vars_66713950763867976827947579408 : ((True → ((p1 → False) ∧ (((p3 ∨ (False → True)) ∧ (((p1 ∧ (p2 ∧ (((p1 ∨ p1) ∨ True) ∨ p2))) ∧ True) ∨ p1)) ∧ (p2 ∧ p5)))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_115387033251100642556880783116 : ((((False → p1) ∧ (((p3 ∨ p1) ∧ p3) → p1)) ∧ (p4 ∧ ((True ∨ (((((p4 ∨ p3) ∧ p2) ∨ p1) → p4) → p3)) → p3))) ∨ (True ∨ p2)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_57363479811228022451314504195 : (((p4 ∧ (p3 ∧ p4)) ∨ ((True ∨ p3) ∧ (True → ((p3 ∧ (((p4 ∨ (p5 → p2)) → ((True ∨ p4) → (False → True))) → p5)) ∧ True)))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_57663394952259934945155581442 : ((((p5 ∨ p1) ∨ False) → (p2 ∨ (((p1 ∧ p4) ∧ (((p2 ∨ p3) ∨ ((p1 → (p4 ∨ (True → p1))) ∨ p4)) ∧ (p3 ∨ p1))) ∧ False))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_808698673805959858244691620490 : (((p4 → (p2 → (((p1 → (((False ∧ p2) ∧ ((False ∨ (p5 ∧ p4)) ∨ False)) ∧ False)) ∨ p4) ∨ (((p3 ∧ (p4 ∧ p1)) ∧ p2) ∨ p3)))) ∨ p2) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_123415006603094246994907093819 : ((((((((False ∧ p5) → p1) → p1) ∧ ((p2 ∨ p1) ∧ p3)) ∨ p5) → ((True ∧ True) ∧ False)) → (p2 ∨ (p3 ∨ (p4 ∧ p2)))) → (p1 ∨ True)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_716433916480528145981660980534 : (((((p4 → p2) ∧ (p3 → p1)) ∧ ((((p3 ∧ p4) → (((True ∧ p5) ∨ True) → ((p1 ∧ p1) → ((True ∨ p1) ∨ p1)))) ∨ True) → False)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_52010919834127494822014121819 : (((p3 ∧ (True → (((((False ∨ p1) ∨ True) → p1) ∨ False) → (p4 ∨ (p2 → False))))) ∨ (((p4 → p4) ∨ False) ∨ (p1 ∧ (True ∧ False)))) ∨ p3) := by
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



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_305910829050497891727181467280 : (p1 ∨ ((((p5 → p1) → p5) ∧ (p4 ∧ p5)) → (((p3 ∨ p3) → p3) → ((True → ((((p3 ∨ (False ∧ p2)) → p4) ∧ p3) → p2)) ∨ p4)))) := by
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
  let h5 := h4.left
  let h6 := h4.right
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h5



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_258884442471284816220966376504 : ((True → p2) → (((((False ∧ p5) → (((p2 ∨ p4) → p4) ∧ (p1 ∨ (p1 → (p2 ∧ p2))))) → (((True ∨ False) ∧ p5) ∧ p4)) ∨ p4) ∨ p2)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h2 : True := by
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h3 := h1 h2
  -- One of the premise coincides with the conclusion.
  exact h3



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_234078117721041805950021718259 : ((True → (p1 ∧ p3)) → (((True → (p2 ∨ (p2 ∧ (False ∨ p1)))) ∨ p1) ∨ ((p3 ∧ ((p2 ∨ p3) ∧ (True → ((p5 ∧ p1) ∨ p1)))) ∨ p5))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h2 : True := by
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h3 := h1 h2
  -- We need to get the left conjuct of h3 based on <expert-advice>.
  let h4 := h3.left
  -- One of the premise coincides with the conclusion.
  exact h4



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_353491246506169867675093500959 : (p4 → (p2 ∨ ((((p1 → (False ∧ (True ∧ ((p1 → p4) → ((p4 ∨ p5) ∨ p4))))) → p5) ∧ p2) ∨ (((p5 ∨ False) ∨ (p1 → True)) → True)))) := by
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
theorem thm_5_vars_165688060727829593768301314057 : ((((p1 ∧ True) ∨ (p1 ∨ (p5 → p3))) → ((True → False) → ((p5 → (p3 ∧ False)) → p5))) ∨ (p1 → ((p5 → (p1 ∨ p1)) → (p2 ∨ p5)))) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
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
    -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
    have h7 : True := by
      -- True on the right can always be proven directly.
      apply True.intro
    -- We have shown the premise of h2, we can now drive its conclusion.
    let h8 := h2 h7
    -- False on the left can always be used.
    apply False.elim h8
  case inr h9 =>
    -- Disjunctions on the left can always be decomposed.
    cases h9
    case inl h10 =>
      -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
      have h11 : True := by
        -- True on the right can always be proven directly.
        apply True.intro
      -- We have shown the premise of h2, we can now drive its conclusion.
      let h12 := h2 h11
      -- False on the left can always be used.
      apply False.elim h12
    case inr h13 =>
      -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
      have h14 : True := by
        -- True on the right can always be proven directly.
        apply True.intro
      -- We have shown the premise of h2, we can now drive its conclusion.
      let h15 := h2 h14
      -- False on the left can always be used.
      apply False.elim h15



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_228203920426309388921166298691 : ((p5 ∧ (True ∨ p5)) ∨ (p3 → (((False ∨ ((((p4 ∧ (p4 ∧ p4)) → p3) ∧ p4) ∨ p2)) ∨ (p5 → (p2 ∨ (p4 → p3)))) ∧ (True ∨ p2)))) := by
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
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h3
  -- One of the premise coincides with the conclusion.
  exact h1
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_797855069705101953386530727556 : (((p1 → ((((p5 ∨ (((False → (p2 ∨ ((p3 → p5) ∧ p5))) ∧ (((p3 → p1) → p2) → p3)) ∨ p4)) ∨ p1) → p5) ∨ (p4 ∨ p4))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_60173457883234351069056422439 : (((p5 ∨ False) → ((p5 ∨ (((False ∧ False) → False) ∨ ((False ∧ p5) ∨ (p3 → False)))) → (p1 ∨ ((p4 ∨ ((True ∧ p4) → p4)) ∨ p1)))) ∨ p1) := by
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
    cases h1
    case inl h4 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Implications on the right can always be decomposed.
      intro h5
      -- Conjunctions on the left can always be decomposed.
      let h6 := h5.left
      let h7 := h5.right
      -- One of the premise coincides with the conclusion.
      exact h7
    case inr h8 =>
      -- False on the left can always be used.
      apply False.elim h8
  case inr h9 =>
    -- Disjunctions on the left can always be decomposed.
    cases h9
    case inl h10 =>
      -- Disjunctions on the left can always be decomposed.
      cases h1
      case inl h11 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- Implications on the right can always be decomposed.
        intro h12
        -- Conjunctions on the left can always be decomposed.
        let h13 := h12.left
        let h14 := h12.right
        -- One of the premise coincides with the conclusion.
        exact h14
      case inr h15 =>
        -- False on the left can always be used.
        apply False.elim h15
    case inr h16 =>
      -- Disjunctions on the left can always be decomposed.
      cases h16
      case inl h17 =>
        -- Conjunctions on the left can always be decomposed.
        let h18 := h17.left
        let h19 := h17.right
        -- False on the left can always be used.
        apply False.elim h18
      case inr h20 =>
        -- Disjunctions on the left can always be decomposed.
        cases h1
        case inl h21 =>
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- Show the left disjunct based on <expert-advice>.
          apply Or.inl
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- Implications on the right can always be decomposed.
          intro h22
          -- Conjunctions on the left can always be decomposed.
          let h23 := h22.left
          let h24 := h22.right
          -- One of the premise coincides with the conclusion.
          exact h24
        case inr h25 =>
          -- False on the left can always be used.
          apply False.elim h25



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_211534706152587508840241207736 : (((True ∨ p5) → (False ∨ True)) ∧ ((False ∧ ((True → True) ∨ ((p5 ∧ p3) ∨ p4))) ∨ (((((p1 → p1) → p5) ∨ p1) → (p5 ∨ p1)) ∨ p4))) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
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
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h4
  -- Disjunctions on the left can always be decomposed.
  cases h4
  case inl h5 =>
    -- We want to use the implication h5 based on <expert-advice>. So we show its premise.
    have h6 : (p1 → p1) := by
      -- Implications on the right can always be decomposed.
      intro h7
      -- One of the premise coincides with the conclusion.
      exact h7
    -- We have shown the premise of h5, we can now drive its conclusion.
    let h8 := h5 h6
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- One of the premise coincides with the conclusion.
    exact h8
  case inr h9 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h9



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_117091585937028163932962340526 : (((p1 → p1) → ((((True ∧ p4) ∨ ((False ∨ p5) ∨ True)) → (p1 ∨ (False ∨ ((p1 ∨ (True ∧ p1)) ∨ (True ∧ p4))))) ∨ True)) ∨ (p2 ∨ p4)) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_118685621887613817695922965695 : ((p5 ∨ (((p4 ∨ p3) ∧ ((p3 ∧ True) ∧ ((True ∨ (((((p2 ∨ p4) ∨ (p2 → False)) → p4) ∧ p5) ∧ True)) → p5))) ∧ p4)) ∨ (p4 ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_253621965331276622906349353832 : ((p1 ∧ True) → ((((p3 ∨ ((((p5 ∧ p5) ∧ (True → p5)) → p2) → p4)) ∨ p3) → (p5 ∧ p3)) → (p5 ∨ (((True ∧ p4) ∨ p3) ∨ p1)))) := by
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
  -- One of the premise coincides with the conclusion.
  exact h3



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_38430458813645026657043376995 : (((((p5 ∨ (p4 ∧ ((((p2 → True) → (p2 ∧ p2)) ∨ True) → p4))) ∨ p2) ∨ ((p1 → (True ∨ (p4 → p2))) → (p2 ∧ False))) ∧ p5) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_305693275996206538222645900282 : (p1 ∨ ((p3 → (((p2 → (p4 ∨ False)) ∨ p2) ∨ (p5 ∨ p4))) ∨ ((True → p1) ∨ (p3 → (p1 ∨ ((p5 → (True ∨ (p3 → True))) → True)))))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
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
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_952116113287475049889314238949 : (((((p2 ∧ p5) ∧ p5) ∨ (((p1 ∨ (True ∨ (((p5 ∧ (p3 → p2)) ∨ (p2 ∨ (p4 → True))) ∨ False))) → (p2 ∧ True)) ∧ (p1 → p5))) → p2) ∧ True) := by
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
    -- One of the premise coincides with the conclusion.
    exact h5
  case inr h7 =>
    -- Conjunctions on the left can always be decomposed.
    let h8 := h7.left
    let h9 := h7.right
    -- We want to use the implication h8 based on <expert-advice>. So we show its premise.
    have h10 : (p1 ∨ (True ∨ (((p5 ∧ (p3 → p2)) ∨ (p2 ∨ (p4 → True))) ∨ False))) := by
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- True on the right can always be proven directly.
      apply True.intro
    -- We have shown the premise of h8, we can now drive its conclusion.
    let h11 := h8 h10
    -- We need to get the left conjuct of h11 based on <expert-advice>.
    let h12 := h11.left
    -- One of the premise coincides with the conclusion.
    exact h12
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_245951350162467045490663119628 : ((p4 ∧ True) ∨ ((((p2 ∨ (p3 ∧ p5)) ∨ (p3 ∨ p1)) ∨ (((False ∧ p3) → (((p5 ∨ p3) → (True → p4)) → p1)) ∨ (p1 ∧ p5))) ∨ False)) := by
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
  -- Conjunctions on the left can always be decomposed.
  let h3 := h1.left
  let h4 := h1.right
  -- False on the left can always be used.
  apply False.elim h3



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_157870996583033582459635056136 : (((((True ∧ p1) ∧ ((p3 ∧ False) ∧ (p4 ∧ False))) ∨ p3) ∨ (False ∨ (((p5 ∨ False) ∧ False) → True))) ∨ (((p2 → (True → p1)) ∧ p4) ∨ p5)) := by
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
theorem thm_5_vars_181377385883522928476975202724 : ((p1 ∨ ((p5 ∧ (((((True → p5) ∧ False) ∨ False) ∧ p5) ∨ True)) → p4)) → ((p3 ∧ ((((p2 ∨ p4) ∨ p2) ∧ True) ∧ (True ∨ p4))) ∨ True)) := by
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
theorem thm_5_vars_258083419558927676384605703704 : ((p4 ∨ p2) → (True → (((p2 ∨ p3) ∨ (p2 ∧ p2)) ∨ (p3 ∨ (p5 ∨ ((p2 ∨ (True ∧ (p1 ∧ (((False ∨ p4) → p1) ∨ False)))) → p4)))))) := by
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
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h4
    -- Disjunctions on the left can always be decomposed.
    cases h4
    case inl h5 =>
      -- One of the premise coincides with the conclusion.
      exact h3
    case inr h6 =>
      -- Conjunctions on the left can always be decomposed.
      let h7 := h6.left
      let h8 := h6.right
      -- Conjunctions on the left can always be decomposed.
      let h9 := h8.left
      let h10 := h8.right
      -- Disjunctions on the left can always be decomposed.
      cases h10
      case inl h11 =>
        -- One of the premise coincides with the conclusion.
        exact h3
      case inr h12 =>
        -- False on the left can always be used.
        apply False.elim h12
  case inr h13 =>
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- One of the premise coincides with the conclusion.
    exact h13



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_247953330539611111605194218601 : ((p1 ∨ p4) ∨ (((p4 ∨ ((p4 → ((((False ∨ True) → (p2 ∨ False)) → p4) ∧ ((p4 → p4) ∧ (p3 ∨ (True → p5))))) ∨ p2)) ∨ True) ∨ p1)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_166553787476605495845719464486 : ((p5 ∨ ((True ∨ (p3 ∨ (False ∨ p3))) → (p5 → (((p1 ∧ p1) ∨ (p4 ∨ p5)) ∧ True)))) ∨ (p2 → (p4 → ((p3 ∧ (p4 ∨ False)) ∧ p1)))) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h3 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h2
  case inr h4 =>
    -- Disjunctions on the left can always be decomposed.
    cases h4
    case inl h5 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- One of the premise coincides with the conclusion.
      exact h2
    case inr h6 =>
      -- Disjunctions on the left can always be decomposed.
      cases h6
      case inl h7 =>
        -- False on the left can always be used.
        apply False.elim h7
      case inr h8 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- One of the premise coincides with the conclusion.
        exact h2
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_115660053647468355156929139941 : (((((p1 → p2) ∨ p1) → (p1 ∧ p3)) ∨ ((((True ∨ False) → True) ∨ ((p3 ∨ p2) ∧ p3)) ∧ (p1 → ((False → p2) ∨ False)))) ∨ (True ∧ p3)) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro
  -- Implications on the right can always be decomposed.
  intro h2
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h3
  -- False on the left can always be used.
  apply False.elim h3



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_161407303001380609875979922946 : ((p1 ∧ (p1 ∨ (p1 ∨ ((p5 → (p1 ∨ ((p1 ∨ p3) ∧ (p4 → (p1 ∨ True))))) ∧ (p1 ∨ p1))))) → (p2 ∨ (((p2 → p3) ∧ p1) ∨ True))) := by
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
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro
  case inr h5 =>
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
      -- Conjunctions on the left can always be decomposed.
      let h8 := h7.left
      let h9 := h7.right
      -- Disjunctions on the left can always be decomposed.
      cases h9
      case inl h10 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- True on the right can always be proven directly.
        apply True.intro
      case inr h11 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- True on the right can always be proven directly.
        apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_206054043489071042376039306666 : ((p2 ∧ (p5 → ((p5 → p5) → p3))) ∨ ((p3 ∨ True) → (((p3 ∨ ((False ∨ (p3 ∨ p5)) ∨ p2)) ∨ ((p2 ∨ (False → False)) ∧ True)) ∨ False))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h2 =>
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
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
    -- Conjunctions on the right can always be decomposed.
    apply And.intro
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h4
    -- False on the left can always be used.
    apply False.elim h4
    -- True on the right can always be proven directly.
    apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_616276296604256113872656100736 : (((((((p1 ∧ p4) → ((p2 ∨ ((True ∨ p2) → p1)) → p4)) → p5) ∨ (p2 → (False ∧ (((p3 ∨ p2) → (p1 → p4)) ∧ False)))) ∨ p1) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_191106617556886445945889774123 : (((p1 ∧ (p2 ∧ p1)) ∧ ((p1 ∨ (p5 ∧ p4)) ∨ p2)) ∨ ((True ∨ p1) ∨ ((p3 ∧ ((p5 ∧ False) → (((p4 ∨ p4) ∨ p1) ∧ p2))) ∨ False))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_48656776931893908642636124892 : (((((p1 → p5) ∧ (True ∧ ((False → ((True → p5) ∨ (p5 ∨ p1))) ∨ p1))) → ((p4 ∧ (p1 ∧ p5)) → p2)) ∧ (p1 ∧ (True → p4))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_117320623130978124701461322453 : ((False ∧ ((True ∧ (p4 ∨ (p1 ∧ (p1 ∧ (p3 ∧ (True → p4)))))) ∨ ((True → (p5 → (False ∧ ((p2 → p1) ∨ p2)))) ∧ p1))) ∨ (p2 ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_322396644393907805552659125619 : (p5 ∨ (((p4 → ((((((p4 ∧ p1) → p5) ∧ p1) ∨ p5) ∨ p4) ∧ (p5 → p2))) ∨ (True ∧ ((p2 ∨ False) ∨ (p3 ∨ (p5 → False))))) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_62283236592186663908550507091 : ((p3 ∧ ((((p3 ∨ p1) ∧ p5) ∨ ((((p2 → p2) ∧ (p4 ∨ (p3 ∨ ((p3 → ((p3 ∧ p2) ∨ p5)) ∧ True)))) → True) → p4)) → p2)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_802552477374145820176313422019 : (((p2 → (p4 ∨ ((p1 ∧ ((((p3 ∧ p3) ∨ p1) → (p4 ∧ p3)) → p1)) ∨ (True ∧ (((p1 ∨ (p1 → False)) ∧ (p4 → p5)) → p2))))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_344105469208406019118513971648 : (p2 → (False ∨ ((((p5 ∧ ((True ∧ p3) ∨ p4)) ∧ ((p4 ∧ p4) ∨ p3)) → (((((p2 ∨ False) → False) ∧ (True → True)) ∨ True) ∨ p4)) ∨ p3))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h2
  -- Conjunctions on the left can always be decomposed.
  let h3 := h2.left
  let h4 := h2.right
  -- Conjunctions on the left can always be decomposed.
  let h5 := h3.left
  let h6 := h3.right
  -- Disjunctions on the left can always be decomposed.
  cases h6
  case inl h7 =>
    -- Conjunctions on the left can always be decomposed.
    let h8 := h7.left
    let h9 := h7.right
    -- Disjunctions on the left can always be decomposed.
    cases h4
    case inl h10 =>
      -- Conjunctions on the left can always be decomposed.
      let h11 := h10.left
      let h12 := h10.right
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- One of the premise coincides with the conclusion.
      exact h12
    case inr h13 =>
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- True on the right can always be proven directly.
      apply True.intro
  case inr h14 =>
    -- Disjunctions on the left can always be decomposed.
    cases h4
    case inl h15 =>
      -- Conjunctions on the left can always be decomposed.
      let h16 := h15.left
      let h17 := h15.right
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- One of the premise coincides with the conclusion.
      exact h17
    case inr h18 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- One of the premise coincides with the conclusion.
      exact h14



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_317116620636824847854807816615 : (p3 ∨ (p5 → (((p1 ∧ (p5 ∧ ((p5 → True) → ((p4 → p2) → p4)))) ∨ True) ∧ ((p3 ∨ p5) ∨ (p1 → (p2 ∨ ((True → p4) ∨ p2))))))) := by
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
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_77515212820526127061913122540 : (((True ∧ ((p4 → (p1 → (p3 ∧ ((p1 ∨ p5) → ((p2 ∨ p2) ∨ ((p2 ∧ p2) ∧ (((p3 ∨ p5) ∧ True) ∧ p2))))))) ∨ True)) → False) → p5) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h2 : (True ∧ ((p4 → (p1 → (p3 ∧ ((p1 ∨ p5) → ((p2 ∨ p2) ∨ ((p2 ∧ p2) ∧ (((p3 ∨ p5) ∧ True) ∧ p2))))))) ∨ True)) := by
    -- Conjunctions on the right can always be decomposed.
    apply And.intro
    -- True on the right can always be proven directly.
    apply True.intro
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h3 := h1 h2
  -- False on the left can always be used.
  apply False.elim h3



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_174184570917441547050602008665 : (((True → (((p5 ∨ p5) → ((p3 → True) → p3)) → (p1 ∧ p5))) ∨ (p2 ∨ p3)) → ((p1 ∨ ((False ∧ ((True ∧ p1) ∨ p1)) → False)) ∨ p5)) := by
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
    -- Conjunctions on the left can always be decomposed.
    let h4 := h3.left
    let h5 := h3.right
    -- False on the left can always be used.
    apply False.elim h4
  case inr h6 =>
    -- Disjunctions on the left can always be decomposed.
    cases h6
    case inl h7 =>
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Implications on the right can always be decomposed.
      intro h8
      -- Conjunctions on the left can always be decomposed.
      let h9 := h8.left
      let h10 := h8.right
      -- False on the left can always be used.
      apply False.elim h9
    case inr h11 =>
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Implications on the right can always be decomposed.
      intro h12
      -- Conjunctions on the left can always be decomposed.
      let h13 := h12.left
      let h14 := h12.right
      -- False on the left can always be used.
      apply False.elim h13



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_36783588964867362104935480767 : ((p5 → ((p3 ∨ ((p1 ∧ (((False ∧ (p2 ∨ False)) ∧ False) ∨ ((p1 ∧ (p2 → (p4 → p2))) ∧ p4))) ∨ p1)) ∨ (p1 ∨ (p3 ∨ True)))) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
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
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_350907235980756887679825121458 : (p4 → ((((False ∧ ((p1 ∨ (p1 → ((((p4 → False) ∨ p1) ∨ p4) ∨ p2))) ∨ (p4 → p1))) ∨ ((p5 ∧ True) → p4)) ∧ p3) ∨ (p1 ∨ p4))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_234668317379567964510227346512 : ((p4 → (p1 ∧ p3)) → ((((True ∧ ((p4 ∨ True) → p2)) → p2) → (((False ∨ p1) ∨ (p1 ∨ (p2 ∧ ((p2 → p5) → p3)))) ∧ False)) → p5)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
  have h3 : ((True ∧ ((p4 ∨ True) → p2)) → p2) := by
    -- Implications on the right can always be decomposed.
    intro h4
    -- Conjunctions on the left can always be decomposed.
    let h5 := h4.left
    let h6 := h4.right
    -- We want to use the implication h6 based on <expert-advice>. So we show its premise.
    have h7 : (p4 ∨ True) := by
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- True on the right can always be proven directly.
      apply True.intro
    -- We have shown the premise of h6, we can now drive its conclusion.
    let h8 := h6 h7
    -- One of the premise coincides with the conclusion.
    exact h8
  -- We have shown the premise of h2, we can now drive its conclusion.
  let h9 := h2 h3
  -- We need to get the right conjuct of h9 based on <expert-advice>.
  let h10 := h9.right
  -- False on the left can always be used.
  apply False.elim h10



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_605767587479824167096345705310 : ((((p4 → (False ∧ ((p3 ∧ (((True → p5) ∨ (((p5 ∧ False) ∧ p4) ∧ (p3 ∧ (p2 ∧ False)))) ∧ p2)) ∧ ((True ∨ False) ∨ p1)))) ∧ p4) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_630728325891504197397811293117 : (((((p3 → ((((True → (p4 → (False → ((((True → p1) → p4) → p2) ∧ p5)))) ∨ (p2 → (p5 → False))) ∧ p2) ∨ p2)) ∨ False) → False) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_147598725637490592826738568748 : (((((True ∨ (True → (p1 → (p5 → (((p3 ∧ p5) ∧ True) ∨ p1))))) ∨ ((p5 ∨ p1) ∧ p1)) ∨ p5) → p3) ∨ ((p3 ∨ (False ∧ p5)) → p3)) := by
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
    -- Conjunctions on the left can always be decomposed.
    let h4 := h3.left
    let h5 := h3.right
    -- False on the left can always be used.
    apply False.elim h4



