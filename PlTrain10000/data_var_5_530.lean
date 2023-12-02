variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_232648505624977943816946271039 : ((p1 ∧ (True ∧ p1)) → (p2 ∨ (((p2 ∧ ((p4 ∧ ((((p2 → (p1 → p2)) ∨ ((True → p2) ∨ p1)) → p2) → p3)) → False)) ∨ True) ∧ True))) := by
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
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_427035174059796100431348249065 : ((((((((p2 ∧ ((p1 ∧ (p1 ∨ p2)) ∨ p4)) ∨ (((p4 ∨ True) → ((p2 → p5) ∨ False)) ∧ p1)) ∧ p4) ∧ p3) ∧ p5) ∨ (False → p3)) ∧ True) ∧ True) := by
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
theorem thm_5_vars_221810570811790730440266396416 : (((p2 ∧ p4) → True) ∧ (((((p3 ∨ (False → (((False ∧ p2) → p5) → p1))) → (False ∧ p2)) → False) → (((p4 ∨ p5) ∨ p2) ∧ False)) ∨ True)) := by
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
theorem thm_5_vars_350186212682350099613832705648 : (p4 → (((((True → True) ∨ False) ∨ p1) → ((p5 ∨ ((p5 ∨ ((True → ((p1 → p1) → (p2 → p1))) ∨ p3)) ∨ p4)) ∨ (p5 ∧ p1))) ∨ True)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_147008008296178572117785217280 : (((((((False ∧ p3) ∧ p3) ∧ False) ∧ ((p5 ∨ (p5 → ((p1 ∨ True) → p1))) → p3)) ∨ (False ∧ p2)) ∧ p1) ∨ ((p5 → p4) → (p4 ∨ True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_56020090324352707961108042153 : (((((p5 ∨ True) → p3) ∨ p3) ∨ ((p2 ∨ p4) ∨ (((p1 ∧ True) ∧ (p4 → (p5 ∨ True))) ∧ (((False ∨ (p4 → p3)) ∨ False) → p3)))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_696650086218099744678258040478 : (((((False ∧ (((p1 ∨ False) ∧ p2) → (p4 ∨ (p3 ∨ p3)))) ∨ p2) ∧ (((p2 → p3) → p5) ∧ (((True → p4) → p3) ∨ (p3 ∧ p2)))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_47530908891774075134806901350 : (((p4 ∨ (((((((True ∨ p5) ∨ (p1 → (p2 → p3))) ∧ p5) ∧ (p2 ∨ p2)) → (p5 → p2)) ∧ p4) → (False ∨ False))) ∨ (p5 → False)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_229118038078930183184693981176 : ((True → (p1 ∧ p2)) ∨ (True → (((p3 ∧ (p3 ∧ ((p2 ∧ p3) ∧ (p1 → False)))) ∧ p3) ∨ (p2 → ((p1 → p3) → ((p2 ∨ p1) ∨ p5)))))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h2
  -- Implications on the right can always be decomposed.
  intro h3
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- One of the premise coincides with the conclusion.
  exact h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_59028934101746361492405827087 : (((p4 ∧ True) ∨ (p2 → ((((((p5 ∨ False) ∧ ((False ∨ (p5 ∧ (p5 ∨ p4))) ∧ p1)) ∨ p1) ∨ p5) → ((p2 ∧ False) ∨ True)) ∨ p5))) ∨ p2) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h2
  -- Disjunctions on the left can always be decomposed.
  cases h2
  case inl h3 =>
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
        let h8 := h6.left
        let h9 := h6.right
        -- Disjunctions on the left can always be decomposed.
        cases h8
        case inl h10 =>
          -- False on the left can always be used.
          apply False.elim h10
        case inr h11 =>
          -- Conjunctions on the left can always be decomposed.
          let h12 := h11.left
          let h13 := h11.right
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
        -- False on the left can always be used.
        apply False.elim h16
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
theorem thm_5_vars_685301323454577207767402163864 : ((((p2 → ((p4 → p4) ∧ (False ∨ (p3 ∧ (((p4 ∧ p4) ∨ p3) ∧ (p4 ∧ (True → True))))))) ∨ ((p1 ∨ p1) ∨ ((p3 ∧ p4) ∨ True))) ∨ p4) ∧ True) := by
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
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_136479205355579887497515781894 : ((((p3 ∧ p1) ∨ p2) ∧ (p2 → ((True ∧ p2) ∧ ((p2 ∧ (((p4 ∧ p1) → False) → (p4 ∨ (True → p2)))) ∧ p3)))) ∨ (False → (p4 → False))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_356520960745921446440645172703 : (p5 → (((p1 → (p4 → (p5 → ((True → p3) → p2)))) ∧ p5) ∨ ((((p3 → p1) ∨ p4) ∧ ((True → (p3 → (p4 ∨ False))) ∨ p1)) ∨ True))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_50376715579202692533586807403 : ((((p2 ∧ p1) ∧ ((False ∧ p5) ∧ ((p5 ∧ (True ∨ ((p2 ∧ p3) ∧ p1))) ∨ ((p1 ∨ False) ∧ p3)))) ∨ ((p1 ∧ True) ∧ (p5 ∨ p5))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_607864844425278200789582598338 : (((((True → (((((p2 ∨ (p1 ∧ True)) ∧ p3) ∧ (((p3 → (p1 → False)) ∨ p4) ∧ p2)) ∧ ((p1 ∨ p2) ∨ False)) ∧ p3)) ∧ True) ∨ True) ∨ p1) ∧ True) := by
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
theorem thm_5_vars_354968040779411405714169297573 : (p5 → ((p3 → (((((p1 → p2) ∨ ((p5 → (p1 ∧ p1)) → ((p4 ∧ p2) ∧ (p1 ∨ p5)))) ∧ p2) → False) ∨ ((p1 ∨ False) ∧ False))) ∨ True)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_767881301672550005691750660605 : (((p5 ∧ (((p5 ∨ ((False → (p5 ∨ p5)) ∨ True)) ∨ (((((False ∨ p5) → ((p3 → True) ∧ False)) ∨ (p3 ∨ p5)) ∨ p4) → p5)) → p5)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_249621660318819977417790085355 : ((p5 ∨ p3) ∨ (((True ∧ (p5 ∧ p1)) ∧ p5) ∨ ((False ∨ p4) → ((((True ∧ (False ∧ p5)) → (p4 ∧ True)) ∨ (p5 → (p3 ∨ p5))) → p4)))) := by
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
    -- Disjunctions on the left can always be decomposed.
    cases h1
    case inl h4 =>
      -- False on the left can always be used.
      apply False.elim h4
    case inr h5 =>
      -- One of the premise coincides with the conclusion.
      exact h5
  case inr h6 =>
    -- Disjunctions on the left can always be decomposed.
    cases h1
    case inl h7 =>
      -- False on the left can always be used.
      apply False.elim h7
    case inr h8 =>
      -- One of the premise coincides with the conclusion.
      exact h8



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_197980498723171166520632206218 : (((p2 ∨ p1) ∧ ((p1 ∨ True) ∨ (p5 ∧ False))) ∨ ((p1 ∨ ((((True ∨ (p3 ∨ p2)) → p3) ∧ (p1 → p4)) ∧ p1)) ∨ ((False ∧ p3) ∨ True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_143787086896640406068600688189 : ((((p5 → (((True → p3) ∨ ((False ∧ p1) ∨ (p2 → (p1 ∨ False)))) ∨ (p2 ∨ (True → True)))) ∧ True) ∨ p3) ∧ ((True ∨ p1) → (False ∨ True))) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
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
  -- Implications on the right can always be decomposed.
  intro h2
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- Implications on the right can always be decomposed.
  intro h3
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



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_114188769951242377877832599941 : (((((p5 → p3) ∧ (p5 ∨ (p3 ∨ ((p2 ∨ (True → p3)) ∧ p3)))) ∨ (p3 → ((p3 ∨ p4) → True))) → (p4 ∧ (p2 → p2))) ∨ (True ∨ p1)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_744117777567687856957421750722 : ((((p1 ∧ True) → (p1 ∧ ((((p2 → (False ∧ p5)) → (p5 ∧ ((False ∨ (p4 ∧ p4)) ∨ ((False ∨ (p1 ∧ p5)) ∧ p4)))) ∨ p2) → p4))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_185545410125859233623176472335 : ((p3 ∨ (p5 → ((p1 ∨ p2) ∨ (((p3 ∨ p4) → p4) ∧ p2)))) ∨ (((True → (((p5 ∧ p5) → True) ∨ p2)) ∨ (True ∨ p4)) → (p5 → p5))) := by
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
    -- Disjunctions on the left can always be decomposed.
    cases h4
    case inl h5 =>
      -- One of the premise coincides with the conclusion.
      exact h2
    case inr h6 =>
      -- One of the premise coincides with the conclusion.
      exact h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_201118484744233168825091584122 : ((True → (p1 ∧ (p4 ∧ ((False ∧ False) ∨ p3)))) → (((False ∧ p5) ∨ ((p1 ∧ (((p5 ∨ p4) ∨ p4) ∨ ((False ∧ True) ∨ p4))) → p3)) ∨ False)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h2 : True := by
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h3 := h1 h2
  -- We need to get the right conjuct of h3 based on <expert-advice>.
  let h4 := h3.right
  -- We need to get the right conjuct of h4 based on <expert-advice>.
  let h5 := h4.right
  -- Disjunctions on the left can always be decomposed.
  cases h5
  case inl h6 =>
    -- Conjunctions on the left can always be decomposed.
    let h7 := h6.left
    let h8 := h6.right
    -- False on the left can always be used.
    apply False.elim h7
  case inr h9 =>
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h10
    -- Conjunctions on the left can always be decomposed.
    let h11 := h10.left
    let h12 := h10.right
    -- Disjunctions on the left can always be decomposed.
    cases h12
    case inl h13 =>
      -- Disjunctions on the left can always be decomposed.
      cases h13
      case inl h14 =>
        -- Disjunctions on the left can always be decomposed.
        cases h14
        case inl h15 =>
          -- One of the premise coincides with the conclusion.
          exact h9
        case inr h16 =>
          -- One of the premise coincides with the conclusion.
          exact h9
      case inr h17 =>
        -- One of the premise coincides with the conclusion.
        exact h9
    case inr h18 =>
      -- Disjunctions on the left can always be decomposed.
      cases h18
      case inl h19 =>
        -- Conjunctions on the left can always be decomposed.
        let h20 := h19.left
        let h21 := h19.right
        -- False on the left can always be used.
        apply False.elim h20
      case inr h22 =>
        -- One of the premise coincides with the conclusion.
        exact h9



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_204800888908800908691656627500 : (((((p3 ∧ p4) ∧ True) ∨ True) → p1) ∨ ((p5 ∧ ((p5 → (p4 ∨ False)) → ((((p2 ∧ p1) ∧ (p3 ∨ False)) ∨ p1) ∧ p3))) ∨ (True ∨ p1))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_219037944820224863528179361362 : ((p5 ∧ ((True → p4) ∨ p4)) → (((p3 ∧ (p2 ∧ p2)) ∨ ((((True ∨ ((p5 ∧ p4) ∨ (False ∧ p1))) → (p5 ∧ True)) ∨ p2) ∨ p2)) ∧ p5)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- Disjunctions on the left can always be decomposed.
  cases h3
  case inl h4 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Implications on the right can always be decomposed.
    intro h5
    -- Conjunctions on the right can always be decomposed.
    apply And.intro
    -- Disjunctions on the left can always be decomposed.
    cases h5
    case inl h6 =>
      -- One of the premise coincides with the conclusion.
      exact h2
    case inr h7 =>
      -- Disjunctions on the left can always be decomposed.
      cases h7
      case inl h8 =>
        -- Conjunctions on the left can always be decomposed.
        let h9 := h8.left
        let h10 := h8.right
        -- One of the premise coincides with the conclusion.
        exact h9
      case inr h11 =>
        -- Conjunctions on the left can always be decomposed.
        let h12 := h11.left
        let h13 := h11.right
        -- False on the left can always be used.
        apply False.elim h12
    -- True on the right can always be proven directly.
    apply True.intro
  case inr h14 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Implications on the right can always be decomposed.
    intro h15
    -- Conjunctions on the right can always be decomposed.
    apply And.intro
    -- Disjunctions on the left can always be decomposed.
    cases h15
    case inl h16 =>
      -- One of the premise coincides with the conclusion.
      exact h2
    case inr h17 =>
      -- Disjunctions on the left can always be decomposed.
      cases h17
      case inl h18 =>
        -- Conjunctions on the left can always be decomposed.
        let h19 := h18.left
        let h20 := h18.right
        -- One of the premise coincides with the conclusion.
        exact h19
      case inr h21 =>
        -- Conjunctions on the left can always be decomposed.
        let h22 := h21.left
        let h23 := h21.right
        -- False on the left can always be used.
        apply False.elim h22
    -- True on the right can always be proven directly.
    apply True.intro
  -- Conjunctions on the left can always be decomposed.
  let h24 := h1.left
  let h25 := h1.right
  -- Disjunctions on the left can always be decomposed.
  cases h25
  case inl h26 =>
    -- One of the premise coincides with the conclusion.
    exact h24
  case inr h27 =>
    -- One of the premise coincides with the conclusion.
    exact h24



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_258296394549424670740280755601 : ((p5 ∨ True) → (((((p5 ∧ (p4 ∧ p5)) ∨ p1) ∨ (p1 → ((p2 → p5) ∨ ((p3 ∨ p1) ∧ False)))) ∨ p5) → ((p2 ∧ (True ∨ p5)) ∨ True))) := by
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
        let h6 := h5.left
        let h7 := h5.right
        -- Conjunctions on the left can always be decomposed.
        let h8 := h7.left
        let h9 := h7.right
        -- Disjunctions on the left can always be decomposed.
        cases h1
        case inl h10 =>
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
        cases h1
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
      -- Disjunctions on the left can always be decomposed.
      cases h1
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
    -- Disjunctions on the left can always be decomposed.
    cases h1
    case inl h19 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- True on the right can always be proven directly.
      apply True.intro
    case inr h20 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- True on the right can always be proven directly.
      apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_303114493659995672309982460015 : (False ∨ (p3 → (((((((p4 → p4) → p2) ∨ (p2 → p1)) ∨ p4) ∧ True) ∨ (((p5 ∨ p3) → (p1 ∧ (p2 ∨ p5))) → p1)) ∧ (p3 ∨ False)))) := by
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
  -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
  have h3 : (p5 ∨ p3) := by
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h1
  -- We have shown the premise of h2, we can now drive its conclusion.
  let h4 := h2 h3
  -- We need to get the left conjuct of h4 based on <expert-advice>.
  let h5 := h4.left
  -- One of the premise coincides with the conclusion.
  exact h5
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_155163872287310584614576033333 : (((((p4 ∧ True) ∨ p5) → ((p2 ∧ (p4 → p5)) ∨ p2)) → ((((True ∨ p2) → False) ∨ True) ∨ p5)) ∧ (((p3 ∨ (True ∨ p5)) → True) ∨ False)) := by
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
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h2
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_181631995846186085369658619086 : ((p2 → (p5 → ((p4 ∧ (((p4 ∨ p1) ∧ p1) ∨ (p2 ∧ p4))) ∨ p4))) → (True ∧ ((p5 → False) ∨ (((p2 → False) ∧ (p3 ∧ p4)) → p4)))) := by
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
  -- Conjunctions on the left can always be decomposed.
  let h3 := h2.left
  let h4 := h2.right
  -- Conjunctions on the left can always be decomposed.
  let h5 := h4.left
  let h6 := h4.right
  -- One of the premise coincides with the conclusion.
  exact h6



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_68142360558342691979791539540 : ((p3 → (((p1 ∨ ((p1 ∧ (((((True → (p1 ∧ p4)) → (p4 ∨ (p2 ∧ (p5 ∧ p4)))) ∧ p1) ∧ False) → False)) ∧ p2)) → p5) ∧ p1)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_53564841841037401486015040158 : ((((((p4 ∨ p1) → (p2 → False)) ∨ (True ∨ True)) ∨ p3) ∧ (p2 → (p4 → ((((p4 ∨ (p3 → p3)) → p1) → (p3 ∨ p1)) ∨ p3)))) ∨ p3) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
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
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h3
  -- We want to use the implication h3 based on <expert-advice>. So we show its premise.
  have h4 : (p4 ∨ (p3 → p3)) := by
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- One of the premise coincides with the conclusion.
    exact h2
  -- We have shown the premise of h3, we can now drive its conclusion.
  let h5 := h3 h4
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h5



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_549428692645203699949247978 : ((((p2 → ((p1 ∨ p2) ∨ True)) → (((((True ∧ False) ∨ ((((False ∨ False) → p3) → True) → p2)) ∧ p2) ∧ p1) ∧ p5)) ∨ True) ∨ False) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_58783716994205193544950082617 : (((p4 → p5) ∧ (((p2 ∧ (p2 ∧ (False → (((False ∧ (((p4 → p2) → (True ∨ p2)) ∧ p4)) ∧ p5) → False)))) → p3) → (p5 ∨ False))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_148036337417678851031398326265 : ((((p4 → p2) ∧ ((((p3 → (p4 ∧ False)) ∧ p2) → p3) ∨ (False ∨ (p2 → (p5 ∧ True))))) ∨ (p5 ∨ True)) ∨ (p4 → ((p5 ∧ p2) → p5))) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_326846080020619633805262324078 : (True → ((((False ∨ p2) ∨ ((((((p1 ∨ p4) ∨ (True ∨ ((False → p5) → p4))) → (p1 ∧ p2)) ∧ (False → p1)) ∨ p5) → p5)) ∧ p2) ∨ True)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_613801430694980881987822995611 : (((((True → (p5 ∨ (((p1 → ((p3 → (True ∧ p3)) ∨ True)) ∨ (p4 → True)) → ((p4 → False) ∧ p2)))) ∧ ((p4 ∨ p3) ∧ p1)) ∨ False) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_309933999422815167786240099427 : (p2 ∨ (((p2 → p4) → ((p3 ∨ p2) ∨ (p5 ∧ (p4 ∧ ((((p5 ∨ p4) ∧ p5) → p1) ∨ False))))) ∨ (False → (True → (p5 ∧ (p2 ∧ True)))))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- False on the left can always be used.
  apply False.elim h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- False on the left can always be used.
  apply False.elim h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_600304299142922415682974994143 : (((((p5 → True) → ((p2 ∨ ((p3 ∨ (p4 ∨ (((p5 ∨ (p2 → (p5 → (p2 ∧ (p5 ∨ False))))) → p3) → True))) → False)) → p5)) ∧ p3) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_196927184811646162715248894691 : ((((p2 ∧ ((p4 ∨ p1) ∨ p5)) ∧ p3) ∨ p2) ∨ (((p2 ∧ (p4 → p4)) → p1) ∨ (p4 → ((p2 → p4) → ((True ∨ p3) → (p4 ∨ False)))))) := by
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
  -- Disjunctions on the left can always be decomposed.
  cases h3
  case inl h4 =>
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- One of the premise coincides with the conclusion.
    exact h1
  case inr h5 =>
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- One of the premise coincides with the conclusion.
    exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_186348560479010938753577556374 : (((((p3 → p5) → p4) ∨ (False ∨ (p5 ∧ (p3 → p2)))) → p5) → ((p2 → p2) ∧ (((p2 → (False ∨ p1)) ∨ True) ∨ (p3 ∨ (True ∨ True))))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h2
  -- One of the premise coincides with the conclusion.
  exact h2
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_166229849682616289320380731235 : ((p2 ∧ ((p1 → (p5 → True)) ∧ (True → (p5 → ((p2 ∧ p1) ∨ (True ∧ (p2 → False))))))) ∨ (((True → p2) ∧ p3) → ((p3 → False) → False))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Conjunctions on the left can always be decomposed.
  let h3 := h1.left
  let h4 := h1.right
  -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
  have h5 : p3 := by
    -- One of the premise coincides with the conclusion.
    exact h4
  -- We have shown the premise of h2, we can now drive its conclusion.
  let h6 := h2 h5
  -- False on the left can always be used.
  apply False.elim h6



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_310214008315201497700078572264 : (p2 ∨ (((((p3 → p1) ∨ p5) ∨ p2) → (p5 ∨ (False ∨ (False → True)))) ∨ ((p2 ∧ p1) → (p4 → (p4 ∨ ((False ∨ p2) ∧ (False ∧ p3))))))) := by
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
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- One of the premise coincides with the conclusion.
  exact h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_234657009430538012967365253595 : ((p4 → (True ∧ p3)) → ((True ∧ ((p2 ∧ (True ∨ True)) → ((p5 ∨ (((p2 → p2) ∧ (False ∨ p2)) → (False ∧ (p4 ∨ p3)))) ∨ p2))) ∨ p1)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- Implications on the right can always be decomposed.
  intro h2
  -- Conjunctions on the left can always be decomposed.
  let h3 := h2.left
  let h4 := h2.right
  -- Disjunctions on the left can always be decomposed.
  cases h4
  case inl h5 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h3
  case inr h6 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h3



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_37222279880782486796098702231 : (((((p3 → (False → p4)) → ((p1 ∧ (((p2 ∧ (p2 ∧ (((False ∨ p1) ∧ p5) ∧ p4))) ∧ (p1 ∧ True)) → p4)) → p2)) ∧ p3) ∧ p3) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_134276899826583813022713115146 : ((((False → p4) ∧ ((((p3 ∧ (p4 ∨ (True ∨ (((True ∨ (p1 ∧ p1)) → True) ∧ True)))) ∨ p4) ∧ p5) → False)) ∨ p1) ∨ ((p5 ∨ False) → p5)) := by
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
    -- False on the left can always be used.
    apply False.elim h3



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_65691171588169095550476368152 : ((p4 ∨ ((p4 ∧ ((((p3 ∧ p5) ∨ (p4 → (((p3 ∨ ((p4 ∨ p1) ∨ p2)) ∧ p5) ∧ True))) → p4) ∨ (p3 ∨ (p3 ∧ p1)))) → p2)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_149938389132487106693657847592 : ((p3 ∨ ((False → p1) → ((p2 ∧ (p3 ∨ (True → ((p5 → (p3 ∨ (p1 ∨ p5))) → (p4 → p1))))) ∨ p3))) ∨ (p2 → ((True ∧ True) ∨ True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_89267075287693335412391148218 : (((p4 ∧ (True → p3)) ∧ ((((False ∧ p5) ∧ True) ∨ ((p5 → ((False → p5) ∨ False)) ∧ False)) → (p2 → ((p3 ∧ (False ∧ p1)) ∨ True)))) → p3) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- Conjunctions on the left can always be decomposed.
  let h4 := h2.left
  let h5 := h2.right
  -- We want to use the implication h5 based on <expert-advice>. So we show its premise.
  have h6 : True := by
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h5, we can now drive its conclusion.
  let h7 := h5 h6
  -- One of the premise coincides with the conclusion.
  exact h7



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_705303023519251118697883502859 : ((((((False ∨ ((True → True) → p2)) ∧ True) ∨ True) ∧ (False ∨ (p4 ∨ ((p1 → (p5 ∨ ((True ∧ p5) ∨ (p1 ∨ p3)))) ∨ (p5 → p2))))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_158661567028379770808121409796 : ((p1 ∧ (p4 ∨ ((p3 → p1) ∧ ((p3 ∧ p4) ∨ (p2 ∨ ((p1 ∧ (True → (True → True))) ∨ False)))))) ∨ (p3 → (p1 ∨ ((False → p3) ∨ p5)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
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
theorem thm_5_vars_51081435764558178217752877139 : (((p5 → ((True ∧ (((False ∧ ((False → p5) ∨ p3)) ∧ p4) ∧ ((p5 ∧ False) ∧ p3))) ∨ p3)) ∧ (True → (False → ((p2 ∨ p4) → p3)))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_346619923160188611652248645717 : (p3 → (((((p1 ∨ True) → p3) → p1) ∨ ((((((p5 → (p1 → False)) ∨ True) → (p2 → p3)) ∨ p3) ∨ p1) → p2)) ∨ (p2 ∨ (False ∨ True)))) := by
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
theorem thm_5_vars_68884149500102815683560398384 : ((p4 → (p2 ∧ ((p1 → ((p3 ∨ p4) ∧ p2)) ∧ (((((p1 ∨ (True → (p3 ∧ True))) → False) ∨ p3) → p2) → ((p1 ∨ p3) ∨ p1))))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_95298647279655236667020173922 : ((p4 ∧ (p3 ∧ (((((p3 ∨ p2) → ((((p3 → True) ∨ (False ∧ p4)) ∨ p1) ∧ False)) ∧ p2) ∧ p2) ∧ (((False → True) ∧ True) ∧ p5)))) → False) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- Conjunctions on the left can always be decomposed.
  let h4 := h3.left
  let h5 := h3.right
  -- Conjunctions on the left can always be decomposed.
  let h6 := h5.left
  let h7 := h5.right
  -- Conjunctions on the left can always be decomposed.
  let h8 := h6.left
  let h9 := h6.right
  -- Conjunctions on the left can always be decomposed.
  let h10 := h8.left
  let h11 := h8.right
  -- Conjunctions on the left can always be decomposed.
  let h12 := h7.left
  let h13 := h7.right
  -- Conjunctions on the left can always be decomposed.
  let h14 := h12.left
  let h15 := h12.right
  -- We want to use the implication h10 based on <expert-advice>. So we show its premise.
  have h16 : (p3 ∨ p2) := by
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- One of the premise coincides with the conclusion.
    exact h4
  -- We have shown the premise of h10, we can now drive its conclusion.
  let h17 := h10 h16
  -- We need to get the right conjuct of h17 based on <expert-advice>.
  let h18 := h17.right
  -- False on the left can always be used.
  apply False.elim h18



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_3249421110489167118820643090 : ((p5 ∨ p3) ∨ (((((p2 ∧ ((True ∧ (p1 ∨ p1)) ∨ p2)) ∨ p2) → (((p2 ∨ True) ∧ ((p4 → p3) ∧ p1)) → p5)) ∨ True) ∧ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_328886511002002229822438084893 : (True → (((True ∨ ((p4 ∨ p3) ∨ p3)) → (p5 ∨ p2)) ∨ (p3 → (((p4 ∨ p5) → ((p2 → (((p2 ∨ p5) ∧ p3) ∨ p4)) ∨ p3)) ∨ False)))) := by
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
  -- Disjunctions on the left can always be decomposed.
  cases h3
  case inl h4 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h2
  case inr h5 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_345543155262622801260598600748 : (p3 → (((((p5 ∧ (p1 ∨ p3)) ∧ p1) ∨ p3) ∧ (((p4 ∨ ((False ∨ p1) ∨ (((p4 → p1) ∧ True) ∧ p4))) ∧ (p3 ∨ False)) ∨ p2)) ∨ p3)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_637493970819629045536723350699 : (((((True → (p3 ∨ (True → (((False ∧ p2) ∨ False) ∨ False)))) ∧ ((p5 ∧ p3) → (((False ∧ p5) ∨ ((p1 → p3) → p5)) → True))) → p3) ∨ p4) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
  have h4 : True := by
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h2, we can now drive its conclusion.
  let h5 := h2 h4
  -- Disjunctions on the left can always be decomposed.
  cases h5
  case inl h6 =>
    -- One of the premise coincides with the conclusion.
    exact h6
  case inr h7 =>
    -- We want to use the implication h7 based on <expert-advice>. So we show its premise.
    have h8 : True := by
      -- True on the right can always be proven directly.
      apply True.intro
    -- We have shown the premise of h7, we can now drive its conclusion.
    let h9 := h7 h8
    -- Disjunctions on the left can always be decomposed.
    cases h9
    case inl h10 =>
      -- Disjunctions on the left can always be decomposed.
      cases h10
      case inl h11 =>
        -- Conjunctions on the left can always be decomposed.
        let h12 := h11.left
        let h13 := h11.right
        -- False on the left can always be used.
        apply False.elim h12
      case inr h14 =>
        -- False on the left can always be used.
        apply False.elim h14
    case inr h15 =>
      -- False on the left can always be used.
      apply False.elim h15
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_118325677760682386249780840308 : ((p2 ∨ ((((True → (((p3 ∨ ((True ∧ p1) ∨ (p5 → False))) → False) → False)) → ((True → p4) ∨ (p1 ∧ p1))) ∨ p2) ∧ p5)) ∨ (p3 → True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_178369175895298228762660158741 : (((((p3 ∧ p1) → ((p1 → (p4 → False)) ∧ True)) ∧ p1) → (p4 ∧ p3)) ∨ (p1 ∨ (((True ∨ ((p2 → p5) ∨ p3)) ∨ p5) ∨ (False ∨ p5)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_206433337040814261445322912469 : ((p4 ∨ ((p5 ∨ (p4 ∧ p2)) ∧ p4)) ∨ ((((((True ∨ True) ∨ False) ∨ ((p4 ∧ p3) ∨ ((p3 → True) ∧ p4))) ∧ p1) ∧ False) → (p3 ∧ False))) := by
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
  -- Disjunctions on the left can always be decomposed.
  cases h4
  case inl h6 =>
    -- Disjunctions on the left can always be decomposed.
    cases h6
    case inl h7 =>
      -- Disjunctions on the left can always be decomposed.
      cases h7
      case inl h8 =>
        -- False on the left can always be used.
        apply False.elim h3
      case inr h9 =>
        -- False on the left can always be used.
        apply False.elim h3
    case inr h10 =>
      -- False on the left can always be used.
      apply False.elim h10
  case inr h11 =>
    -- Disjunctions on the left can always be decomposed.
    cases h11
    case inl h12 =>
      -- Conjunctions on the left can always be decomposed.
      let h13 := h12.left
      let h14 := h12.right
      -- False on the left can always be used.
      apply False.elim h3
    case inr h15 =>
      -- Conjunctions on the left can always be decomposed.
      let h16 := h15.left
      let h17 := h15.right
      -- False on the left can always be used.
      apply False.elim h3
  -- Conjunctions on the left can always be decomposed.
  let h18 := h1.left
  let h19 := h1.right
  -- Conjunctions on the left can always be decomposed.
  let h20 := h18.left
  let h21 := h18.right
  -- Disjunctions on the left can always be decomposed.
  cases h20
  case inl h22 =>
    -- Disjunctions on the left can always be decomposed.
    cases h22
    case inl h23 =>
      -- Disjunctions on the left can always be decomposed.
      cases h23
      case inl h24 =>
        -- False on the left can always be used.
        apply False.elim h19
      case inr h25 =>
        -- False on the left can always be used.
        apply False.elim h19
    case inr h26 =>
      -- False on the left can always be used.
      apply False.elim h26
  case inr h27 =>
    -- Disjunctions on the left can always be decomposed.
    cases h27
    case inl h28 =>
      -- Conjunctions on the left can always be decomposed.
      let h29 := h28.left
      let h30 := h28.right
      -- False on the left can always be used.
      apply False.elim h19
    case inr h31 =>
      -- Conjunctions on the left can always be decomposed.
      let h32 := h31.left
      let h33 := h31.right
      -- False on the left can always be used.
      apply False.elim h19



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_52579327076052844482112856543 : (((((p5 ∧ p5) ∨ (((p4 → p1) ∧ (p5 ∧ p3)) → p3)) → (p3 ∧ p4)) ∨ ((p2 ∧ (p3 → ((p1 → (p1 → p4)) → p3))) → p5)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_350146687101051733067569137135 : (p4 → (((p1 ∨ ((p3 → p5) ∧ ((p4 ∧ False) ∨ (p5 → (p4 → p4))))) → ((p3 ∨ p3) ∧ ((((p3 ∨ p4) → p3) ∨ p2) ∧ p2))) ∨ True)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_7780751117543643315224788360 : (((((p5 → ((p5 ∧ (p4 ∧ (p5 → (p1 → True)))) ∨ ((p2 → p5) ∨ (p1 ∨ False)))) → (True → ((p1 ∨ p2) ∧ True))) ∧ p5) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_70131842704772068065736414155 : ((((((p4 ∨ False) ∨ p5) → (p1 ∨ ((p1 ∨ (p3 ∨ (p4 ∨ False))) ∧ (True ∨ (((p4 ∧ (p5 ∧ p3)) ∨ p4) ∧ p4))))) → p1) ∧ p4) → p1) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
  have h4 : (((p4 ∨ False) ∨ p5) → (p1 ∨ ((p1 ∨ (p3 ∨ (p4 ∨ False))) ∧ (True ∨ (((p4 ∧ (p5 ∧ p3)) ∨ p4) ∧ p4))))) := by
    -- Implications on the right can always be decomposed.
    intro h5
    -- Disjunctions on the left can always be decomposed.
    cases h5
    case inl h6 =>
      -- Disjunctions on the left can always be decomposed.
      cases h6
      case inl h7 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- Conjunctions on the right can always be decomposed.
        apply And.intro
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- One of the premise coincides with the conclusion.
        exact h7
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- True on the right can always be proven directly.
        apply True.intro
      case inr h8 =>
        -- False on the left can always be used.
        apply False.elim h8
    case inr h9 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Conjunctions on the right can always be decomposed.
      apply And.intro
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- One of the premise coincides with the conclusion.
      exact h3
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- True on the right can always be proven directly.
      apply True.intro
  -- We have shown the premise of h2, we can now drive its conclusion.
  let h10 := h2 h4
  -- One of the premise coincides with the conclusion.
  exact h10



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_308683527727963446349887287839 : (p2 ∨ ((False ∨ (p2 ∧ ((False ∨ ((p4 ∧ p4) ∧ ((True ∧ False) → p1))) ∧ (p1 ∧ ((False ∨ (p4 ∧ p1)) ∧ ((p4 → False) → p3)))))) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_156983432372393980258847864797 : ((((p2 ∨ (p4 ∨ (((False → p3) ∨ True) ∨ p4))) → ((p3 ∧ ((p1 ∧ p3) ∧ p5)) → False)) ∨ True) ∨ (p3 ∨ ((True ∧ (p3 ∨ False)) → True))) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_697532792031581637192488131936 : ((((p5 ∧ (False ∧ (p5 → (False ∧ (False → ((p3 ∨ p1) → p5)))))) ∧ ((((((False ∧ False) → False) → p3) ∨ p5) ∧ p1) → (p4 ∧ p3))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_208744019051721702822049866574 : ((p1 ∧ (False ∨ (p1 ∨ (p1 ∧ False)))) → ((p5 → p2) ∨ ((((False ∨ ((p2 ∨ ((p4 ∨ p3) ∨ False)) → (p2 ∨ p3))) → False) ∨ False) ∨ p1))) := by
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
    -- Disjunctions on the left can always be decomposed.
    cases h5
    case inl h6 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- One of the premise coincides with the conclusion.
      exact h6
    case inr h7 =>
      -- Conjunctions on the left can always be decomposed.
      let h8 := h7.left
      let h9 := h7.right
      -- False on the left can always be used.
      apply False.elim h9



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_740912012833448655698659476197 : ((((p3 ∨ p2) ∨ ((p4 → ((p5 ∨ p4) ∧ (p2 → (p4 → (((True ∨ p4) → p5) ∧ (p4 ∨ ((True → p2) ∨ p1))))))) ∧ (True ∨ p2))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_213387536790415354824239458889 : (((False ∨ (True ∧ p2)) ∧ p4) ∨ (((((p3 ∨ ((p2 ∨ False) ∨ (p4 ∨ False))) ∨ False) → (False ∧ (p4 → p1))) ∧ ((p3 ∨ True) → p4)) → p2)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- We want to use the implication h3 based on <expert-advice>. So we show its premise.
  have h4 : (p3 ∨ True) := by
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h3, we can now drive its conclusion.
  let h5 := h3 h4
  -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
  have h6 : ((p3 ∨ ((p2 ∨ False) ∨ (p4 ∨ False))) ∨ False) := by
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- One of the premise coincides with the conclusion.
    exact h5
  -- We have shown the premise of h2, we can now drive its conclusion.
  let h7 := h2 h6
  -- We need to get the left conjuct of h7 based on <expert-advice>.
  let h8 := h7.left
  -- False on the left can always be used.
  apply False.elim h8



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_219522651381736493551687754213 : ((p5 ∨ (p3 ∧ (p1 → p3))) → (((True → p2) ∨ (p4 ∧ ((p1 → ((p4 ∧ p3) ∨ p2)) ∧ p3))) → ((p2 ∧ p3) ∨ (True ∨ (p1 ∨ False))))) := by
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
      -- True on the right can always be proven directly.
      apply True.intro
    case inr h5 =>
      -- Conjunctions on the left can always be decomposed.
      let h6 := h5.left
      let h7 := h5.right
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- True on the right can always be proven directly.
      apply True.intro
  case inr h8 =>
    -- Conjunctions on the left can always be decomposed.
    let h9 := h8.left
    let h10 := h8.right
    -- Conjunctions on the left can always be decomposed.
    let h11 := h10.left
    let h12 := h10.right
    -- Disjunctions on the left can always be decomposed.
    cases h1
    case inl h13 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- True on the right can always be proven directly.
      apply True.intro
    case inr h14 =>
      -- Conjunctions on the left can always be decomposed.
      let h15 := h14.left
      let h16 := h14.right
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- True on the right can always be proven directly.
      apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_608367342214583721884438008041 : ((((((p4 ∧ (p4 ∨ (((((((False ∧ True) ∨ p3) ∨ True) → ((False ∧ (p2 ∨ True)) ∨ p5)) → p4) → p3) ∧ p1))) ∨ p3) ∨ p2) ∨ True) ∨ False) ∧ True) := by
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
theorem thm_5_vars_609699176447360341366788274679 : (((((p2 ∨ (((True → (p1 → (p2 → (((p5 → (False ∧ p3)) ∨ p4) ∧ (True ∧ p2))))) ∧ False) ∧ (p1 ∨ (p4 ∨ p1)))) ∨ True) ∨ p3) ∨ False) ∧ True) := by
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
theorem thm_5_vars_82029712366874842790225171620 : (((((p1 → True) ∨ p3) → ((p5 ∧ ((p2 ∨ ((p2 ∨ False) → (p2 ∨ p3))) → p2)) ∨ (p5 → (p5 ∧ True)))) → ((p1 ∨ True) ∧ p5)) → p5) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h2 : (((p1 → True) ∨ p3) → ((p5 ∧ ((p2 ∨ ((p2 ∨ False) → (p2 ∨ p3))) → p2)) ∨ (p5 → (p5 ∧ True)))) := by
    -- Implications on the right can always be decomposed.
    intro h3
    -- Disjunctions on the left can always be decomposed.
    cases h3
    case inl h4 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Implications on the right can always be decomposed.
      intro h5
      -- Conjunctions on the right can always be decomposed.
      apply And.intro
      -- One of the premise coincides with the conclusion.
      exact h5
      -- True on the right can always be proven directly.
      apply True.intro
    case inr h6 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Implications on the right can always be decomposed.
      intro h7
      -- Conjunctions on the right can always be decomposed.
      apply And.intro
      -- One of the premise coincides with the conclusion.
      exact h7
      -- True on the right can always be proven directly.
      apply True.intro
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h8 := h1 h2
  -- We need to get the right conjuct of h8 based on <expert-advice>.
  let h9 := h8.right
  -- One of the premise coincides with the conclusion.
  exact h9



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_169062235050168010915673925703 : ((p3 → (((((p1 → p3) → (False → False)) → ((p1 → False) ∨ True)) ∧ True) ∧ (False ∧ True))) → (p3 → (((p1 ∧ (p2 ∨ p2)) ∨ p4) ∨ p2))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h3 : p3 := by
    -- One of the premise coincides with the conclusion.
    exact h2
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h4 := h1 h3
  -- We need to get the right conjuct of h4 based on <expert-advice>.
  let h5 := h4.right
  -- We need to get the left conjuct of h5 based on <expert-advice>.
  let h6 := h5.left
  -- False on the left can always be used.
  apply False.elim h6



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_381017118985137185460900209723 : (((((False ∧ ((p5 ∨ p1) ∧ (p2 → ((p3 ∨ ((p3 → (p4 ∧ (((p4 → False) ∧ False) ∧ p5))) ∨ False)) → (p2 → p4))))) ∧ p2) ∨ True) ∧ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
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



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_116828276869942918523932196705 : (((p5 ∨ p1) ∨ (True → (((((False ∨ p4) → False) ∨ ((True ∧ p2) ∨ (p1 ∧ p5))) → (((p3 ∧ p1) → p2) ∧ True)) → p1))) ∨ (False → False)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_66173308810075100242474677546 : ((p5 ∨ ((((False ∨ False) ∨ ((p5 ∨ p5) → False)) ∨ (p5 → (((False ∧ ((False ∨ p1) ∨ p2)) → p3) → p2))) → (p1 → (p2 ∧ p4)))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_183786308080150578386402421336 : ((((p2 ∨ (((True ∨ (p1 ∧ p5)) → p2) ∨ p2)) ∧ p1) ∧ p4) ∨ (((p4 ∨ False) ∧ ((p5 ∨ p2) ∧ (p3 ∧ False))) → (p3 ∨ (p4 ∧ p5)))) := by
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
    -- Conjunctions on the left can always be decomposed.
    let h5 := h3.left
    let h6 := h3.right
    -- Disjunctions on the left can always be decomposed.
    cases h5
    case inl h7 =>
      -- Conjunctions on the left can always be decomposed.
      let h8 := h6.left
      let h9 := h6.right
      -- False on the left can always be used.
      apply False.elim h9
    case inr h10 =>
      -- Conjunctions on the left can always be decomposed.
      let h11 := h6.left
      let h12 := h6.right
      -- False on the left can always be used.
      apply False.elim h12
  case inr h13 =>
    -- False on the left can always be used.
    apply False.elim h13



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_304689429904320510538465962783 : (p1 ∨ (((((p2 ∨ (p3 ∧ (True ∨ p4))) → p2) ∨ (((p1 ∨ p5) ∨ (p3 → ((p3 ∨ p5) ∨ False))) ∨ (p1 ∨ p1))) ∨ p3) ∨ (p4 ∧ True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_40643778449422000969425876959 : (((((p2 ∧ ((p3 ∨ (True → (p4 ∨ (True ∧ ((((p2 → p3) → (p3 ∧ p5)) ∨ True) ∧ p1))))) ∨ (True ∧ p3))) → p2) → p5) ∨ p5) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_250963350132004574620682406539 : ((p1 → p4) ∨ ((p1 ∧ False) ∨ ((p4 ∧ (((p2 ∧ (True → False)) ∧ (((False ∧ p1) → ((False ∧ True) ∧ p4)) → p2)) ∧ p2)) ∨ (p5 ∨ True)))) := by
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
theorem thm_5_vars_763450776948283577165110606697 : (((p3 ∧ (False ∧ (True → ((p5 → (p1 ∨ ((((((False → p1) → True) → (((p1 ∨ p1) ∨ False) ∧ p3)) → p2) ∧ p3) → True))) → p4)))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_61965861654512484323130229229 : ((p2 ∧ (((p3 ∧ (p3 ∨ (((p4 ∧ p4) ∨ p1) ∨ p2))) ∧ (p4 ∧ p1)) → (p4 → ((((False ∧ p1) ∨ (p2 → p5)) ∧ p4) ∨ True)))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_894278570179972144083835733213 : ((((p5 ∧ ((p5 → p4) ∧ ((True ∧ (p1 → True)) → ((p4 ∨ ((False ∨ ((False ∧ False) → True)) ∨ False)) ∧ False)))) ∧ (p4 ∧ (p2 ∧ p5))) → False) ∧ True) := by
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
  let h6 := h5.left
  let h7 := h5.right
  -- Conjunctions on the left can always be decomposed.
  let h8 := h3.left
  let h9 := h3.right
  -- Conjunctions on the left can always be decomposed.
  let h10 := h9.left
  let h11 := h9.right
  -- We want to use the implication h7 based on <expert-advice>. So we show its premise.
  have h12 : (True ∧ (p1 → True)) := by
    -- Conjunctions on the right can always be decomposed.
    apply And.intro
    -- True on the right can always be proven directly.
    apply True.intro
    -- Implications on the right can always be decomposed.
    intro h13
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h7, we can now drive its conclusion.
  let h14 := h7 h12
  -- We need to get the right conjuct of h14 based on <expert-advice>.
  let h15 := h14.right
  -- False on the left can always be used.
  apply False.elim h15
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_47933962645031084952374055809 : ((((p2 ∨ (p5 ∨ (((p2 ∨ p5) ∨ p1) ∨ ((((p4 → False) ∨ p2) ∨ p1) → (p5 → p3))))) ∧ ((p1 ∧ p1) → False)) → (False ∧ p2)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_112065890826042249455603553081 : ((((p5 ∨ False) ∧ ((((p4 → True) ∨ p3) ∧ (p2 → ((p1 ∨ ((p1 ∨ p4) ∧ p1)) ∧ p5))) ∨ (False → (False ∧ p3)))) ∨ True) ∨ (p3 ∨ p2)) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_608692378508690039959412647973 : ((((((((p2 ∨ ((False ∧ (False ∨ p4)) → (p2 → ((p3 → p2) → (True → p3))))) → (p3 ∨ False)) ∨ p1) → (False ∨ p3)) ∨ True) ∨ p5) ∨ p3) ∧ True) := by
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
theorem thm_5_vars_46896486248538056089615402213 : ((((((p1 ∧ p4) → (True ∨ ((p1 → (p5 ∨ (p2 → (True ∨ p3)))) ∧ ((p5 ∨ False) → (False ∧ p2))))) → p2) ∨ True) ∨ (p2 ∨ p2)) ∨ p4) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_342765864566596375768997541342 : (p2 → ((p4 ∧ (False ∧ ((p3 → (p4 → p2)) → False))) ∨ ((True ∧ True) ∨ ((p4 ∧ p5) ∨ ((((p5 → p4) ∨ True) ∨ p4) → (p1 → p3)))))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_157013593478595196580071809324 : (((((p1 → p1) ∨ True) → (((True ∨ (p5 → (((p4 ∨ True) ∨ p1) → False))) ∨ p5) → p4)) ∨ True) ∨ ((p5 ∧ p1) ∧ (False ∧ (p3 ∨ True)))) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_173410027415430276014418600359 : ((p5 → ((False ∨ (p5 → (p1 ∧ ((p1 → (False ∨ p2)) ∧ (p2 ∨ p2))))) ∨ p4)) ∨ (p1 → ((False ∨ (p1 ∧ (True ∨ p2))) ∧ (p1 ∨ p3)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- One of the premise coincides with the conclusion.
  exact h1
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_737537019303524744424171985031 : ((((p5 → False) ∧ ((((True → p1) ∧ p5) ∧ p4) ∧ (((((p2 ∨ p2) → p1) ∧ p2) ∧ (p5 ∨ (p1 ∨ p5))) ∧ (p3 ∨ (p3 → False))))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_246143754761756844163048354503 : ((p4 ∧ p2) ∨ (((p2 ∨ (p1 → (p3 → (((p5 ∨ (False → False)) ∧ (False → False)) → (p2 ∨ (True ∧ p3)))))) ∧ (p4 → True)) ∨ (p1 ∨ p4))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Implications on the right can always be decomposed.
  intro h3
  -- Conjunctions on the left can always be decomposed.
  let h4 := h3.left
  let h5 := h3.right
  -- Disjunctions on the left can always be decomposed.
  cases h4
  case inl h6 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Conjunctions on the right can always be decomposed.
    apply And.intro
    -- True on the right can always be proven directly.
    apply True.intro
    -- One of the premise coincides with the conclusion.
    exact h2
  case inr h7 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Conjunctions on the right can always be decomposed.
    apply And.intro
    -- True on the right can always be proven directly.
    apply True.intro
    -- One of the premise coincides with the conclusion.
    exact h2
  -- Implications on the right can always be decomposed.
  intro h8
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_117674564028732055831831444814 : ((p3 ∧ (((p5 → (((p2 → True) ∨ p3) → False)) ∧ (p5 ∨ p5)) ∨ (((True → (p3 ∨ p5)) ∧ (False ∨ p1)) ∨ (p4 → p3)))) ∨ (False → False)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_180066667497759459564401766077 : (((False → (False → (p3 → ((((p5 → p4) → p2) → p2) ∨ p1)))) ∨ True) → (p5 ∨ ((p4 → ((False ∨ p4) → ((p1 ∨ p1) ∨ p4))) ∨ p5))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h2 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Implications on the right can always be decomposed.
    intro h3
    -- Implications on the right can always be decomposed.
    intro h4
    -- Disjunctions on the left can always be decomposed.
    cases h4
    case inl h5 =>
      -- False on the left can always be used.
      apply False.elim h5
    case inr h6 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- One of the premise coincides with the conclusion.
      exact h3
  case inr h7 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Implications on the right can always be decomposed.
    intro h8
    -- Implications on the right can always be decomposed.
    intro h9
    -- Disjunctions on the left can always be decomposed.
    cases h9
    case inl h10 =>
      -- False on the left can always be used.
      apply False.elim h10
    case inr h11 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- One of the premise coincides with the conclusion.
      exact h8



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_347097862593262833656272843729 : (p3 → ((((((p5 ∧ (p2 ∨ p4)) ∨ p3) ∧ ((p2 ∨ p1) ∨ p1)) → False) ∨ False) ∨ ((p4 → ((((p3 ∧ True) ∨ p2) → p3) → p4)) ∨ p1))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h2
  -- Implications on the right can always be decomposed.
  intro h3
  -- One of the premise coincides with the conclusion.
  exact h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_303919891820961218468554525567 : (p1 ∨ (((((p1 ∧ p3) ∧ (p3 → (p1 → (p3 ∨ p5)))) ∧ p2) ∨ (((p4 ∨ (p1 ∨ True)) → ((p2 → p3) → (p3 ∧ False))) ∨ False)) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



