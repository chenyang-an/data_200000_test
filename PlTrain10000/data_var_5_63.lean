variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_53759103762352384319186293381 : ((((False ∧ ((p1 → ((p3 ∨ True) ∧ p4)) → p1)) ∧ p1) ∨ (p5 → ((False ∧ p2) → ((p5 ∨ p3) → (p1 ∧ ((p5 → p2) ∧ p2)))))) ∨ False) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
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
    -- Conjunctions on the left can always be decomposed.
    let h5 := h2.left
    let h6 := h2.right
    -- False on the left can always be used.
    apply False.elim h5
  case inr h7 =>
    -- Conjunctions on the left can always be decomposed.
    let h8 := h2.left
    let h9 := h2.right
    -- False on the left can always be used.
    apply False.elim h8
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h10
  -- Disjunctions on the left can always be decomposed.
  cases h3
  case inl h11 =>
    -- Conjunctions on the left can always be decomposed.
    let h12 := h2.left
    let h13 := h2.right
    -- False on the left can always be used.
    apply False.elim h12
  case inr h14 =>
    -- Conjunctions on the left can always be decomposed.
    let h15 := h2.left
    let h16 := h2.right
    -- False on the left can always be used.
    apply False.elim h15
  -- Disjunctions on the left can always be decomposed.
  cases h3
  case inl h17 =>
    -- Conjunctions on the left can always be decomposed.
    let h18 := h2.left
    let h19 := h2.right
    -- False on the left can always be used.
    apply False.elim h18
  case inr h20 =>
    -- Conjunctions on the left can always be decomposed.
    let h21 := h2.left
    let h22 := h2.right
    -- False on the left can always be used.
    apply False.elim h21



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_43989070350903268685859322607 : (((((((True ∨ (p5 → ((p2 ∨ True) → False))) ∧ (p5 ∧ p3)) → ((p4 ∧ (p3 → p5)) ∨ (False ∧ p2))) ∨ True) → (p4 ∧ p5)) → p1) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_773483123831443595774695196342 : (((False ∨ ((((((p3 → (p2 ∧ p3)) ∨ (p5 ∧ (p2 ∨ (p3 ∧ p2)))) ∨ (((False ∧ False) → False) ∧ p3)) ∨ False) ∧ (p1 ∨ p4)) ∨ True)) ∨ p1) ∧ True) := by
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
theorem thm_5_vars_324545820403566943038872757566 : (p5 ∨ (((False ∨ p4) → (p3 ∧ p1)) → ((False ∨ (((True ∨ (p1 ∧ (True ∧ (p3 ∨ p5)))) ∨ p5) ∨ True)) → (p3 → (p4 ∨ (p3 ∨ p4)))))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Implications on the right can always be decomposed.
  intro h3
  -- Disjunctions on the left can always be decomposed.
  cases h2
  case inl h4 =>
    -- False on the left can always be used.
    apply False.elim h4
  case inr h5 =>
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
          -- Show the left disjunct based on <expert-advice>.
          apply Or.inl
          -- One of the premise coincides with the conclusion.
          exact h3
        case inr h9 =>
          -- Conjunctions on the left can always be decomposed.
          let h10 := h9.left
          let h11 := h9.right
          -- Conjunctions on the left can always be decomposed.
          let h12 := h11.left
          let h13 := h11.right
          -- Disjunctions on the left can always be decomposed.
          cases h13
          case inl h14 =>
            -- Show the right disjunct based on <expert-advice>.
            apply Or.inr
            -- Show the left disjunct based on <expert-advice>.
            apply Or.inl
            -- One of the premise coincides with the conclusion.
            exact h14
          case inr h15 =>
            -- Show the right disjunct based on <expert-advice>.
            apply Or.inr
            -- Show the left disjunct based on <expert-advice>.
            apply Or.inl
            -- One of the premise coincides with the conclusion.
            exact h3
      case inr h16 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- One of the premise coincides with the conclusion.
        exact h3
    case inr h17 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- One of the premise coincides with the conclusion.
      exact h3



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_201322683818728350490474477146 : ((p5 → ((((p1 ∨ p4) ∧ p5) → p2) ∨ p4)) → ((p1 → (p3 → ((p1 ∧ (((p2 ∨ ((p4 ∨ True) ∨ p4)) ∨ p3) ∧ p2)) ∨ p1))) ∧ True)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h2
  -- Implications on the right can always be decomposed.
  intro h3
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h2
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_136229045018822297970597169097 : (((((False ∧ False) ∨ False) ∧ (p3 ∨ p3)) ∨ ((((True ∧ False) ∧ (p2 ∨ p2)) ∨ (True ∧ ((False ∨ False) ∨ p1))) ∨ True)) ∨ ((False → p3) ∧ p5)) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_230550830289312931817831452739 : (((False → p4) ∧ p1) → (((p3 ∧ (False ∨ p2)) ∨ (p1 → True)) ∧ (((p1 → p2) ∨ (p1 ∨ ((p3 ∨ True) ∨ ((False ∨ p5) ∨ p4)))) ∨ p5))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h4
  -- True on the right can always be proven directly.
  apply True.intro
  -- Conjunctions on the left can always be decomposed.
  let h5 := h1.left
  let h6 := h1.right
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- One of the premise coincides with the conclusion.
  exact h6



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_158434653885785324313964946215 : (((False ∨ p5) ∨ (p2 ∨ (p5 ∧ (((p1 ∧ ((True ∧ p4) → p4)) ∨ ((p4 → p3) → p1)) → False)))) ∨ (True ∨ (p4 → (False ∨ (False ∧ p1))))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_667911944311801646196994456944 : ((((p2 ∨ ((((p2 ∨ (p5 → p4)) ∧ (((False → p3) ∧ p4) → False)) ∧ (False → p5)) ∨ ((p4 ∧ False) ∧ False))) ∧ ((p2 ∧ p2) ∨ p4)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_350004651417943166999243242484 : (p4 → (((p3 ∧ (((p2 ∨ ((((False ∧ False) ∨ ((True ∧ False) ∧ p5)) ∧ p1) ∨ p4)) ∧ True) ∧ (((p5 → p2) → p4) ∧ p5))) ∨ p3) ∨ p4)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_317829392497179270707390823614 : (p4 ∨ ((((p1 → p2) ∧ p5) ∧ (p5 ∧ (((((p2 ∧ p5) ∧ p4) ∧ (False ∨ True)) ∧ ((p3 → True) ∨ (p3 → p3))) ∨ (p4 ∨ False)))) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_63346601087003515739824428650 : ((p5 ∧ (False ∧ (((p2 → p3) ∨ (p5 ∧ p2)) → ((((p5 ∧ ((p4 ∨ p5) ∧ p5)) → p1) → False) ∧ (((True ∧ p2) ∨ p4) → p4))))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_135301479600886082968536884431 : ((((((((False → (p4 → p5)) → p3) ∧ False) ∨ p3) ∧ (((p4 ∧ p2) ∧ p3) ∧ True)) ∨ True) ∧ (p4 ∨ (p4 ∨ p3))) ∨ (p3 → (True ∨ p4))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_42690241758147664073680742476 : (((p5 ∨ ((((((p5 → (p1 ∧ p5)) ∨ (p4 → ((p2 → ((True ∨ p2) ∧ p1)) ∨ p3))) → (p5 → p4)) ∧ True) ∨ p2) → p4)) ∨ True) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_244879447699400248154520812105 : ((p1 ∧ p2) ∨ ((((((p4 → (True → p2)) ∧ (p4 → p3)) ∨ p3) ∨ p4) ∧ p1) → (p3 ∨ ((((True ∧ (p3 ∧ True)) → p5) ∨ False) → p1)))) := by
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
    -- Disjunctions on the left can always be decomposed.
    cases h4
    case inl h5 =>
      -- Conjunctions on the left can always be decomposed.
      let h6 := h5.left
      let h7 := h5.right
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Implications on the right can always be decomposed.
      intro h8
      -- Disjunctions on the left can always be decomposed.
      cases h8
      case inl h9 =>
        -- One of the premise coincides with the conclusion.
        exact h3
      case inr h10 =>
        -- False on the left can always be used.
        apply False.elim h10
    case inr h11 =>
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- One of the premise coincides with the conclusion.
      exact h11
  case inr h12 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h13
    -- Disjunctions on the left can always be decomposed.
    cases h13
    case inl h14 =>
      -- One of the premise coincides with the conclusion.
      exact h3
    case inr h15 =>
      -- False on the left can always be used.
      apply False.elim h15



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_206102346850677397554651549269 : ((p4 ∧ (((p1 ∧ True) ∨ True) ∧ False)) ∨ (((p2 ∧ True) ∨ (((p1 → (p2 → p4)) ∧ ((p1 ∨ (False → False)) ∨ (p3 ∨ p4))) ∧ p2)) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_179365149586463323350169369687 : ((p2 ∨ (((p4 ∨ p5) ∧ (False ∨ False)) ∨ (((p1 ∨ p3) ∧ p2) → p2))) ∨ (((((False ∧ p5) → True) ∧ p2) ∧ p2) ∧ (p3 ∧ (p1 ∧ p3)))) := by
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



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_962417802969303733348421956264 : ((((True → False) ∧ ((p3 ∨ p2) ∨ ((((((p1 → p2) ∧ p3) ∧ p2) → (p2 → ((False ∨ p1) → ((p1 ∧ p4) ∨ p2)))) ∧ p2) → p4))) → p2) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
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
      -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
      have h6 : True := by
        -- True on the right can always be proven directly.
        apply True.intro
      -- We have shown the premise of h2, we can now drive its conclusion.
      let h7 := h2 h6
      -- False on the left can always be used.
      apply False.elim h7
    case inr h8 =>
      -- One of the premise coincides with the conclusion.
      exact h8
  case inr h9 =>
    -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
    have h10 : True := by
      -- True on the right can always be proven directly.
      apply True.intro
    -- We have shown the premise of h2, we can now drive its conclusion.
    let h11 := h2 h10
    -- False on the left can always be used.
    apply False.elim h11
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_217635686689136022425657413809 : ((((p3 ∧ p1) → p5) → p3) → (p1 ∨ (p4 ∨ ((((p4 ∧ p2) ∨ ((p4 ∨ True) → p2)) ∧ ((False → False) ∨ (p4 ∧ False))) ∨ (True ∨ p3))))) := by
  -- Implications on the right can always be decomposed.
  intro h1
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
theorem thm_5_vars_258702248828730218394059823712 : ((True → True) → ((((True → ((p5 → False) ∧ (((((True → False) ∨ p2) ∨ p1) → p1) ∧ True))) ∨ ((True ∨ (p2 → p4)) ∨ p3)) ∨ p3) ∨ p2)) := by
  -- Implications on the right can always be decomposed.
  intro h1
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



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_159821869935973452944782905317 : (((p1 ∨ (p5 ∨ (((((True → p2) ∨ True) → p1) ∧ (p2 → p5)) ∨ ((p2 ∧ p4) → False)))) ∨ p5) → (p4 ∨ ((p3 ∧ p2) → (p1 → p2)))) := by
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
      -- Implications on the right can always be decomposed.
      intro h5
      -- Conjunctions on the left can always be decomposed.
      let h6 := h4.left
      let h7 := h4.right
      -- One of the premise coincides with the conclusion.
      exact h7
    case inr h8 =>
      -- Disjunctions on the left can always be decomposed.
      cases h8
      case inl h9 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- Implications on the right can always be decomposed.
        intro h10
        -- Implications on the right can always be decomposed.
        intro h11
        -- Conjunctions on the left can always be decomposed.
        let h12 := h10.left
        let h13 := h10.right
        -- One of the premise coincides with the conclusion.
        exact h13
      case inr h14 =>
        -- Disjunctions on the left can always be decomposed.
        cases h14
        case inl h15 =>
          -- Conjunctions on the left can always be decomposed.
          let h16 := h15.left
          let h17 := h15.right
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- Implications on the right can always be decomposed.
          intro h18
          -- Implications on the right can always be decomposed.
          intro h19
          -- Conjunctions on the left can always be decomposed.
          let h20 := h18.left
          let h21 := h18.right
          -- One of the premise coincides with the conclusion.
          exact h21
        case inr h22 =>
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- Implications on the right can always be decomposed.
          intro h23
          -- Implications on the right can always be decomposed.
          intro h24
          -- Conjunctions on the left can always be decomposed.
          let h25 := h23.left
          let h26 := h23.right
          -- One of the premise coincides with the conclusion.
          exact h26
  case inr h27 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h28
    -- Implications on the right can always be decomposed.
    intro h29
    -- Conjunctions on the left can always be decomposed.
    let h30 := h28.left
    let h31 := h28.right
    -- One of the premise coincides with the conclusion.
    exact h31



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_40773644878376612445559382471 : ((((True ∧ ((p2 → p1) ∨ (((((False ∨ ((p5 ∨ (p1 ∧ p3)) ∧ p5)) ∧ (False → p2)) ∨ (p1 ∨ p4)) ∧ p3) → True))) → False) ∨ True) ∨ p5) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_116054305246920081066512433800 : (((p4 → (p2 ∨ (p1 → p3))) → (p2 ∧ (((p3 → ((p5 ∨ p1) ∧ ((p3 → False) → p2))) ∨ (p5 ∧ (p3 ∧ p1))) ∨ p4))) ∨ (p4 → True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_48876364907824192661561250850 : (((True → ((p4 → p3) ∧ (((p3 ∧ (False → (p4 ∨ p1))) → (True ∧ p1)) → ((p5 ∨ (p3 ∨ p1)) ∨ p4)))) ∧ (p2 ∨ (p5 ∨ p1))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_111622659550626833763087117920 : ((((((p4 → (True → False)) ∨ (((True → p4) → p3) → (True ∧ (False ∧ (p3 → (p4 ∨ p1)))))) ∧ (p3 → p5)) ∨ p2) ∨ p1) ∨ (False → False)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_47185549541249489763880694984 : (((((False ∧ (p3 ∨ ((False ∧ False) → (p2 → p2)))) ∧ (p3 ∨ False)) ∧ (True ∧ (p2 → (p3 ∨ (True → (p5 ∨ p3)))))) ∨ (True ∨ True)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_62425295427030967789471418123 : ((p3 ∧ ((p2 ∧ ((p1 ∧ p5) → p1)) ∧ ((p3 ∨ p3) → (True ∧ (((((p5 ∧ False) ∨ p3) ∧ (False ∨ False)) ∧ (p5 ∧ False)) ∧ True))))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_313019979488699316135138411372 : (p3 ∨ (((p2 ∧ (p1 ∨ (True → (p3 ∧ (p4 ∨ (p2 ∧ (False ∧ ((((p2 ∨ True) ∨ p4) ∧ ((False ∨ p3) → p2)) ∧ False)))))))) ∨ False) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_208282732076608596475455519275 : (((p1 ∨ p3) ∧ (False → (p3 ∨ p1))) → (p4 ∨ (p5 → (p5 ∧ ((((p1 → ((True → (True ∧ p1)) ∧ (p4 ∧ p3))) ∧ True) → p3) ∨ p2))))) := by
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
    -- Conjunctions on the right can always be decomposed.
    apply And.intro
    -- One of the premise coincides with the conclusion.
    exact h5
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Implications on the right can always be decomposed.
    intro h6
    -- Conjunctions on the left can always be decomposed.
    let h7 := h6.left
    let h8 := h6.right
    -- We want to use the implication h7 based on <expert-advice>. So we show its premise.
    have h9 : p1 := by
      -- One of the premise coincides with the conclusion.
      exact h4
    -- We have shown the premise of h7, we can now drive its conclusion.
    let h10 := h7 h9
    -- We need to get the right conjuct of h10 based on <expert-advice>.
    let h11 := h10.right
    -- We need to get the right conjuct of h11 based on <expert-advice>.
    let h12 := h11.right
    -- One of the premise coincides with the conclusion.
    exact h12
  case inr h13 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h14
    -- Conjunctions on the right can always be decomposed.
    apply And.intro
    -- One of the premise coincides with the conclusion.
    exact h14
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Implications on the right can always be decomposed.
    intro h15
    -- Conjunctions on the left can always be decomposed.
    let h16 := h15.left
    let h17 := h15.right
    -- One of the premise coincides with the conclusion.
    exact h13



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_147331835043856517967626890771 : ((((((p2 → p4) ∨ ((p2 ∧ p4) ∧ (p3 ∨ (p2 ∨ ((False ∧ False) ∧ True))))) ∨ True) ∨ (p3 → p3)) ∨ False) ∨ ((p3 ∨ False) ∧ (p5 ∧ True))) := by
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
theorem thm_5_vars_354811801278318274941469110146 : (p5 → (((True ∨ ((p4 ∨ p1) → True)) → (p2 ∨ ((p5 ∧ (p1 ∨ ((p3 ∧ (p5 ∨ p2)) ∧ p2))) ∨ (False ∨ ((p5 ∧ p3) ∨ p2))))) ∨ True)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_639331733206536388003909711501 : ((((((p4 ∨ p4) ∧ (p3 ∧ False)) → (p1 ∨ (((False ∧ (p2 → p2)) → p2) ∨ (p1 ∧ (((p5 ∧ p5) → (p1 ∨ p5)) ∨ p4))))) → False) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_179092809888497453525530275301 : ((False ∧ ((p2 ∨ (False ∨ ((True ∧ ((p1 ∨ False) ∨ p1)) ∨ p5))) ∨ p5)) ∨ (p4 → (((p5 ∨ False) ∧ (p1 ∧ p4)) → (p1 → (True ∧ True))))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Implications on the right can always be decomposed.
  intro h3
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_218041098542422800632014784113 : (((p2 ∨ False) ∧ (p1 → p5)) → (p2 → (((p4 → (((p4 ∨ ((p4 ∨ (p5 ∧ (p1 → False))) → (False ∨ p5))) ∧ True) ∧ p4)) → p4) ∨ True))) := by
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
    -- False on the left can always be used.
    apply False.elim h6



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_46343865559525070300620931335 : ((((((p4 → False) ∨ (True ∧ ((p4 ∨ ((False ∧ False) ∨ False)) → p4))) → p5) ∨ (p2 → (p4 → ((True → p4) ∨ p4)))) ∧ (True ∨ True)) ∨ p1) := by
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
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h2
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_44391028222468844006369725481 : ((((((p1 ∨ p3) → False) → (p2 → ((p1 → True) → ((p2 ∧ False) ∧ p4)))) ∨ (p5 ∧ (False → (((p1 ∧ p5) ∨ p2) ∧ p1)))) → p2) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_197553245754642226116215866140 : (((((p1 ∨ True) → p4) → p3) ∨ (p2 → p3)) ∨ (((p4 ∨ p5) → p1) ∨ ((p3 ∧ (((p5 ∨ (False → (p3 ∧ False))) → p4) ∨ p2)) → p3))) := by
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
  cases h3
  case inl h4 =>
    -- One of the premise coincides with the conclusion.
    exact h2
  case inr h5 =>
    -- One of the premise coincides with the conclusion.
    exact h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_134216886177708687467496038851 : ((((((p2 → p1) ∧ (False ∨ False)) ∧ p1) ∧ (((p3 ∧ (p5 ∧ p3)) → ((p1 ∨ (True ∨ p4)) ∨ True)) → p4)) ∨ True) ∨ ((p2 ∨ p5) ∧ p4)) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_232917836743033895793776347051 : ((p3 ∧ (p5 ∧ p1)) → ((((p2 ∧ (p3 ∧ False)) ∧ ((p2 → p4) → ((p3 ∨ p4) ∧ (p5 ∧ p2)))) ∨ (p1 ∧ ((p1 ∨ p2) ∨ True))) ∨ True)) := by
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
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_134540556345984371618322154287 : (((((((p3 ∨ (True ∨ p5)) ∧ (((p5 → True) ∨ p2) ∧ (p3 ∨ p2))) ∨ p5) → ((False ∨ p2) ∧ p2)) → False) → p2) ∨ (p2 → (p2 → True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_742339114494022836344569203482 : ((((p1 → p3) ∨ ((True → (((p4 → p5) ∨ p2) ∧ p2)) → ((True ∧ ((((p5 → (False → False)) ∧ True) ∨ p3) ∧ p2)) ∨ (p5 ∨ p3)))) ∨ p1) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
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
  -- We need to get the right conjuct of h3 based on <expert-advice>.
  let h4 := h3.right
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h5
  -- Implications on the right can always be decomposed.
  intro h6
  -- False on the left can always be used.
  apply False.elim h6
  -- True on the right can always be proven directly.
  apply True.intro
  -- One of the premise coincides with the conclusion.
  exact h4
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_38646087298972254049710497974 : (((((False → (True ∨ (p5 → (p2 ∨ p3)))) ∨ True) → (p3 ∨ (((p5 ∨ p5) ∨ ((True → False) ∨ ((p4 → p4) → p3))) ∨ p1))) ∧ p2) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_163018118980805009116288569245 : (((((((p2 → p4) ∨ False) ∧ p1) ∨ ((False ∨ p3) ∨ p3)) → p5) ∨ ((p1 ∨ True) ∨ p5)) ∧ ((p1 → (p1 ∧ False)) ∨ (False ∨ (p5 ∨ True)))) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_662903550288091649712142713676 : ((((((p2 ∨ False) ∨ p3) ∨ ((p1 → p4) → ((p3 → ((p2 ∨ p4) ∨ (((p3 ∨ True) → (p5 ∧ p4)) ∨ p1))) ∧ p2))) → (p2 ∧ p5)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_197716402977724841625370678305 : ((((p2 ∨ p2) ∧ p3) ∧ (p1 → (p2 ∧ False))) ∨ ((p3 → (True ∧ p2)) → (((p1 ∨ p2) → ((True ∨ False) ∨ (p4 ∨ (True → False)))) ∨ p1))) := by
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
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- True on the right can always be proven directly.
    apply True.intro
  case inr h4 =>
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- True on the right can always be proven directly.
    apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_670441042382035244300846076680 : (((((True ∧ p4) ∧ (p1 → (p3 ∧ (((p5 ∧ p1) ∧ (((p2 ∨ p3) ∧ (True ∨ (True ∧ False))) → p1)) → False)))) ∨ (True → (p5 → True))) ∨ p4) ∧ True) := by
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
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_318851993171567894408347958320 : (p4 ∨ (((((((p2 ∧ (True → (p3 → p1))) → True) → p3) → (((p4 ∧ p5) ∧ p4) ∨ True)) ∧ (False ∨ p3)) ∨ True) ∨ (p1 → (p3 ∨ p3)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_177690887516179053216519721708 : ((((((p4 ∨ p1) ∨ p5) ∨ (True ∨ (False ∨ p1))) ∧ (p5 ∧ p5)) ∧ p4) ∨ ((False ∧ (p4 → (((True ∧ (p5 → True)) ∨ p2) → p4))) → p4)) := by
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
theorem thm_5_vars_175245296226535678247037051833 : ((p1 ∨ (p2 → (((p2 → p4) → (p1 ∧ p4)) → (((p2 ∨ p2) ∨ p2) → p5)))) → ((p2 ∧ p4) ∨ (True ∨ ((p5 → (False ∨ False)) → False)))) := by
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
theorem thm_5_vars_14705839433431345876667541047 : (((((p4 ∨ p4) ∧ (((((p2 → ((p4 → True) → p2)) ∧ p3) ∧ p5) → (p1 ∧ False)) ∨ (p4 ∨ p2))) ∨ (p4 → True)) ∨ (False → p3)) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_153293439032512115317407045717 : ((p1 ∨ ((((((p5 → (((p5 ∧ ((False → True) → p5)) ∨ p2) ∨ p1)) ∨ p3) ∧ True) ∨ p5) → p5) → False)) → ((p3 → False) ∨ (False ∨ True))) := by
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
theorem thm_5_vars_56840854741755502141666165202 : ((((p5 → p1) → p5) ∧ (p4 → (((p4 ∧ False) ∨ p2) ∨ ((((((True → p1) → False) → p5) ∧ ((p1 → p1) ∧ p1)) ∧ p4) ∧ p5)))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_717872349023995068075314480170 : (((((True ∨ (p1 ∨ p5)) ∧ p4) ∨ (p1 ∨ ((p2 ∧ ((True → (p2 → False)) ∧ (p4 → ((True → (True → True)) ∨ p4)))) → (True → p1)))) ∨ p1) ∧ True) := by
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
  -- Implications on the right can always be decomposed.
  intro h2
  -- Conjunctions on the left can always be decomposed.
  let h3 := h1.left
  let h4 := h1.right
  -- Conjunctions on the left can always be decomposed.
  let h5 := h4.left
  let h6 := h4.right
  -- We want to use the implication h5 based on <expert-advice>. So we show its premise.
  have h7 : True := by
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h5, we can now drive its conclusion.
  let h8 := h5 h7
  -- We want to use the implication h8 based on <expert-advice>. So we show its premise.
  have h9 : p2 := by
    -- One of the premise coincides with the conclusion.
    exact h3
  -- We have shown the premise of h8, we can now drive its conclusion.
  let h10 := h8 h9
  -- False on the left can always be used.
  apply False.elim h10
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_721582775123222128753130207707 : ((((p4 ∧ (True → (False ∧ p5))) → ((p3 ∨ (p2 ∨ (p5 → (False → True)))) ∧ (False ∨ ((True ∨ (p1 ∨ (False → (False → p3)))) ∧ p2)))) ∨ p1) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- We want to use the implication h3 based on <expert-advice>. So we show its premise.
  have h4 : True := by
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h3, we can now drive its conclusion.
  let h5 := h3 h4
  -- We need to get the left conjuct of h5 based on <expert-advice>.
  let h6 := h5.left
  -- False on the left can always be used.
  apply False.elim h6
  -- Conjunctions on the left can always be decomposed.
  let h7 := h1.left
  let h8 := h1.right
  -- We want to use the implication h8 based on <expert-advice>. So we show its premise.
  have h9 : True := by
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h8, we can now drive its conclusion.
  let h10 := h8 h9
  -- We need to get the left conjuct of h10 based on <expert-advice>.
  let h11 := h10.left
  -- False on the left can always be used.
  apply False.elim h11
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_112341451219457892226036325944 : (((p5 → ((((p5 ∧ (False ∧ p1)) → (False ∧ (p1 ∨ ((False → (p5 ∨ (p3 ∨ True))) → p2)))) ∧ p3) ∨ (False ∧ p4))) ∨ p4) ∨ (p1 ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_150005672948852995862050239679 : ((p5 ∨ (((True ∧ ((p5 ∨ p1) ∧ True)) ∧ ((False ∧ p3) ∧ (True ∧ (p5 → (p4 → (p5 → p4)))))) ∨ False)) ∨ ((p5 → (False → p2)) ∧ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- False on the left can always be used.
  apply False.elim h2
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_232732978653579684510536995227 : ((p1 ∧ (False → p2)) → (((((p4 ∨ (p1 ∨ ((((((False ∨ (False ∨ p3)) → p1) ∨ False) → p5) ∧ p2) → p3))) → p5) → p4) ∨ p1) ∧ True)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h2
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_337903015704860295241585501373 : (p1 → ((p1 ∨ ((p5 → ((p4 ∧ True) ∨ (p5 ∨ (False ∧ (p3 ∨ p4))))) → p1)) → ((p1 → (((p5 → (False → True)) ∧ p2) ∧ False)) → p2))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Implications on the right can always be decomposed.
  intro h3
  -- Disjunctions on the left can always be decomposed.
  cases h2
  case inl h4 =>
    -- We want to use the implication h3 based on <expert-advice>. So we show its premise.
    have h5 : p1 := by
      -- One of the premise coincides with the conclusion.
      exact h1
    -- We have shown the premise of h3, we can now drive its conclusion.
    let h6 := h3 h5
    -- We need to get the left conjuct of h6 based on <expert-advice>.
    let h7 := h6.left
    -- We need to get the right conjuct of h7 based on <expert-advice>.
    let h8 := h7.right
    -- One of the premise coincides with the conclusion.
    exact h8
  case inr h9 =>
    -- We want to use the implication h3 based on <expert-advice>. So we show its premise.
    have h10 : p1 := by
      -- One of the premise coincides with the conclusion.
      exact h1
    -- We have shown the premise of h3, we can now drive its conclusion.
    let h11 := h3 h10
    -- We need to get the left conjuct of h11 based on <expert-advice>.
    let h12 := h11.left
    -- We need to get the right conjuct of h12 based on <expert-advice>.
    let h13 := h12.right
    -- One of the premise coincides with the conclusion.
    exact h13



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_184052775364394462990688657860 : (((((p5 ∧ ((p4 ∧ p3) ∧ p5)) ∧ True) ∨ (p1 ∨ p4)) ∨ p3) ∨ ((p5 → p3) ∨ ((False ∧ (p4 → (p1 ∧ ((p5 ∧ True) ∧ p3)))) → True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_154329627637020093350223309988 : (((p2 ∨ ((((p1 → p2) ∧ (True ∨ False)) ∨ p2) ∧ (p5 ∨ (p4 ∨ (p4 ∧ (p1 ∧ True)))))) ∨ True) ∧ (False → ((False ∨ p1) ∧ (True ∨ p4)))) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- False on the left can always be used.
  apply False.elim h1
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_41443717294887109031382792024 : ((((p4 ∨ (((p5 ∨ (p1 ∧ (((p1 → p4) ∨ True) ∧ p5))) ∧ p4) ∨ True)) → (p4 ∧ (p2 ∧ (((False ∨ True) ∧ p5) ∧ p3)))) ∨ True) ∨ p1) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_54720275214263272116915000162 : ((((p1 → (p1 ∧ (p4 ∨ p2))) → (p2 → p3)) → (((((False → p5) → (p4 → p4)) ∨ ((p2 → True) ∨ (p3 ∧ p3))) ∨ p1) → p3)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_634834522687211055985079206357 : ((((((True → ((p5 ∨ p4) ∨ True)) → ((False ∧ p4) ∧ (p5 → (((p1 ∧ (p1 → p1)) ∧ p2) ∨ p1)))) ∨ ((True ∨ p3) → True)) → p3) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_698252188746360874055419746477 : (((((p3 ∨ ((((p3 ∨ (p2 ∨ p2)) ∨ True) ∨ False) → True)) → p5) ∨ (True ∧ ((((((p2 → p5) → p5) → p1) ∧ p5) ∨ False) → p5))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_43779511473646125346817554977 : ((((False ∨ (p4 ∨ (((True ∧ p3) ∧ (p3 ∨ ((False ∨ (((False → p3) ∨ ((p1 → p5) ∧ p5)) ∨ p3)) ∨ True))) → False))) → p1) → p2) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_762058470576094106821783997130 : (((p3 ∧ (((p1 ∧ (((True → p3) ∧ True) → ((p2 ∨ p5) ∨ (((p1 ∧ p1) ∨ p4) ∧ (p5 ∨ (p4 → True)))))) ∧ False) ∧ (False ∨ p2))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_890544823275250541543496148 : ((p2 → (((((p4 ∧ p5) ∧ (p2 ∨ (p3 → ((False ∧ p4) ∨ (p4 ∨ False))))) ∨ p2) → (False ∨ (p5 ∨ (p1 → p4)))) → p5)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_345909119962464733391663509688 : (p3 → (((((p3 ∨ p2) → p5) ∧ ((p4 ∨ (True ∨ ((p4 ∨ (p5 ∨ p2)) ∧ p5))) → (p1 → p5))) ∧ (((p3 ∨ p2) ∨ p1) ∨ p5)) → p5)) := by
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
  -- Disjunctions on the left can always be decomposed.
  cases h4
  case inl h7 =>
    -- Disjunctions on the left can always be decomposed.
    cases h7
    case inl h8 =>
      -- Disjunctions on the left can always be decomposed.
      cases h8
      case inl h9 =>
        -- We want to use the implication h5 based on <expert-advice>. So we show its premise.
        have h10 : (p3 ∨ p2) := by
          -- Show the left disjunct based on <expert-advice>.
          apply Or.inl
          -- One of the premise coincides with the conclusion.
          exact h1
        -- We have shown the premise of h5, we can now drive its conclusion.
        let h11 := h5 h10
        -- One of the premise coincides with the conclusion.
        exact h11
      case inr h12 =>
        -- We want to use the implication h5 based on <expert-advice>. So we show its premise.
        have h13 : (p3 ∨ p2) := by
          -- Show the left disjunct based on <expert-advice>.
          apply Or.inl
          -- One of the premise coincides with the conclusion.
          exact h1
        -- We have shown the premise of h5, we can now drive its conclusion.
        let h14 := h5 h13
        -- One of the premise coincides with the conclusion.
        exact h14
    case inr h15 =>
      -- We want to use the implication h5 based on <expert-advice>. So we show its premise.
      have h16 : (p3 ∨ p2) := by
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- One of the premise coincides with the conclusion.
        exact h1
      -- We have shown the premise of h5, we can now drive its conclusion.
      let h17 := h5 h16
      -- One of the premise coincides with the conclusion.
      exact h17
  case inr h18 =>
    -- One of the premise coincides with the conclusion.
    exact h18



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_62565304098961374169177638808 : ((p3 ∧ (p5 ∨ (p1 ∨ (((False ∨ p3) ∨ (p2 → ((True ∧ False) → p3))) ∧ ((((p2 → True) ∨ (p3 ∧ p2)) ∨ (p5 ∧ p3)) → p4))))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_230479270992772759868452920088 : (((p5 ∨ p5) ∧ p3) → (((p2 ∨ ((True ∨ (p2 → p2)) ∧ ((p3 → p3) → p5))) → (p4 ∨ p2)) → ((((True → p4) → False) ∨ p5) ∧ p3))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Conjunctions on the left can always be decomposed.
  let h3 := h1.left
  let h4 := h1.right
  -- Disjunctions on the left can always be decomposed.
  cases h3
  case inl h5 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h5
  case inr h6 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h6
  -- Conjunctions on the left can always be decomposed.
  let h7 := h1.left
  let h8 := h1.right
  -- Disjunctions on the left can always be decomposed.
  cases h7
  case inl h9 =>
    -- One of the premise coincides with the conclusion.
    exact h8
  case inr h10 =>
    -- One of the premise coincides with the conclusion.
    exact h8



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_257184963823487785820168710062 : ((p2 ∨ p2) → (((p5 ∨ (p5 → ((((p4 ∨ p1) → (((p3 ∧ p2) ∨ p2) ∧ p1)) ∨ ((p5 → True) → True)) ∨ p1))) ∧ (p2 ∨ p3)) ∨ p2)) := by
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
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h3



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_64725159510220164984828399166 : ((p1 ∨ (p4 → (p2 → (((((p2 ∨ p3) → ((p1 ∧ p3) ∨ True)) → (((((p3 ∨ p5) ∨ p3) ∨ p1) → False) ∧ True)) → True) → p5)))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_157415798886498605820561185628 : ((((((True ∧ p3) ∨ p4) ∧ p4) ∧ ((p3 ∧ (True ∧ (p4 ∧ (p4 ∧ p5)))) ∧ False)) ∧ (p5 ∨ False)) ∨ (False ∨ (p1 → ((True → True) → True)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_51454696035705296789010488793 : ((((((((p4 ∧ (p5 ∨ True)) ∧ p2) → False) → p2) → (True ∧ p5)) → (p3 ∧ (p3 → p5))) → (((p4 ∧ p5) → p2) ∨ (p1 ∧ True))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_680372293159931451150281871899 : ((((((p3 ∧ (p5 ∨ p3)) ∧ (p2 ∧ ((p4 → p2) → ((p1 → p2) ∧ p1)))) → ((p1 → p3) ∨ p1)) → (False ∨ ((p3 ∧ p2) ∨ p2))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_222384370714449272580336511391 : (((p3 → p1) → True) ∧ ((True ∨ ((p2 ∨ (p2 ∧ ((p2 ∧ (((p1 ∨ p2) ∧ p1) → p1)) ∨ p1))) → p2)) → ((False ∨ (p5 ∨ p2)) ∨ True))) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro
  -- Implications on the right can always be decomposed.
  intro h2
  -- Disjunctions on the left can always be decomposed.
  cases h2
  case inl h3 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro
  case inr h4 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_323796541831671397418107041086 : (p5 ∨ ((((p3 → True) ∧ ((p5 ∧ p5) ∧ p3)) → ((((p4 → (True ∧ p5)) → False) ∨ p3) ∨ p4)) ∨ (True → (((p1 ∧ p5) ∨ p4) ∧ p5)))) := by
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
  let h4 := h3.left
  let h5 := h3.right
  -- Conjunctions on the left can always be decomposed.
  let h6 := h4.left
  let h7 := h4.right
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h5



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_340733334776775511563879590389 : (p2 → ((((((p4 ∨ p4) ∨ (((True ∧ p3) ∧ (False → p1)) → p4)) ∧ (p3 ∨ ((p1 → p5) → (True ∧ (p1 → p5))))) ∨ p2) ∨ p4) ∨ True)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_51801975971077572215937663681 : (((p2 ∨ ((p4 ∧ p3) ∨ ((False ∧ ((False ∨ True) ∧ (p1 → p2))) ∧ (p5 → False)))) ∧ ((((p4 ∨ p5) → (True ∧ False)) ∧ p4) → p4)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_2936356389267247108575530579 : (((p3 ∧ p5) ∨ p1) ∨ (p1 ∨ ((p1 → ((True ∧ p1) ∨ (p4 ∧ (True ∧ p1)))) ∧ (((((p3 → p4) ∧ p5) ∨ p1) ∧ p5) ∨ True)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- One of the premise coincides with the conclusion.
  exact h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_84106193741619499969589813556 : (((((True ∨ p1) ∨ p5) → ((p1 → p1) → (((p5 ∨ (p5 ∧ p5)) ∧ p1) ∧ p1))) ∧ ((p1 → p2) ∧ ((p3 ∨ p4) ∨ (False ∨ p3)))) → p1) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- Conjunctions on the left can always be decomposed.
  let h4 := h3.left
  let h5 := h3.right
  -- Disjunctions on the left can always be decomposed.
  cases h5
  case inl h6 =>
    -- Disjunctions on the left can always be decomposed.
    cases h6
    case inl h7 =>
      -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
      have h8 : ((True ∨ p1) ∨ p5) := by
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- True on the right can always be proven directly.
        apply True.intro
      -- We have shown the premise of h2, we can now drive its conclusion.
      let h9 := h2 h8
      -- We want to use the implication h9 based on <expert-advice>. So we show its premise.
      have h10 : (p1 → p1) := by
        -- Implications on the right can always be decomposed.
        intro h11
        -- One of the premise coincides with the conclusion.
        exact h11
      -- We have shown the premise of h9, we can now drive its conclusion.
      let h12 := h9 h10
      -- We need to get the right conjuct of h12 based on <expert-advice>.
      let h13 := h12.right
      -- One of the premise coincides with the conclusion.
      exact h13
    case inr h14 =>
      -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
      have h15 : ((True ∨ p1) ∨ p5) := by
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- True on the right can always be proven directly.
        apply True.intro
      -- We have shown the premise of h2, we can now drive its conclusion.
      let h16 := h2 h15
      -- We want to use the implication h16 based on <expert-advice>. So we show its premise.
      have h17 : (p1 → p1) := by
        -- Implications on the right can always be decomposed.
        intro h18
        -- One of the premise coincides with the conclusion.
        exact h18
      -- We have shown the premise of h16, we can now drive its conclusion.
      let h19 := h16 h17
      -- We need to get the right conjuct of h19 based on <expert-advice>.
      let h20 := h19.right
      -- One of the premise coincides with the conclusion.
      exact h20
  case inr h21 =>
    -- Disjunctions on the left can always be decomposed.
    cases h21
    case inl h22 =>
      -- False on the left can always be used.
      apply False.elim h22
    case inr h23 =>
      -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
      have h24 : ((True ∨ p1) ∨ p5) := by
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- True on the right can always be proven directly.
        apply True.intro
      -- We have shown the premise of h2, we can now drive its conclusion.
      let h25 := h2 h24
      -- We want to use the implication h25 based on <expert-advice>. So we show its premise.
      have h26 : (p1 → p1) := by
        -- Implications on the right can always be decomposed.
        intro h27
        -- One of the premise coincides with the conclusion.
        exact h27
      -- We have shown the premise of h25, we can now drive its conclusion.
      let h28 := h25 h26
      -- We need to get the right conjuct of h28 based on <expert-advice>.
      let h29 := h28.right
      -- One of the premise coincides with the conclusion.
      exact h29



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_325696688364611586509968005079 : (p5 ∨ (p1 ∨ ((p2 ∨ ((p3 ∧ p4) ∨ (False → ((True → p5) → p1)))) ∨ ((p1 → (p4 ∨ False)) ∨ ((False → p1) ∨ ((p1 → True) ∨ p1)))))) := by
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
  -- Implications on the right can always be decomposed.
  intro h1
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_811540271920113718986571330273 : (((p5 → (True → (((((p4 → ((False ∨ False) ∨ (False ∧ False))) ∧ (False ∨ (p1 ∨ p3))) ∨ p5) ∨ (p4 ∧ (p2 ∨ (p4 ∧ p1)))) ∧ p5))) ∨ p1) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h1
  -- One of the premise coincides with the conclusion.
  exact h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_44384403029032462515786802212 : (((((p5 → ((((((False ∧ False) → p2) → True) → p3) ∨ True) ∨ False)) → True) ∨ (p3 → (False ∨ (p1 → ((p3 ∧ p1) ∨ True))))) → p4) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_781740403855438576829440208650 : (((p2 ∨ (p4 ∨ (p3 → (((p2 ∧ ((p3 → p5) ∨ ((p1 → True) ∧ (True → (p3 → True))))) → ((p4 → p5) ∨ True)) ∨ (p2 → p3))))) ∨ p5) ∧ True) := by
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
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h2
  -- One of the premise coincides with the conclusion.
  exact h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_347278904396491629724595730365 : (p3 → ((((p3 ∨ (p5 → (p2 ∧ (p2 ∧ True)))) ∨ True) → False) ∨ (True → ((p5 → True) ∨ (((p2 → True) ∧ p3) ∨ ((p5 ∧ p1) → p4)))))) := by
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
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_134502365265648976401367449052 : ((((((p1 ∧ (True ∨ (p4 ∧ False))) ∨ p4) ∨ ((((p3 ∧ (p1 ∧ False)) → False) ∨ p2) ∧ (p3 → p2))) ∨ p4) → p1) ∨ ((False → p1) ∨ p3)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_192534877919038061864933607789 : (((p1 ∧ (((p3 → p4) ∧ (p5 → p5)) → p2)) ∨ True) → (False ∨ ((((True → p5) ∨ p5) ∨ ((True ∨ p4) ∧ p5)) ∨ ((p2 → True) ∨ True)))) := by
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
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro
  case inr h5 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_342932655481435771297843267545 : (p2 → ((((p1 → p1) ∨ True) → True) ∧ ((((((p1 ∧ p3) ∧ p1) → (p1 → (p2 ∧ True))) ∧ p2) → (True → p3)) ∨ ((True ∨ True) ∨ False)))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h2
  -- True on the right can always be proven directly.
  apply True.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_355609875681372349365445949818 : (p5 → (((p5 ∨ p1) → (p1 ∧ (p1 ∨ ((p2 → (p1 ∧ p1)) ∨ (((p3 ∧ p2) ∧ True) ∨ ((True ∨ True) → (p5 ∨ False))))))) ∨ (False → True))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h2
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_344317843566155804926336819192 : (p2 → (p3 ∨ (((p1 → p3) → p4) → (((False ∨ (((((p1 → p2) ∨ p5) ∧ p5) ∧ p1) ∧ p4)) ∨ ((False ∧ p2) ∨ (p2 ∧ True))) ∨ p2)))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h2
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_684003035276498580699499976148 : (((((((False ∨ (True ∧ False)) ∨ p4) ∨ ((p2 → p2) → (p3 ∨ (p4 ∨ (p1 → p2))))) → p3) ∨ ((p4 ∧ (p5 ∨ (p5 ∨ p5))) ∨ False)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_231069261278127024943851905237 : (((True ∨ p5) ∨ p2) → (True → (((p3 ∧ (p2 ∧ p1)) ∨ True) ∨ ((False ∧ (p4 ∧ False)) → ((p1 ∨ (p1 → p2)) ∨ ((p3 ∨ p4) ∨ True)))))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h3 =>
    -- Disjunctions on the left can always be decomposed.
    cases h3
    case inl h4 =>
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- True on the right can always be proven directly.
      apply True.intro
    case inr h5 =>
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



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_50712744235006872849421660474 : ((((p2 ∧ p1) ∨ ((False ∨ ((p5 ∨ (((p1 → p4) ∧ p1) → (p4 ∧ False))) ∧ (p3 → True))) ∧ p5)) → (((False ∧ p5) ∧ p1) ∨ True)) ∨ p5) := by
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
    -- True on the right can always be proven directly.
    apply True.intro
  case inr h5 =>
    -- Conjunctions on the left can always be decomposed.
    let h6 := h5.left
    let h7 := h5.right
    -- Disjunctions on the left can always be decomposed.
    cases h6
    case inl h8 =>
      -- False on the left can always be used.
      apply False.elim h8
    case inr h9 =>
      -- Conjunctions on the left can always be decomposed.
      let h10 := h9.left
      let h11 := h9.right
      -- Disjunctions on the left can always be decomposed.
      cases h10
      case inl h12 =>
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
theorem thm_5_vars_118700769802963685804982431203 : ((p5 ∨ ((((((((True ∨ p3) ∨ (p4 ∧ p5)) → p4) → ((p3 ∧ p2) ∨ (p5 ∧ True))) ∨ p5) ∧ (p2 ∧ p3)) ∧ p1) → False)) ∨ (p3 → True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_40133494476751291539453578097 : ((((((((p2 ∧ True) → ((p1 → p5) ∧ ((p4 ∧ p3) ∨ True))) → (p2 ∧ p5)) ∨ p5) ∧ (p4 ∨ ((p4 → p5) ∨ True))) ∧ p2) ∨ p3) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_165109104456751686907942393071 : (((p1 → (p5 ∨ ((p3 ∨ ((True → ((p2 → p2) ∧ p3)) → (True ∧ True))) ∧ p5))) → p1) ∨ ((p5 ∨ (p4 ∨ ((p3 → p2) ∨ p1))) → True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_780219666788042791268512404466 : (((p2 ∨ ((p1 ∨ (p4 → (((((True → True) → (p2 ∨ (p2 ∨ ((False ∧ p5) → p4)))) → False) → p2) ∨ p4))) ∨ (p2 ∧ (p5 ∧ p3)))) ∨ p4) ∧ True) := by
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
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_744761248656188599272012231880 : ((((p3 ∧ p2) → ((((p1 ∧ ((p3 ∨ (True ∨ (False ∧ False))) ∨ (((p1 ∧ p5) ∧ p3) ∧ p3))) → (p3 ∨ (p4 ∨ p4))) ∧ p1) ∨ p1)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_909643839383878509161596731197 : ((((p2 ∧ (((p2 ∧ p5) → p3) ∧ ((p1 ∨ (p3 ∧ p3)) → (((p2 → p3) ∨ False) ∧ p1)))) ∧ ((p2 ∨ (p4 → (p4 ∧ p1))) ∧ p1)) → p3) ∧ True) := by
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
  -- Disjunctions on the left can always be decomposed.
  cases h8
  case inl h10 =>
    -- We want to use the implication h7 based on <expert-advice>. So we show its premise.
    have h11 : (p1 ∨ (p3 ∧ p3)) := by
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- One of the premise coincides with the conclusion.
      exact h9
    -- We have shown the premise of h7, we can now drive its conclusion.
    let h12 := h7 h11
    -- We need to get the left conjuct of h12 based on <expert-advice>.
    let h13 := h12.left
    -- Disjunctions on the left can always be decomposed.
    cases h13
    case inl h14 =>
      -- We want to use the implication h14 based on <expert-advice>. So we show its premise.
      have h15 : p2 := by
        -- One of the premise coincides with the conclusion.
        exact h10
      -- We have shown the premise of h14, we can now drive its conclusion.
      let h16 := h14 h15
      -- One of the premise coincides with the conclusion.
      exact h16
    case inr h17 =>
      -- False on the left can always be used.
      apply False.elim h17
  case inr h18 =>
    -- We want to use the implication h7 based on <expert-advice>. So we show its premise.
    have h19 : (p1 ∨ (p3 ∧ p3)) := by
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- One of the premise coincides with the conclusion.
      exact h9
    -- We have shown the premise of h7, we can now drive its conclusion.
    let h20 := h7 h19
    -- We need to get the left conjuct of h20 based on <expert-advice>.
    let h21 := h20.left
    -- Disjunctions on the left can always be decomposed.
    cases h21
    case inl h22 =>
      -- We want to use the implication h22 based on <expert-advice>. So we show its premise.
      have h23 : p2 := by
        -- One of the premise coincides with the conclusion.
        exact h4
      -- We have shown the premise of h22, we can now drive its conclusion.
      let h24 := h22 h23
      -- One of the premise coincides with the conclusion.
      exact h24
    case inr h25 =>
      -- False on the left can always be used.
      apply False.elim h25
  -- True on the right can always be proven directly.
  apply True.intro



