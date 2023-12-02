variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_147818456087875894908052914008 : (((p5 ∧ (True ∧ ((p1 ∧ p3) → (((p4 ∨ (p5 ∧ (True ∧ p5))) ∨ p4) → (True ∨ (p2 ∧ p5)))))) → p1) ∨ ((True ∨ p5) ∨ (False → False))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_125077882869699737767807925469 : (((p1 ∨ (p3 ∧ p2)) ∧ ((((True ∨ p1) ∧ p3) → ((p5 → p2) ∧ (p1 ∧ ((False ∨ False) ∨ (p3 ∨ (p4 ∨ True)))))) ∨ p1)) → (p4 ∨ p1)) := by
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
      -- One of the premise coincides with the conclusion.
      exact h4
    case inr h6 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- One of the premise coincides with the conclusion.
      exact h6
  case inr h7 =>
    -- Conjunctions on the left can always be decomposed.
    let h8 := h7.left
    let h9 := h7.right
    -- Disjunctions on the left can always be decomposed.
    cases h3
    case inl h10 =>
      -- We want to use the implication h10 based on <expert-advice>. So we show its premise.
      have h11 : ((True ∨ p1) ∧ p3) := by
        -- Conjunctions on the right can always be decomposed.
        apply And.intro
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- True on the right can always be proven directly.
        apply True.intro
        -- One of the premise coincides with the conclusion.
        exact h8
      -- We have shown the premise of h10, we can now drive its conclusion.
      let h12 := h10 h11
      -- We need to get the right conjuct of h12 based on <expert-advice>.
      let h13 := h12.right
      -- We need to get the left conjuct of h13 based on <expert-advice>.
      let h14 := h13.left
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- One of the premise coincides with the conclusion.
      exact h14
    case inr h15 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- One of the premise coincides with the conclusion.
      exact h15



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_136357549030464692076673968928 : (((((p5 ∧ p4) ∨ False) ∧ p4) ∨ (((p5 ∨ ((((p1 ∧ False) → p4) ∧ False) → ((p2 ∨ p1) ∧ p4))) ∧ p4) ∧ p3)) ∨ (True ∨ (p5 → p3))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_37779201238137959534576006162 : (((((p1 → False) ∧ (p1 → ((p1 → p3) ∧ (p3 ∨ ((p3 → ((p2 ∧ (p1 ∨ (p3 ∨ p1))) ∨ (p4 ∨ True))) → p3))))) → p5) ∧ p2) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_315119093370512420885051113375 : (p3 ∨ ((((p1 ∨ p1) ∨ False) ∧ (False ∧ False)) ∨ ((p2 → True) ∨ ((((p4 → True) → p2) ∨ ((p5 ∧ p2) ∧ p2)) ∨ ((p3 → False) ∧ p4))))) := by
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
theorem thm_5_vars_314601059901992219267006893686 : (p3 ∨ ((p4 ∨ (((p5 ∨ False) ∨ p1) ∧ ((False ∨ ((p5 → p4) → p3)) ∨ (p3 → (p2 ∨ p2))))) → (p5 ∨ (True → (p2 ∨ (p2 → True)))))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
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
    -- True on the right can always be proven directly.
    apply True.intro
  case inr h5 =>
    -- Conjunctions on the left can always be decomposed.
    let h6 := h5.left
    let h7 := h5.right
    -- Disjunctions on the left can always be decomposed.
    cases h6
    case inl h8 =>
      -- Disjunctions on the left can always be decomposed.
      cases h8
      case inl h9 =>
        -- Disjunctions on the left can always be decomposed.
        cases h7
        case inl h10 =>
          -- Disjunctions on the left can always be decomposed.
          cases h10
          case inl h11 =>
            -- False on the left can always be used.
            apply False.elim h11
          case inr h12 =>
            -- Show the left disjunct based on <expert-advice>.
            apply Or.inl
            -- One of the premise coincides with the conclusion.
            exact h9
        case inr h13 =>
          -- Show the left disjunct based on <expert-advice>.
          apply Or.inl
          -- One of the premise coincides with the conclusion.
          exact h9
      case inr h14 =>
        -- False on the left can always be used.
        apply False.elim h14
    case inr h15 =>
      -- Disjunctions on the left can always be decomposed.
      cases h7
      case inl h16 =>
        -- Disjunctions on the left can always be decomposed.
        cases h16
        case inl h17 =>
          -- False on the left can always be used.
          apply False.elim h17
        case inr h18 =>
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- Implications on the right can always be decomposed.
          intro h19
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- Implications on the right can always be decomposed.
          intro h20
          -- True on the right can always be proven directly.
          apply True.intro
      case inr h21 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- Implications on the right can always be decomposed.
        intro h22
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- Implications on the right can always be decomposed.
        intro h23
        -- True on the right can always be proven directly.
        apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_229825927032081000607522313156 : ((p5 → (p1 ∧ p2)) ∨ ((((False → True) ∧ (p1 ∨ (((p5 → p2) → (p3 ∧ p3)) ∨ p2))) ∨ (((p5 ∧ p2) → False) ∨ (p1 → p1))) ∨ False)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
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
theorem thm_5_vars_459985157499376895682559036704 : ((((((False → p3) → p4) → (False ∧ (((False ∨ p3) → (p2 ∧ ((False ∨ p4) ∨ p1))) ∧ p5))) → (p3 ∨ (p5 → (p5 ∨ (p3 ∧ p3))))) ∧ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h2
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- One of the premise coincides with the conclusion.
  exact h2
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_198281674453803572169331682875 : ((False ∧ (False ∨ (p4 ∧ ((p1 → p1) ∧ True)))) ∨ (((True → ((True ∧ p1) ∨ p5)) ∧ ((((False ∧ True) ∨ (p5 ∧ p1)) ∨ False) → True)) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_145597209023638959483447163466 : ((((p5 ∧ p4) ∨ True) → (p4 → (((p5 → (False ∨ (p2 ∧ False))) ∨ ((p2 ∨ p2) ∨ p1)) ∨ (True → True)))) ∧ (((True → p1) ∧ p2) → True)) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
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
  -- Implications on the right can always be decomposed.
  intro h9
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_341258910690143215511069766306 : (p2 → ((((((((p1 ∨ (p1 → p4)) ∨ (p1 ∧ p4)) → True) → p5) → p4) → (((p2 → (p1 → False)) ∨ True) ∨ p2)) → (True ∧ False)) → False)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
  have h3 : ((((((p1 ∨ (p1 → p4)) ∨ (p1 ∧ p4)) → True) → p5) → p4) → (((p2 → (p1 → False)) ∨ True) ∨ p2)) := by
    -- Implications on the right can always be decomposed.
    intro h4
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h1
  -- We have shown the premise of h2, we can now drive its conclusion.
  let h5 := h2 h3
  -- We need to get the right conjuct of h5 based on <expert-advice>.
  let h6 := h5.right
  -- False on the left can always be used.
  apply False.elim h6



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_221850243860429404294606747810 : (((p3 ∧ p4) → True) ∧ (((p1 ∨ (((False ∨ p3) → p1) ∧ p4)) ∨ p4) ∨ (p3 ∨ (p3 → (p3 → (False → (p3 ∧ (p2 ∧ (p3 → True))))))))) := by
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
  -- Implications on the right can always be decomposed.
  intro h3
  -- Implications on the right can always be decomposed.
  intro h4
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- False on the left can always be used.
  apply False.elim h4
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- False on the left can always be used.
  apply False.elim h4
  -- Implications on the right can always be decomposed.
  intro h5
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_656081794788597802187646606306 : (((((p2 ∨ ((p5 ∧ p2) ∨ (p1 ∧ (((p3 ∨ False) ∨ p4) ∨ ((p3 → p4) ∨ p5))))) → (p4 ∨ (p3 ∨ (True ∨ False)))) ∨ (p2 ∧ p3)) ∨ p3) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
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
      -- Conjunctions on the left can always be decomposed.
      let h5 := h4.left
      let h6 := h4.right
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- True on the right can always be proven directly.
      apply True.intro
    case inr h7 =>
      -- Conjunctions on the left can always be decomposed.
      let h8 := h7.left
      let h9 := h7.right
      -- Disjunctions on the left can always be decomposed.
      cases h9
      case inl h10 =>
        -- Disjunctions on the left can always be decomposed.
        cases h10
        case inl h11 =>
          -- Disjunctions on the left can always be decomposed.
          cases h11
          case inl h12 =>
            -- Show the right disjunct based on <expert-advice>.
            apply Or.inr
            -- Show the left disjunct based on <expert-advice>.
            apply Or.inl
            -- One of the premise coincides with the conclusion.
            exact h12
          case inr h13 =>
            -- False on the left can always be used.
            apply False.elim h13
        case inr h14 =>
          -- Show the left disjunct based on <expert-advice>.
          apply Or.inl
          -- One of the premise coincides with the conclusion.
          exact h14
      case inr h15 =>
        -- Disjunctions on the left can always be decomposed.
        cases h15
        case inl h16 =>
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- Show the left disjunct based on <expert-advice>.
          apply Or.inl
          -- True on the right can always be proven directly.
          apply True.intro
        case inr h17 =>
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
theorem thm_5_vars_341715651383685518462109433298 : (p2 → (((((((False ∧ True) ∨ p4) → p1) ∧ (p1 → p1)) → p1) ∨ (p2 ∧ (((p3 → p1) ∨ (p5 ∧ (True → p5))) ∨ False))) ∨ (p3 → p3))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h2
  -- One of the premise coincides with the conclusion.
  exact h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_47402794386334145292948757294 : (((True ∧ ((p2 → p3) → (True ∧ (((p2 → p2) ∨ True) → (p1 ∨ (p3 ∧ (p5 ∨ ((p5 ∧ (p2 ∨ True)) ∧ p1)))))))) ∨ (p5 ∨ p4)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_348790565381821902553810166610 : (p3 → (p1 ∨ ((False ∧ ((p1 ∨ False) ∧ ((((p4 → False) ∧ ((p2 ∨ p3) → p3)) ∨ p4) ∨ ((p2 ∨ p5) ∧ (p2 → (p3 ∧ p5)))))) ∨ p3))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_677442060908076937935618455957 : (((((((p5 ∨ p4) ∨ ((p2 ∨ p4) ∧ ((p3 ∧ ((True → p1) ∧ True)) → p5))) → (p4 ∧ p5)) ∨ True) ∨ (p3 ∧ (p3 → (p2 → True)))) ∨ p4) ∧ True) := by
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
theorem thm_5_vars_216585575156695546942860992605 : ((((p4 ∨ p3) ∧ True) ∧ p2) → ((p5 ∨ p2) ∧ (True → ((False ∨ p4) ∨ ((((((False ∨ p2) ∧ p1) ∨ p5) ∨ p4) → (p2 → p5)) → p3))))) := by
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
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h3
  case inr h7 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h3
  -- Implications on the right can always be decomposed.
  intro h8
  -- Conjunctions on the left can always be decomposed.
  let h9 := h1.left
  let h10 := h1.right
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
    -- One of the premise coincides with the conclusion.
    exact h13
  case inr h14 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h15
    -- One of the premise coincides with the conclusion.
    exact h14



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_227305415866876255924624600019 : (((p2 → p1) → False) ∨ (((((True → p5) ∧ p5) → p1) → (((p1 → (p4 → True)) ∧ False) ∨ p5)) ∨ (p3 ∨ (((True ∨ p3) → p1) ∨ True)))) := by
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
theorem thm_5_vars_45044605417263333379138489016 : ((((True → False) ∨ ((p1 → p1) ∨ (False ∨ ((((p1 ∨ ((p5 → p5) ∨ p4)) ∧ p3) → p3) ∧ ((True → True) ∧ (p4 → p4)))))) → p3) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_309929044529044290479953763437 : (p2 ∨ (((p3 → ((p2 ∧ p5) → p1)) → ((p2 ∨ (p1 → False)) ∧ ((True ∨ p3) ∧ (p2 ∨ True)))) ∨ ((False ∧ ((p4 ∨ p1) ∨ True)) → False))) := by
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
theorem thm_5_vars_134326811936432045530597389744 : (((p2 ∧ (((True → p1) → (True ∨ ((p5 ∨ p3) ∨ p1))) → (((p4 ∨ p2) → (p3 → p2)) ∨ (True ∧ p3)))) ∨ p5) ∨ ((p3 ∧ p1) → p1)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- One of the premise coincides with the conclusion.
  exact h3



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_67711255484160187064039914480 : ((p2 → ((((((p2 ∧ ((((False → (False ∧ ((False ∧ p4) → (p2 → False)))) ∨ p4) → p1) → p1)) ∧ p3) → False) → False) ∨ p5) ∧ p5)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_69133470604440150911854235090 : ((p5 → (((((p3 ∨ ((((p4 → p1) → (p2 ∨ (p2 → p3))) ∨ p5) ∨ p3)) → p1) ∧ (p4 ∧ p3)) ∧ False) ∧ ((p1 ∧ p3) ∨ p3))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_525686681685726248683870295526 : (((True ∧ (p3 → (p4 ∨ (((p4 ∧ False) ∨ ((p1 ∧ p4) ∨ p2)) ∨ (True ∧ (((p4 ∧ p3) ∨ ((True ∨ (p4 → p1)) ∧ False)) → p3)))))) ∧ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
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
    -- Conjunctions on the left can always be decomposed.
    let h4 := h3.left
    let h5 := h3.right
    -- One of the premise coincides with the conclusion.
    exact h5
  case inr h6 =>
    -- Conjunctions on the left can always be decomposed.
    let h7 := h6.left
    let h8 := h6.right
    -- Disjunctions on the left can always be decomposed.
    cases h7
    case inl h9 =>
      -- False on the left can always be used.
      apply False.elim h8
    case inr h10 =>
      -- False on the left can always be used.
      apply False.elim h8
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_58960580543728136596491950061 : (((p2 ∧ p1) ∨ (p4 ∧ (((((p4 → (False ∨ (p5 ∨ p3))) ∨ (False → p3)) ∧ p2) → p4) ∧ (((p3 ∧ (p3 ∧ p3)) → p1) ∨ p3)))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_217923286286902368456640980387 : (((p5 → (p3 ∨ p5)) → p3) → (((False ∨ (False ∨ (p2 ∧ p4))) ∨ ((True ∧ p4) → (p1 ∨ True))) ∨ (((p2 ∧ p4) → (True → p4)) ∨ False))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h2
  -- Conjunctions on the left can always be decomposed.
  let h3 := h2.left
  let h4 := h2.right
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_47132499445571255215606793402 : ((((p4 ∨ (((p5 ∨ p5) ∨ (p5 ∧ (p4 ∧ (False → ((p5 ∨ p1) → (p3 ∨ p2)))))) ∨ False)) → ((p4 → p2) → p3)) ∨ (False → p4)) ∨ p1) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_178570102393502270175297399889 : (((True ∧ (p3 ∧ (p5 → (p3 ∧ True)))) ∧ (p4 ∨ (p2 ∧ (True ∧ True)))) ∨ (p2 ∨ ((((False ∨ p3) → p3) ∨ p5) ∨ (False ∧ (p2 ∧ p5))))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
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
theorem thm_5_vars_623049112682306677908741066804 : ((((p5 ∧ (p2 ∨ (((True ∧ p2) ∧ (((p4 ∧ (True → p4)) ∧ (p3 → p4)) ∧ ((p4 ∧ p4) ∨ p4))) → ((p3 → p2) → False)))) ∨ p3) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_226891691456060229476270635101 : (((p5 ∧ p4) → p3) ∨ ((((p2 ∧ p5) ∧ p4) ∨ ((p4 → p3) → ((p4 → ((True → p3) ∧ False)) → p5))) ∨ (p2 → (True ∧ (p5 → p5))))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
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
  -- One of the premise coincides with the conclusion.
  exact h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_263686597118561414601994286488 : (True ∧ ((((p4 ∧ True) ∧ ((p3 → (p3 ∨ (True ∧ ((p1 ∨ (p3 → p1)) ∨ p2)))) ∧ p1)) → p2) ∨ (True ∨ (p3 ∨ ((p1 ∧ p3) ∨ True))))) := by
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
theorem thm_5_vars_313257907255263255347408325573 : (p3 ∨ ((True ∧ (((((False → ((p1 ∨ (p2 → p1)) ∨ (p4 ∨ (p5 → (((p5 ∧ p5) ∨ p3) ∧ p5))))) ∧ True) ∨ p5) → False) ∨ True)) ∨ p5)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_165744768251381408769070783894 : ((((p4 ∨ p2) ∧ (p1 → False)) ∨ (((False → (True ∨ p5)) ∧ p1) → ((False → p2) → False))) ∨ (p4 ∨ (p1 → ((p5 → p1) ∨ (True ∨ p4))))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_682664021844954063275440353246 : (((((((p2 ∨ p5) ∨ (p5 ∨ True)) ∨ False) ∨ (p3 ∧ (p1 ∨ ((p2 → (p4 ∧ p2)) ∨ p3)))) ∧ (((p1 ∨ (p4 → p2)) ∧ False) ∨ p5)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_172107622756357688614734333646 : (((p1 → (False → ((True → True) ∨ ((p5 ∧ (p5 ∨ True)) → p1)))) → (False ∨ p3)) ∨ ((True ∧ ((p3 ∨ (p1 → p3)) → p2)) → (True ∧ True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_234330067822414128985144782015 : ((p1 → (p4 ∧ p2)) → ((p2 ∧ ((((p3 → ((p3 ∧ p1) → (p2 → (p4 ∨ p4)))) → ((p2 → (p4 ∧ p2)) ∨ p5)) ∧ True) → p5)) ∨ True)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_775372759559773495819988580662 : (((False ∨ (p1 ∧ ((((((p4 ∧ p5) ∨ ((False ∧ (p5 ∧ (p2 ∧ p3))) ∧ False)) ∧ (False → p3)) ∧ p2) → p2) → (p5 ∨ (p1 → p2))))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_153016232648364044199123828655 : ((p2 ∧ ((p5 ∨ (p5 → ((p3 → p4) ∨ (True ∧ (False ∨ (p2 ∧ ((p5 ∧ (p2 ∧ True)) → p5))))))) → False)) → (((p4 ∨ p2) ∨ p4) → p3)) := by
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
      -- Conjunctions on the left can always be decomposed.
      let h5 := h1.left
      let h6 := h1.right
      -- We want to use the implication h6 based on <expert-advice>. So we show its premise.
      have h7 : (p5 ∨ (p5 → ((p3 → p4) ∨ (True ∧ (False ∨ (p2 ∧ ((p5 ∧ (p2 ∧ True)) → p5))))))) := by
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- Implications on the right can always be decomposed.
        intro h8
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- Implications on the right can always be decomposed.
        intro h9
        -- One of the premise coincides with the conclusion.
        exact h4
      -- We have shown the premise of h6, we can now drive its conclusion.
      let h10 := h6 h7
      -- False on the left can always be used.
      apply False.elim h10
    case inr h11 =>
      -- Conjunctions on the left can always be decomposed.
      let h12 := h1.left
      let h13 := h1.right
      -- We want to use the implication h13 based on <expert-advice>. So we show its premise.
      have h14 : (p5 ∨ (p5 → ((p3 → p4) ∨ (True ∧ (False ∨ (p2 ∧ ((p5 ∧ (p2 ∧ True)) → p5))))))) := by
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- Implications on the right can always be decomposed.
        intro h15
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- Conjunctions on the right can always be decomposed.
        apply And.intro
        -- True on the right can always be proven directly.
        apply True.intro
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- Conjunctions on the right can always be decomposed.
        apply And.intro
        -- One of the premise coincides with the conclusion.
        exact h12
        -- Implications on the right can always be decomposed.
        intro h16
        -- Conjunctions on the left can always be decomposed.
        let h17 := h16.left
        let h18 := h16.right
        -- Conjunctions on the left can always be decomposed.
        let h19 := h18.left
        let h20 := h18.right
        -- One of the premise coincides with the conclusion.
        exact h17
      -- We have shown the premise of h13, we can now drive its conclusion.
      let h21 := h13 h14
      -- False on the left can always be used.
      apply False.elim h21
  case inr h22 =>
    -- Conjunctions on the left can always be decomposed.
    let h23 := h1.left
    let h24 := h1.right
    -- We want to use the implication h24 based on <expert-advice>. So we show its premise.
    have h25 : (p5 ∨ (p5 → ((p3 → p4) ∨ (True ∧ (False ∨ (p2 ∧ ((p5 ∧ (p2 ∧ True)) → p5))))))) := by
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Implications on the right can always be decomposed.
      intro h26
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- Implications on the right can always be decomposed.
      intro h27
      -- One of the premise coincides with the conclusion.
      exact h22
    -- We have shown the premise of h24, we can now drive its conclusion.
    let h28 := h24 h25
    -- False on the left can always be used.
    apply False.elim h28



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_180352210959539646203646110501 : (((((((True ∧ p5) ∧ p1) ∨ p1) ∨ (True → p1)) ∧ True) ∨ (p2 ∨ False)) → ((True ∧ (p4 → (p5 ∨ (p3 ∨ False)))) → ((p3 ∨ p1) ∨ True))) := by
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
    -- Disjunctions on the left can always be decomposed.
    cases h6
    case inl h8 =>
      -- Disjunctions on the left can always be decomposed.
      cases h8
      case inl h9 =>
        -- Conjunctions on the left can always be decomposed.
        let h10 := h9.left
        let h11 := h9.right
        -- Conjunctions on the left can always be decomposed.
        let h12 := h10.left
        let h13 := h10.right
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
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- True on the right can always be proven directly.
      apply True.intro
  case inr h16 =>
    -- Disjunctions on the left can always be decomposed.
    cases h16
    case inl h17 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- True on the right can always be proven directly.
      apply True.intro
    case inr h18 =>
      -- False on the left can always be used.
      apply False.elim h18



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_50155063245404350687282159275 : (((p2 → (p1 → ((((p5 ∨ (p5 → True)) ∧ (True → (False ∨ ((p1 ∧ p4) → True)))) ∨ p5) ∨ p4))) ∧ (False ∧ (p5 ∧ (False ∧ p3)))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_761463529478233657304253909388 : (((p3 ∧ ((p2 ∨ (((True ∧ (p3 → p5)) ∨ (False ∧ False)) ∨ ((((p3 ∧ p1) ∨ True) ∨ p1) ∧ (False ∧ ((False → False) ∧ True))))) ∧ p4)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_232525680277401347473437088820 : ((True ∧ (p5 → p2)) → (p2 → ((p2 → ((False → False) → ((p3 ∨ (p3 ∨ p5)) ∨ p2))) ∧ (p4 ∨ (p4 → (p2 ∧ (p1 ∨ (True ∨ True)))))))) := by
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
  -- Conjunctions on the left can always be decomposed.
  let h5 := h1.left
  let h6 := h1.right
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h2
  -- Conjunctions on the left can always be decomposed.
  let h7 := h1.left
  let h8 := h1.right
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h9
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- One of the premise coincides with the conclusion.
  exact h2
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_180046684588950357894556596475 : (((p1 ∨ (((p5 → (p3 ∨ p2)) ∧ (False ∧ (p3 → p2))) → p2)) ∨ p2) → ((p1 ∨ p3) ∨ ((((p3 ∧ p2) → p5) → p2) ∨ (False → p5)))) := by
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
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- One of the premise coincides with the conclusion.
      exact h3
    case inr h4 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Implications on the right can always be decomposed.
      intro h5
      -- False on the left can always be used.
      apply False.elim h5
  case inr h6 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h7
    -- False on the left can always be used.
    apply False.elim h7



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_345553028737939632719882066955 : (p3 → (((p5 ∨ (((True ∨ p1) → p2) ∨ True)) → (((p4 ∧ ((p3 ∨ p1) → p4)) ∨ ((p3 ∨ p4) ∨ (True ∨ p3))) ∨ (p5 ∧ p4))) ∨ p2)) := by
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
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- One of the premise coincides with the conclusion.
    exact h1
  case inr h4 =>
    -- Disjunctions on the left can always be decomposed.
    cases h4
    case inl h5 =>
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
    case inr h6 =>
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
theorem thm_5_vars_708809758844455509737842423455 : (((((p2 → ((p3 → (p4 ∨ False)) ∧ True)) → p4) → (((False ∧ p2) ∧ ((p1 → (p2 → (p2 → p5))) → (False ∨ (True ∧ True)))) ∧ p1)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_103406148350440248166939180949 : (((p4 → ((((False → p2) ∧ p4) → False) → (p5 ∧ (False ∨ (((p4 ∨ True) ∧ ((p3 ∨ (p2 ∨ p1)) ∨ False)) ∧ False))))) ∨ True) ∧ (p2 ∨ True)) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_183814679997866287490250455167 : (((((False → (p5 → ((False ∧ p2) → False))) ∧ True) → False) ∧ False) ∨ ((((False ∧ False) → p1) ∧ ((True → False) → (p2 ∧ True))) ∨ (p1 ∨ p2))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- False on the left can always be used.
  apply False.elim h2
  -- Implications on the right can always be decomposed.
  intro h4
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- We want to use the implication h4 based on <expert-advice>. So we show its premise.
  have h5 : True := by
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h4, we can now drive its conclusion.
  let h6 := h4 h5
  -- False on the left can always be used.
  apply False.elim h6
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_313983077907504964089975407891 : (p3 ∨ (((((True ∧ (p1 ∧ p2)) → p3) ∨ False) ∨ ((p3 ∨ ((False ∨ (False ∨ (p2 → (False ∨ p5)))) ∨ (p1 ∨ p3))) ∨ True)) ∨ (True → p4))) := by
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
theorem thm_5_vars_52123923351296538574145620986 : ((((p4 ∧ ((True ∧ (p3 ∧ ((p2 → (p1 ∧ p2)) ∨ (p2 → p3)))) ∨ False)) → p3) → ((p2 ∨ p4) ∧ ((p3 → p4) ∨ (True → True)))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_678716811068753098020915421991 : (((((True ∧ True) → (((p5 ∧ p5) ∧ (True ∧ True)) ∨ ((p4 ∧ ((True → (p1 ∧ p5)) ∧ False)) ∧ False))) ∨ ((False → (False → False)) ∨ p2)) ∨ p5) ∧ True) := by
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
  -- Implications on the right can always be decomposed.
  intro h2
  -- False on the left can always be used.
  apply False.elim h2
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_51916739948730712103263769170 : (((((((p4 ∧ p1) ∧ ((p4 ∨ p4) ∧ True)) ∨ (p5 ∨ True)) → p5) → (p5 ∨ False)) ∨ (((True → (True → True)) ∧ (p5 ∧ p3)) ∧ False)) ∨ False) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h2 : (((p4 ∧ p1) ∧ ((p4 ∨ p4) ∧ True)) ∨ (p5 ∨ True)) := by
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h3 := h1 h2
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- One of the premise coincides with the conclusion.
  exact h3



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_709276868308961969194302252149 : (((((p2 → False) ∨ (((p1 ∨ p2) ∨ False) ∧ False)) → ((((((p4 ∧ (p3 ∧ p4)) ∨ ((p4 ∧ p4) → p1)) ∧ p3) ∧ p1) ∨ p2) ∧ False)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_53710135712781230930804203451 : (((p2 ∨ (((p3 → (p1 ∧ p4)) → p4) → (False ∧ True))) ∧ ((p1 ∨ (p1 → (p5 ∧ (True ∧ p4)))) ∨ (((True ∧ p2) ∨ False) ∧ p2))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_148914752121176240673206473236 : (((((p1 ∨ p3) ∧ p3) ∨ p1) → ((p1 ∨ ((p2 ∧ p1) ∧ (p5 ∨ p4))) ∨ ((p4 ∨ (p4 ∧ p1)) ∧ p1))) ∨ (True ∨ (p4 → (p3 ∨ p5)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_600963452876121308101755745139 : ((((p1 ∧ ((p2 ∨ ((((True ∨ p3) → False) ∨ (((((True ∧ p1) ∧ p3) ∨ p5) ∧ True) → False)) ∧ (p2 ∨ False))) ∧ (p3 ∨ False))) ∧ p3) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_117066773174773651568162427142 : (((True → True) → (((((p4 ∨ True) → (p2 → p5)) ∨ (p5 → p3)) ∧ ((p5 ∨ p1) ∧ (p3 → p2))) ∨ (False → (p2 → p5)))) ∨ (p2 ∧ True)) := by
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
  apply False.elim h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_329028867718406293658815911353 : (True → ((((False ∨ p4) ∧ p3) → (p5 ∨ p5)) → (p4 → (p1 → ((((True → p5) ∨ p2) ∧ (((p5 ∨ p4) → True) ∧ (p1 ∧ p2))) ∨ p1))))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Implications on the right can always be decomposed.
  intro h3
  -- Implications on the right can always be decomposed.
  intro h4
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h4



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_46119692097536827852459554663 : ((((p5 ∨ (((((False ∨ (p3 ∨ p3)) → p3) → p2) ∧ p4) ∨ (((False ∧ (p1 ∧ (p4 ∨ p5))) → p2) ∨ p3))) ∨ False) ∧ (True ∨ p3)) ∨ p2) := by
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
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- False on the left can always be used.
  apply False.elim h2
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_648059998788207063247208867666 : ((((((p3 → (((False ∧ False) ∧ p1) ∨ (p4 ∧ False))) → (p5 ∧ ((p5 ∧ p2) ∧ (p2 → (p5 ∧ (True ∧ p2)))))) ∧ p5) ∧ (p2 → p1)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_833028971387912789423414471501 : ((((((((p2 ∨ (((((p2 ∧ True) ∨ p3) ∧ p5) → (p1 ∧ p2)) ∧ False)) ∨ ((p1 → (False ∨ p1)) ∧ True)) ∨ True) → p5) ∧ p1) ∨ False) → p5) ∧ True) := by
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
    -- We want to use the implication h3 based on <expert-advice>. So we show its premise.
    have h5 : (((p2 ∨ (((((p2 ∧ True) ∨ p3) ∧ p5) → (p1 ∧ p2)) ∧ False)) ∨ ((p1 → (False ∨ p1)) ∧ True)) ∨ True) := by
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- True on the right can always be proven directly.
      apply True.intro
    -- We have shown the premise of h3, we can now drive its conclusion.
    let h6 := h3 h5
    -- One of the premise coincides with the conclusion.
    exact h6
  case inr h7 =>
    -- False on the left can always be used.
    apply False.elim h7
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_56906488182785834719291518990 : (((p4 ∧ (p1 → True)) ∧ ((((p5 ∨ (p5 ∨ (p3 ∧ p3))) → p1) ∧ (((p4 → p5) ∧ (p5 → p1)) → False)) ∨ (p1 ∧ (True → True)))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_47230629949395443498780435842 : ((((((p4 ∨ p4) ∨ ((p4 ∨ p3) → p4)) ∨ p1) ∨ ((p1 ∨ p1) ∨ ((p4 ∨ True) ∨ (p4 ∨ ((p2 → p1) ∨ p1))))) ∨ (True ∧ p4)) ∨ False) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
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



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_147964762512538941410951631648 : (((p4 ∨ (True ∧ ((False ∧ (p4 → (p3 ∨ (p1 ∨ (True → p2))))) ∧ ((p5 ∧ p3) → p4)))) ∧ (p1 ∨ p4)) ∨ (((True ∧ p2) → p2) ∨ p1)) := by
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
  exact h3



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_66541484559484716149490524500 : ((True → ((p4 ∧ ((((p1 ∧ p1) ∧ p4) ∨ p4) ∨ (((p1 → (p5 ∨ (((p2 → p2) → True) → (False → p5)))) ∨ p5) ∨ p2))) → p2)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_168665800260513587954341976349 : ((p5 ∧ ((p1 ∨ ((p1 → (p2 ∧ False)) → ((False → (p1 ∨ p4)) ∨ (p3 → p3)))) ∧ p5)) → ((p1 ∨ (p2 ∧ (p5 → (p1 ∧ False)))) → p1)) := by
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
    -- Disjunctions on the left can always be decomposed.
    cases h6
    case inl h8 =>
      -- One of the premise coincides with the conclusion.
      exact h8
    case inr h9 =>
      -- One of the premise coincides with the conclusion.
      exact h3
  case inr h10 =>
    -- Conjunctions on the left can always be decomposed.
    let h11 := h10.left
    let h12 := h10.right
    -- Conjunctions on the left can always be decomposed.
    let h13 := h1.left
    let h14 := h1.right
    -- Conjunctions on the left can always be decomposed.
    let h15 := h14.left
    let h16 := h14.right
    -- Disjunctions on the left can always be decomposed.
    cases h15
    case inl h17 =>
      -- One of the premise coincides with the conclusion.
      exact h17
    case inr h18 =>
      -- We want to use the implication h12 based on <expert-advice>. So we show its premise.
      have h19 : p5 := by
        -- One of the premise coincides with the conclusion.
        exact h16
      -- We have shown the premise of h12, we can now drive its conclusion.
      let h20 := h12 h19
      -- We need to get the right conjuct of h20 based on <expert-advice>.
      let h21 := h20.right
      -- False on the left can always be used.
      apply False.elim h21



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_345486400671499986808215995529 : (p3 → (((((((True ∧ (p3 ∧ (p3 ∧ ((p2 ∧ False) ∧ p5)))) → p1) ∧ (p3 ∨ p5)) → p2) ∨ p4) ∨ ((False ∧ (p3 → p5)) ∨ p3)) ∨ False)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_43686314236018171033004406256 : ((((((p3 → (p5 ∨ False)) ∧ (p3 → ((p2 ∧ p5) ∧ p5))) ∨ ((p3 → ((False ∧ (p2 → False)) ∨ (p4 ∧ p1))) ∨ p3)) → p1) → p1) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_246558413974572184381814670550 : ((p5 ∧ p2) ∨ (((((p5 → (True ∨ False)) ∨ True) ∨ ((p3 ∨ p1) ∨ p3)) → (p4 ∨ (False → (False ∧ ((p2 → (p2 → False)) → p5))))) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_229588125992760298917868533485 : ((p3 → (p1 ∧ False)) ∨ (((((p4 → p1) ∨ (False ∧ False)) ∨ (((True → False) ∨ (p4 → (True ∨ (p5 ∧ p1)))) ∧ (p3 ∨ p5))) ∨ True) ∨ p1)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_228711778075722638927296865803 : ((p2 ∨ (True → p1)) ∨ ((p4 ∨ ((((p3 ∨ p3) ∧ p5) → (p5 → (p5 ∨ p4))) ∧ (((p4 → (p5 ∨ (p2 ∧ False))) ∨ True) ∨ p3))) ∨ p3)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
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
  -- Conjunctions on the left can always be decomposed.
  let h3 := h1.left
  let h4 := h1.right
  -- Disjunctions on the left can always be decomposed.
  cases h3
  case inl h5 =>
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- One of the premise coincides with the conclusion.
    exact h4
  case inr h6 =>
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- One of the premise coincides with the conclusion.
    exact h4
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_41872897349179971408646514090 : (((((p2 → p5) → False) ∨ ((((p4 ∧ ((p5 ∧ p4) ∧ (False ∨ (p3 ∨ p4)))) → p3) ∧ (p1 ∨ (p2 ∧ p1))) ∨ (True ∧ p2))) ∨ False) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_38565084073540208346067331923 : ((((((p1 → p5) → (p1 → p5)) → ((p3 → True) → p4)) ∨ (True ∨ (p2 ∧ (((p4 → (p5 ∨ True)) ∨ False) ∨ (False → p4))))) ∧ p3) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_703287074372567447648402294330 : ((((p4 ∧ ((((p5 ∨ p2) ∧ p4) ∧ (p1 ∨ p3)) ∨ True)) ∨ (p1 ∨ (p5 ∨ (((p3 ∧ p2) ∨ (((p3 ∧ p1) ∨ p5) ∧ p4)) → p4)))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_136089725823300401944236620257 : (((((p1 ∧ (p3 ∧ False)) ∧ (p1 → p1)) ∧ True) ∨ (((p5 → p2) ∧ ((True ∧ p1) ∨ (p3 ∨ (p1 ∨ p4)))) ∨ True)) ∨ (p5 ∧ (p4 → p4))) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_38022767896922133317619559087 : ((((p2 → ((((p4 → (((p5 → False) ∧ (((p1 ∧ p4) ∨ p2) ∧ p1)) ∨ p3)) ∨ (False ∧ False)) ∧ True) ∨ p3)) ∨ (p3 ∨ True)) ∧ True) ∨ False) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
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
theorem thm_5_vars_52605631208172758465348820816 : (((((p1 ∨ (True → p3)) → True) ∧ (False ∧ (((False ∧ False) ∧ True) ∨ True))) ∨ ((((False ∧ p4) ∧ (p3 ∧ p3)) ∨ p3) → (False ∧ p3))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_65286112695487989632407600154 : ((p3 ∨ (((p5 ∧ (((((p2 ∨ (p1 ∧ p1)) ∧ (p4 ∧ (p5 → p5))) ∨ p2) → (p4 ∧ False)) → (False ∧ True))) ∧ p3) ∨ (False → p4))) ∨ p4) := by
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
theorem thm_5_vars_157623646579050629921726001456 : ((((p3 → (((p5 ∧ True) ∧ (True ∧ p1)) → p1)) → ((p1 ∨ p2) → p5)) ∧ ((p3 ∨ p4) ∧ p3)) ∨ (False → (True → (p5 → (p5 → p5))))) := by
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
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_199871331859187313122128180848 : (((p2 → ((p2 ∨ p5) ∨ True)) ∧ (p3 ∧ p3)) → ((p5 ∨ ((p1 → (p2 ∨ p2)) ∧ (p3 → (p4 ∨ True)))) ∨ ((p3 ∨ p5) ∨ (p2 ∧ p4)))) := by
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
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- One of the premise coincides with the conclusion.
  exact h5



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_44569531647827071606471610762 : ((((p3 → ((((p2 → False) ∧ p5) ∧ False) ∧ p5)) ∧ (((p3 ∧ (p1 ∨ p2)) ∧ p1) ∨ (p4 ∧ (p5 ∧ ((p2 → p4) → p3))))) → p1) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_585938777813435544820160932170 : ((((((((True → (p3 ∧ (((p2 → p1) ∧ p1) ∧ p1))) ∨ (p1 → (p3 ∨ (False ∨ (p3 ∧ p4))))) → p1) → (p2 → p5)) ∧ p2) ∧ p5) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_574774776476836501780074156856 : (((p2 → (((p1 ∨ (p1 ∧ p3)) ∧ (p5 ∨ (((p3 ∨ p2) ∧ (p3 → True)) ∨ p3))) ∨ (p5 ∨ ((p1 ∧ True) ∨ (p3 → (p1 → p1)))))) ∧ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
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
  -- Implications on the right can always be decomposed.
  intro h2
  -- Implications on the right can always be decomposed.
  intro h3
  -- One of the premise coincides with the conclusion.
  exact h3
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_587601531215219191735855676284 : ((((((((True ∨ p2) ∧ (False → ((True ∨ (((p2 ∨ (p4 ∧ True)) ∨ (p4 ∨ True)) ∧ p3)) ∨ (True ∨ p5)))) ∨ True) → False) ∨ p3) ∧ True) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_804350626441702761567484365216 : (((p3 → ((p2 ∨ (((p1 ∨ p1) → (False ∨ False)) → (p4 ∧ (p1 ∧ p2)))) ∨ (((False ∧ p1) → (p2 ∧ (False ∧ p1))) ∨ (p5 ∧ True)))) ∨ p4) ∧ True) := by
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
  -- Implications on the right can always be decomposed.
  intro h2
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Conjunctions on the left can always be decomposed.
  let h3 := h2.left
  let h4 := h2.right
  -- False on the left can always be used.
  apply False.elim h3
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Conjunctions on the left can always be decomposed.
  let h5 := h2.left
  let h6 := h2.right
  -- False on the left can always be used.
  apply False.elim h5
  -- Conjunctions on the left can always be decomposed.
  let h7 := h2.left
  let h8 := h2.right
  -- False on the left can always be used.
  apply False.elim h7
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_154131373220880867815197630072 : ((((((False ∨ (True → ((((False → p1) ∧ (p2 ∧ p3)) ∨ p2) → p4))) ∧ p2) ∧ p1) ∨ p1) ∨ True) ∧ ((True ∨ p5) → ((False ∨ p3) ∨ True))) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
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
theorem thm_5_vars_165045802653377435461459131344 : ((((p3 ∨ p5) ∨ ((p4 → True) ∧ (p3 → ((p5 ∧ p3) ∧ ((p4 ∧ p1) → p3))))) → p1) ∨ ((p4 → p4) ∧ ((p4 → p5) → (p2 ∨ True)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
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
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_685986421317706454588754519212 : (((((((p3 → p1) → ((((p4 ∨ False) → True) ∨ False) ∧ False)) ∨ (p3 ∧ True)) ∨ (True ∧ True)) → ((((False → True) ∨ p1) → p3) ∧ p3)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_225916218634754552374306905124 : (((p2 ∧ True) ∨ False) ∨ ((((((p1 → p4) ∨ (p3 ∧ False)) ∧ (((False ∨ p4) ∧ (p4 → p2)) ∨ ((p1 ∨ p3) → p3))) ∧ False) ∧ p5) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_689446078110911697739195502113 : (((((((True ∨ ((True ∧ True) → True)) ∨ (True → True)) ∧ p5) ∨ ((p5 → False) ∨ p5)) ∨ (p1 ∨ (p2 ∨ (True ∨ ((p5 ∨ False) ∨ p2))))) ∨ False) ∧ True) := by
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
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_57258598531534573975280033338 : ((((False ∨ True) → p5) ∨ (p2 ∧ (((((False → p4) → (False ∨ (p2 ∨ ((p4 → p2) ∧ (False ∧ p3))))) ∨ p3) ∨ p2) ∧ (p3 → True)))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_185567280173039474788702387378 : ((p4 ∨ (p1 ∧ (p1 ∧ (p1 → (p2 ∨ (p3 ∨ (p5 ∨ p4))))))) ∨ (True ∨ (True ∧ (((((p2 → p5) → p2) ∧ p5) → True) → (p1 ∨ p5))))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_625193310157807414884319851770 : ((((True → ((p5 → (p4 ∨ p3)) → ((p2 ∧ ((p2 ∧ ((p1 ∨ False) ∧ p3)) ∨ (((p5 ∧ True) ∨ (p2 ∧ False)) ∧ p5))) ∧ p2))) ∨ True) ∨ p2) ∧ True) := by
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
theorem thm_5_vars_166138687488663804791373963510 : ((True ∧ (p3 ∧ ((True → p1) ∨ (p1 ∨ (p3 ∧ ((p3 ∧ (p1 ∨ p4)) ∨ (p1 ∧ p3))))))) ∨ ((False ∧ (p4 → p5)) → ((p2 ∧ True) → p1))) := by
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
  let h5 := h1.left
  let h6 := h1.right
  -- False on the left can always be used.
  apply False.elim h5



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_711921062976752258540807169 : (((((p1 ∧ False) ∧ (p1 ∨ (p1 → p1))) ∨ p1) ∨ (((((p4 ∨ False) → p3) → (False ∨ p4)) ∧ True) ∨ ((False ∨ p2) ∨ p5))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_387398122422497952051185582697 : (((((((p1 → (p1 ∧ p5)) ∨ ((True ∧ ((p1 ∨ p5) ∨ p5)) → ((p5 ∧ p4) ∧ p4))) ∨ (p4 → p1)) ∨ (p2 → (True ∨ p3))) ∨ p2) ∧ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
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
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_259098102171958714584238019323 : ((True → p5) → ((p1 ∧ (p4 ∧ p2)) ∨ (((((False ∨ False) ∧ (p2 ∧ p3)) ∨ (p1 ∨ p5)) ∨ (((p2 ∧ (True ∨ p4)) ∧ False) ∧ p1)) ∧ True))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
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
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_355854652372522933569812770618 : (p5 → ((((p5 ∧ (False ∧ (((((False → p4) ∨ p5) ∧ p1) ∧ True) ∨ (True ∧ p5)))) → True) → (p4 ∧ (p2 ∧ p1))) ∨ ((p1 ∨ True) ∨ True))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_303650791858399013477689678564 : (p1 ∨ ((p3 ∨ (((p5 ∨ p1) ∨ ((True ∨ p2) → (False ∧ (p2 → p3)))) → ((p3 ∨ (p4 → True)) ∨ (((p1 ∨ p5) ∨ p3) ∨ p1)))) ∧ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
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
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Implications on the right can always be decomposed.
      intro h4
      -- True on the right can always be proven directly.
      apply True.intro
    case inr h5 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- One of the premise coincides with the conclusion.
      exact h5
  case inr h6 =>
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h7
    -- True on the right can always be proven directly.
    apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_42508186343259248710930016384 : (((False ∨ ((p4 ∧ ((p1 ∧ p5) → False)) ∧ ((True ∧ (p2 ∨ p5)) → ((p5 ∨ p3) ∨ ((((p2 → True) → p4) → p2) ∨ p5))))) ∨ True) ∨ p2) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



