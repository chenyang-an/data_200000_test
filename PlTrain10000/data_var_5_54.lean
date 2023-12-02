variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_316472400625854569663390910019 : (p3 ∨ (p1 ∨ (p3 ∨ ((p3 ∨ ((p2 ∧ p4) ∨ (p5 ∨ (False ∨ (((True ∧ (p3 ∧ (True → (p4 ∨ p5)))) → p2) ∨ p1))))) ∨ (False → p2))))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
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
theorem thm_5_vars_219099542902259431424951651223 : ((True ∨ ((p5 ∧ False) ∨ p1)) → ((((((((False ∧ False) → (True ∨ True)) ∨ p3) ∨ p5) → p2) → p1) ∨ (True → (p2 ∨ (p2 ∧ p1)))) ∨ True)) := by
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
      -- Conjunctions on the left can always be decomposed.
      let h5 := h4.left
      let h6 := h4.right
      -- False on the left can always be used.
      apply False.elim h6
    case inr h7 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- True on the right can always be proven directly.
      apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_122990117323817387218605432731 : ((((p4 → (False ∨ ((True ∨ (True ∨ (p1 ∨ p2))) → p3))) ∨ ((((p5 ∨ True) ∨ p1) ∨ p4) ∧ p3)) ∨ ((p5 ∨ False) → True)) → (p5 ∨ True)) := by
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
      -- True on the right can always be proven directly.
      apply True.intro
    case inr h4 =>
      -- Conjunctions on the left can always be decomposed.
      let h5 := h4.left
      let h6 := h4.right
      -- Disjunctions on the left can always be decomposed.
      cases h5
      case inl h7 =>
        -- Disjunctions on the left can always be decomposed.
        cases h7
        case inl h8 =>
          -- Disjunctions on the left can always be decomposed.
          cases h8
          case inl h9 =>
            -- Show the left disjunct based on <expert-advice>.
            apply Or.inl
            -- One of the premise coincides with the conclusion.
            exact h9
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
theorem thm_5_vars_147344532952542578788044365498 : ((((((True → p5) → False) ∧ (((p1 ∧ (p2 ∨ (p2 ∧ p1))) ∧ (True → p4)) → p2)) → (p5 → p1)) ∨ p3) ∨ ((p1 → (p5 → p4)) → True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_165439748161264635626666051534 : (((False → (((p1 ∨ p5) ∨ False) ∨ ((p1 → (p3 ∨ p4)) ∧ True))) → (p2 ∧ (p3 ∨ p4))) ∨ (p1 → (True → ((p1 ∧ p3) → (True ∨ True))))) := by
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
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_200932146024570881654229748499 : ((p1 ∨ (p2 ∧ ((p5 ∧ p4) → (p4 → True)))) → (((p5 ∨ (p2 → (True → ((p2 ∧ p1) ∨ p1)))) → p2) ∨ ((True → (p4 ∧ p2)) ∨ p1))) := by
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
    -- Conjunctions on the left can always be decomposed.
    let h4 := h3.left
    let h5 := h3.right
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Implications on the right can always be decomposed.
    intro h6
    -- Disjunctions on the left can always be decomposed.
    cases h6
    case inl h7 =>
      -- One of the premise coincides with the conclusion.
      exact h4
    case inr h8 =>
      -- One of the premise coincides with the conclusion.
      exact h4



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_650509016986136400459542077189 : (((((((((True ∧ (p3 ∧ p3)) → False) ∨ False) ∧ (p3 → p4)) ∧ p5) ∨ (p1 ∨ (((p4 ∧ p5) ∧ (p5 ∨ p1)) → p4))) ∧ (p2 ∧ p2)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_346621133973960610851456938341 : (p3 → (((p1 → (p1 ∨ (p5 → True))) → ((((p1 ∨ ((p4 → (p2 ∧ p4)) ∧ p1)) → p4) ∨ p1) ∧ (p5 ∨ p1))) ∨ ((p2 ∧ p1) → p3))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h2
  -- Conjunctions on the left can always be decomposed.
  let h3 := h2.left
  let h4 := h2.right
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_116804547757925654160341764634 : (((p3 ∨ False) ∨ (False ∨ (p2 → (((p3 ∨ p3) ∧ (((p3 → ((p3 → (p4 ∧ p4)) → False)) ∧ (False ∧ p2)) ∨ p1)) ∨ True)))) ∨ (p4 → p5)) := by
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
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_21523041713958497075100690400 : ((((p5 ∨ p3) → (((p1 → p5) → False) ∨ (True ∧ p4))) ∨ ((False → (p1 ∨ (p3 → p3))) ∨ ((p2 ∨ (p5 → (p5 ∨ p2))) ∧ p4))) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- False on the left can always be used.
  apply False.elim h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_215443375663554304101284808674 : ((p3 ∧ ((p3 ∨ p4) → True)) ∨ ((p4 ∨ False) → ((True ∧ p5) ∨ (((p5 ∨ p5) ∨ ((p2 → False) ∧ ((p2 → (False → p5)) → p3))) ∨ True)))) := by
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
    -- True on the right can always be proven directly.
    apply True.intro
  case inr h3 =>
    -- False on the left can always be used.
    apply False.elim h3



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_16838154867388715918596940520 : (((((p1 → False) → p4) ∨ (p1 ∨ (((p2 → p4) ∨ True) → (((p4 ∧ True) ∧ p1) ∨ (True → (p2 ∨ True)))))) ∨ (False → (p2 → p5))) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- False on the left can always be used.
  apply False.elim h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_112120172645819312004275577401 : (((True ∧ ((((p5 → True) → ((((p2 ∧ p5) ∨ p3) ∧ p5) → p2)) → (p1 → ((p3 → False) → (False → p5)))) → p1)) ∨ True) ∨ (True ∨ p5)) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_219780950273600219080257429162 : ((p2 → (True ∧ (p2 → p4))) → ((p1 ∨ (p3 ∧ ((p5 → p1) ∧ (((p2 → p2) → p5) ∧ (p4 ∨ p2))))) ∨ ((p1 ∨ False) ∨ (True ∨ False)))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_91024531289921416949228789965 : (((p1 → p4) ∧ (True → (((p1 ∧ ((p2 ∧ p4) ∧ p3)) → ((False → ((((False → p1) → p3) → (False ∧ p5)) ∧ p2)) ∧ p4)) ∧ p5))) → p5) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- We want to use the implication h3 based on <expert-advice>. So we show its premise.
  have h4 : True := by
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h3, we can now drive its conclusion.
  let h5 := h3 h4
  -- We need to get the right conjuct of h5 based on <expert-advice>.
  let h6 := h5.right
  -- One of the premise coincides with the conclusion.
  exact h6



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_731358039749062481502005537544 : ((((p5 ∨ (p1 ∧ p4)) → (p5 ∧ (p5 ∨ ((p2 → ((True ∧ (p5 ∧ p2)) ∨ ((True ∨ (p3 → p3)) ∧ ((False → False) → p5)))) ∧ False)))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_304728453944169145449589273074 : (p1 ∨ ((((((p5 ∨ (p1 ∨ p1)) ∧ p1) → ((False ∧ p5) ∨ p2)) → p4) ∨ (p2 ∨ ((p5 ∧ (p4 ∧ (p2 ∧ p5))) ∧ False))) ∨ (p5 → p5))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_233316630257026534566472990957 : ((True ∨ (True → False)) → ((((p3 ∨ p2) ∨ p3) ∨ True) ∨ (((p3 → p5) ∨ (p5 ∧ p3)) ∧ (((p1 ∧ False) → p1) ∨ (p1 ∧ (p5 ∧ True)))))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h2 =>
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro
  case inr h3 =>
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_126813353281045392558130450976 : ((p5 ∧ (((p5 → (False ∧ ((p1 ∧ p5) ∨ ((((True ∨ p1) ∧ p2) ∨ p3) ∨ p3)))) ∧ (True ∧ (False → p5))) ∧ (p5 ∧ p5))) → (p4 → p2)) := by
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
  -- Conjunctions on the left can always be decomposed.
  let h7 := h5.left
  let h8 := h5.right
  -- Conjunctions on the left can always be decomposed.
  let h9 := h8.left
  let h10 := h8.right
  -- Conjunctions on the left can always be decomposed.
  let h11 := h6.left
  let h12 := h6.right
  -- We want to use the implication h7 based on <expert-advice>. So we show its premise.
  have h13 : p5 := by
    -- One of the premise coincides with the conclusion.
    exact h12
  -- We have shown the premise of h7, we can now drive its conclusion.
  let h14 := h7 h13
  -- We need to get the left conjuct of h14 based on <expert-advice>.
  let h15 := h14.left
  -- False on the left can always be used.
  apply False.elim h15



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_690005843075906118610616356127 : ((((p2 ∧ ((((p1 ∨ p2) → (p3 → p4)) → ((p3 ∨ True) → p3)) → (p4 → False))) ∨ ((True ∧ (p3 → (p2 → (False ∨ p5)))) ∧ p4)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_350161256657188136601121415273 : (p4 → ((((p1 ∧ p4) ∨ (((p4 ∨ p2) ∧ p5) ∨ p2)) ∨ (p3 ∧ (((p4 ∨ (((False ∧ p4) ∨ False) ∧ False)) → (True → False)) ∧ p3))) ∨ True)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_137830587337174219542643728811 : ((p3 ∨ ((((((p1 ∧ (p1 → (p1 → (True ∧ p5)))) ∧ False) ∨ (False → False)) → (p3 ∧ p5)) ∧ True) → (p2 ∧ p2))) ∨ ((p1 ∨ p5) → True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_133594466964025642983025683641 : ((((p1 → ((((p1 ∧ p2) → (p2 → p1)) → ((p3 ∧ p1) ∧ False)) ∧ ((p4 ∨ (p4 → True)) ∨ p2))) ∨ False) ∧ True) ∨ ((p2 ∧ p1) → p1)) := by
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
theorem thm_5_vars_254998379929268275955299940436 : ((p4 ∧ p1) → ((((True → p1) ∧ ((True → (((p2 ∨ p1) ∨ (True ∧ ((p4 ∧ False) ∧ ((False ∨ False) → p3)))) ∧ False)) ∧ p3)) → False) ∨ False)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h4
  -- Conjunctions on the left can always be decomposed.
  let h5 := h4.left
  let h6 := h4.right
  -- Conjunctions on the left can always be decomposed.
  let h7 := h6.left
  let h8 := h6.right
  -- We want to use the implication h7 based on <expert-advice>. So we show its premise.
  have h9 : True := by
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h7, we can now drive its conclusion.
  let h10 := h7 h9
  -- We need to get the right conjuct of h10 based on <expert-advice>.
  let h11 := h10.right
  -- False on the left can always be used.
  apply False.elim h11



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_322242547781671248375723975928 : (p5 ∨ ((((p2 ∨ ((p5 ∧ p2) ∧ (((False → (((p2 ∨ p1) → ((p4 ∨ p1) ∨ (True ∧ p2))) → False)) → p3) ∧ p2))) ∨ True) ∨ p2) ∨ p3)) := by
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



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_203829554941543488642550421914 : ((False → (((True ∧ False) → p5) ∨ p3)) ∧ (((False ∨ ((True → p3) ∨ p3)) ∨ ((p4 ∨ ((False ∧ p1) ∨ ((p5 → p2) ∨ p5))) ∨ True)) ∨ False)) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h1
  -- False on the left can always be used.
  apply False.elim h1
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_164595898353580589268490512682 : ((((p4 ∧ True) → (p4 → (p1 ∧ (((p2 ∧ p3) ∨ ((p1 ∧ p5) → p3)) ∧ True)))) ∧ p2) ∨ (((p3 → True) → ((False → False) ∧ p4)) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_187242468346451015554548726608 : ((True ∧ ((p5 ∨ ((p3 → (p4 → True)) ∨ (p3 ∨ p3))) → True)) → ((((((p1 ∧ p3) ∨ p4) ∨ False) ∧ p2) ∨ (True ∨ (True → p1))) ∨ p2)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_675230796763974706195267164992 : (((((True ∧ (p5 ∨ (False ∨ ((p3 ∧ ((p4 ∨ p5) ∧ ((p3 ∧ p4) ∨ (p2 → False)))) ∧ p3)))) ∨ False) ∧ (p3 ∧ (False ∧ (False ∨ p1)))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_634781556301795784529854085628 : (((((((p5 → ((p1 → ((p1 → p1) ∨ p5)) ∧ p3)) ∨ (p4 ∧ (p4 ∧ p5))) → (True ∧ (True ∨ p4))) ∨ (p4 ∧ (p1 → False))) → False) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_104601882079660625237395571214 : (((((True ∧ (p1 → (p1 ∧ True))) ∧ False) ∧ ((p4 → (((p4 → p5) ∧ ((True ∨ p4) ∧ p4)) ∨ False)) → p1)) ∨ (p4 → p4)) ∧ (p5 → p5)) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- One of the premise coincides with the conclusion.
  exact h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- One of the premise coincides with the conclusion.
  exact h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_158223645655282027540834939181 : (((False ∨ (True ∧ True)) ∧ (p2 ∧ (((True → p5) ∨ ((p2 ∨ p3) ∨ ((True ∧ p1) ∨ False))) → p1))) ∨ ((p2 ∧ (False → (p2 ∧ False))) → True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_707003398217183469728611707590 : (((((p3 ∧ ((False ∨ (False ∨ p5)) ∧ p3)) ∨ False) ∨ ((p5 → p1) → ((p2 → (p1 ∧ p3)) → (((True → (p2 ∧ True)) ∧ False) ∨ p2)))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_141736321608154665674255623820 : (((True → False) ∧ (((((True → (p1 ∨ True)) ∨ p2) ∧ p1) ∨ (False → (p3 ∧ ((p4 ∨ (False ∨ p2)) ∧ p5)))) → True)) → ((p5 ∧ p4) ∨ p1)) := by
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
  -- False on the left can always be used.
  apply False.elim h5



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_763756418664197930818328079983 : (((p3 ∧ (p1 ∨ ((p5 ∧ p2) ∨ (((p1 ∧ (p2 ∨ ((((p4 ∨ (p1 → True)) → (p2 ∨ (True ∧ p3))) → p1) ∧ True))) ∨ False) → p5)))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_24771523857848909383730987338 : ((((False → p5) ∧ p1) ∨ ((p1 ∧ (True ∧ False)) ∨ (p1 ∨ (p4 → (p1 ∨ (((p5 ∨ p4) ∨ (True → (True ∨ (p4 ∨ True)))) ∨ True)))))) ∧ True) := by
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
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_697271253989675262023131601001 : (((((False ∨ p5) ∧ (((p4 ∨ ((p2 ∧ p4) ∧ p1)) ∧ p1) ∨ p5)) ∧ (((((p2 ∨ (True → (p1 ∧ p1))) → p4) ∨ False) ∨ False) ∨ True)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_148060114089638930614373354855 : (((True → ((p4 → (p1 ∨ (p2 ∧ (p3 ∨ ((p1 ∨ (True ∨ p2)) → (p1 → False)))))) ∨ p1)) ∨ (p2 ∧ False)) ∨ (False → ((p2 ∧ p1) ∨ p4))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_346796344933685161917973692091 : (p3 → ((p1 ∧ (p1 ∨ (p5 ∨ (((((p5 ∨ p4) ∧ p2) ∧ p5) → (True → p5)) ∧ (p4 ∧ (False ∧ p4)))))) ∨ ((p5 ∧ p5) → (p5 ∨ p4)))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h2
  -- Conjunctions on the left can always be decomposed.
  let h3 := h2.left
  let h4 := h2.right
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- One of the premise coincides with the conclusion.
  exact h4



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_51527841290784043612412415101 : ((((p1 ∨ p1) → (((p5 ∨ p3) ∧ ((False ∨ ((p3 ∧ True) ∨ (False ∧ p5))) → p4)) ∨ p2)) → (((True ∨ p3) ∧ (False ∨ p2)) → p4)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_684490445250265592804816610464 : (((((p2 → (p2 ∧ (False ∧ (False → False)))) ∧ (p5 ∨ ((p5 → (True ∧ (p4 ∧ p5))) → p1))) ∨ ((p1 → p4) ∨ (False ∨ (p3 ∧ True)))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_46843927046111895679324198881 : ((((((p1 → p4) ∧ (p5 → p3)) ∨ ((p5 ∨ (p4 ∧ p1)) ∨ ((((p2 ∧ p2) → p2) → (p4 → False)) ∨ False))) ∧ p5) ∨ (False → p1)) ∨ p5) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_734051473968181521057213514801 : ((((True ∨ p3) ∧ (((((True ∧ p5) ∧ ((p2 ∨ (((p5 ∧ p5) → p5) → ((p3 → p5) ∧ p3))) ∧ True)) ∨ (p5 ∧ p5)) ∨ True) ∧ True)) ∨ p5) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro
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
theorem thm_5_vars_59908850452389661710926261946 : (((p5 ∧ p2) → (((p5 → (((p4 → p5) ∨ (p4 ∧ p4)) ∧ (p2 ∨ (p2 → p2)))) → (p4 → p3)) → (p1 → ((p1 ∨ p3) → p3)))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_330500359722739873702436161417 : (True → (p4 ∨ (((p4 ∨ (((((p2 → False) ∧ True) → p3) ∧ p1) ∨ False)) ∨ p2) ∨ ((p5 ∧ True) → (p4 ∨ ((p2 ∨ (p3 → True)) → p5)))))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h2
  -- Conjunctions on the left can always be decomposed.
  let h3 := h2.left
  let h4 := h2.right
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h5
  -- Disjunctions on the left can always be decomposed.
  cases h5
  case inl h6 =>
    -- One of the premise coincides with the conclusion.
    exact h3
  case inr h7 =>
    -- One of the premise coincides with the conclusion.
    exact h3



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_60221992277955278740036287450 : (((True → p2) → (((p3 ∨ (True ∨ (True ∨ (False ∨ (p5 ∧ (False ∨ (((p2 → (p2 ∧ (p1 → True))) → p1) ∨ False))))))) → p3) ∨ p2)) ∨ p5) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
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
theorem thm_5_vars_229524315372909596410196766831 : ((p2 → (p3 ∨ p4)) ∨ ((p2 ∧ p3) ∨ (((((p4 ∨ p4) ∧ (False → p1)) ∧ True) ∨ (p1 → ((p4 → (False → (p2 ∨ True))) ∧ p1))) ∨ p1))) := by
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
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h2
  -- Implications on the right can always be decomposed.
  intro h3
  -- False on the left can always be used.
  apply False.elim h3
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_117381811645328699430313953109 : ((p1 ∧ (((((p1 ∨ ((False ∨ True) ∨ (p3 ∧ p5))) ∨ (p5 → (p5 ∧ (p1 ∧ ((p4 ∨ p4) ∨ p1))))) → p5) → p5) ∧ p2)) ∨ (p4 → p4)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_53529889386277976684990372643 : (((p4 → (p1 ∧ (((p4 ∧ p3) ∧ ((p3 ∨ True) → p4)) ∧ p4))) → (((p4 → ((p1 ∧ True) ∧ False)) ∧ p3) → ((p1 ∨ p3) ∨ False))) ∨ p2) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
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
theorem thm_5_vars_769497632515446756071054771188 : (((p5 ∧ (p3 ∧ ((p5 → (p3 → ((((p2 ∨ ((p4 ∧ (p1 ∨ p4)) ∨ False)) ∨ (p4 ∨ p5)) → (p5 → p4)) → p2))) ∨ (p1 → p1)))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_58608400553007877644371515035 : (((False → p2) ∧ ((False ∧ ((p2 → (p1 ∧ (p5 → ((p3 → p5) ∨ (False ∨ ((((True ∧ p2) → p1) → p1) → p5)))))) → p5)) ∨ True)) ∨ False) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h1
  -- False on the left can always be used.
  apply False.elim h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_615848326067014972400483816893 : (((((((p3 ∨ ((p2 → p1) ∨ False)) ∨ p4) ∧ (False ∨ ((p3 ∧ True) ∧ p1))) ∨ (((((False → p1) ∧ False) → p2) ∧ True) → p3)) ∨ True) ∨ p1) ∧ True) := by
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
theorem thm_5_vars_258808458824247852338598214611 : ((True → False) → (p1 ∨ (p2 → ((((False ∨ (p1 → (p3 ∧ p2))) → p3) → (p5 ∨ (False → (p4 ∧ p3)))) ∧ (p1 ∧ ((p1 ∧ p4) → False)))))) := by
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
theorem thm_5_vars_234927189124397750977937438810 : ((True ∧ True) ∧ ((p5 → (False → False)) ∧ (p4 → (p1 → ((p2 → False) → ((((p4 ∧ p2) ∨ (p5 ∨ (p2 ∧ p3))) ∧ False) ∨ (p4 ∨ p3))))))) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- False on the left can always be used.
  apply False.elim h2
  -- Implications on the right can always be decomposed.
  intro h3
  -- Implications on the right can always be decomposed.
  intro h4
  -- Implications on the right can always be decomposed.
  intro h5
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- One of the premise coincides with the conclusion.
  exact h3



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_225330977300122184744090001286 : (((p1 ∨ False) ∧ True) ∨ (((p3 → False) ∧ (True → (p3 ∧ p3))) ∨ ((p4 ∧ (p4 ∨ ((False → (False ∨ p5)) ∨ (True ∨ p5)))) → (p4 ∨ p2)))) := by
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
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- One of the premise coincides with the conclusion.
    exact h4
  case inr h5 =>
    -- Disjunctions on the left can always be decomposed.
    cases h5
    case inl h6 =>
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- One of the premise coincides with the conclusion.
      exact h2
    case inr h7 =>
      -- Disjunctions on the left can always be decomposed.
      cases h7
      case inl h8 =>
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- One of the premise coincides with the conclusion.
        exact h2
      case inr h9 =>
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- One of the premise coincides with the conclusion.
        exact h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_573033292937961728178284131629 : (((p1 → (p4 ∨ (((False ∧ ((p4 ∧ p2) → (False → p3))) ∧ (p1 ∧ (p2 ∧ (((True → ((p4 ∨ p5) ∨ p5)) ∧ p3) ∧ False)))) ∨ True))) ∧ True) ∧ True) := by
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
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_136313248273160597883369736779 : ((((p2 ∧ (p5 ∧ False)) ∨ p2) ∧ ((((((((p5 ∧ p3) ∨ False) → (False ∨ False)) ∧ p1) ∧ p3) → p3) ∧ p3) → p2)) ∨ ((True ∨ p3) ∧ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_115134257907503145886629336975 : ((((p2 ∧ p1) ∧ (p3 → ((True ∨ (p3 → (False → False))) ∧ p3))) → (p2 → ((p1 ∧ ((True ∧ p5) ∨ p5)) ∨ (p2 ∧ p4)))) ∨ (False ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_666597662114554957113557968493 : (((((p2 ∧ ((p2 ∨ (((p5 ∧ (p5 → False)) ∧ p3) ∨ p3)) → p2)) ∧ ((((False ∨ p3) → p3) ∧ p5) → p2)) ∧ ((p2 ∧ p3) → p5)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_662701839886846937269244217856 : ((((((p4 → p2) ∨ (p3 ∧ p2)) ∨ ((p1 → ((p2 ∨ (p5 → p4)) ∧ p3)) ∨ ((p1 → ((True ∨ True) → p2)) ∨ True))) → (p1 ∨ True)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_340151028639150896686707868310 : (p1 → (p4 → (((p5 → (p2 ∨ True)) ∧ ((((p3 ∧ ((((p4 → p2) ∧ p2) → False) ∨ p1)) ∨ p4) ∧ False) ∨ (p4 ∧ (p5 ∨ p4)))) ∨ False))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h3
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- One of the premise coincides with the conclusion.
  exact h2
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_354712962893612435989067904621 : (p5 → ((((p2 ∧ False) ∨ (((p4 ∨ (True → p5)) → (((True → p4) → True) → (p5 → p4))) ∧ (p2 ∨ True))) ∧ ((p2 → p3) ∨ p4)) ∨ p5)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_113127778106877980288115760282 : (((p1 → ((False → p5) ∧ (True → ((p5 → p1) ∧ ((p3 ∨ ((True ∨ ((p2 ∧ (p3 → p1)) ∧ False)) → True)) ∧ p2))))) → False) ∨ (p4 → p4)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_86035808464527202696917613155 : ((((True → True) → (((True ∧ (False ∨ p5)) → True) ∧ p1)) ∧ ((p1 ∧ p5) ∨ (p2 ∨ ((True ∨ (p1 ∨ True)) ∧ ((True ∧ True) → p2))))) → p1) := by
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
    -- One of the premise coincides with the conclusion.
    exact h5
  case inr h7 =>
    -- Disjunctions on the left can always be decomposed.
    cases h7
    case inl h8 =>
      -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
      have h9 : (True → True) := by
        -- Implications on the right can always be decomposed.
        intro h10
        -- True on the right can always be proven directly.
        apply True.intro
      -- We have shown the premise of h2, we can now drive its conclusion.
      let h11 := h2 h9
      -- We need to get the right conjuct of h11 based on <expert-advice>.
      let h12 := h11.right
      -- One of the premise coincides with the conclusion.
      exact h12
    case inr h13 =>
      -- Conjunctions on the left can always be decomposed.
      let h14 := h13.left
      let h15 := h13.right
      -- Disjunctions on the left can always be decomposed.
      cases h14
      case inl h16 =>
        -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
        have h17 : (True → True) := by
          -- Implications on the right can always be decomposed.
          intro h18
          -- True on the right can always be proven directly.
          apply True.intro
        -- We have shown the premise of h2, we can now drive its conclusion.
        let h19 := h2 h17
        -- We need to get the right conjuct of h19 based on <expert-advice>.
        let h20 := h19.right
        -- One of the premise coincides with the conclusion.
        exact h20
      case inr h21 =>
        -- Disjunctions on the left can always be decomposed.
        cases h21
        case inl h22 =>
          -- One of the premise coincides with the conclusion.
          exact h22
        case inr h23 =>
          -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
          have h24 : (True → True) := by
            -- Implications on the right can always be decomposed.
            intro h25
            -- True on the right can always be proven directly.
            apply True.intro
          -- We have shown the premise of h2, we can now drive its conclusion.
          let h26 := h2 h24
          -- We need to get the right conjuct of h26 based on <expert-advice>.
          let h27 := h26.right
          -- One of the premise coincides with the conclusion.
          exact h27



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_743628064708089342603001754777 : ((((True ∧ p1) → ((((p4 ∨ False) ∨ ((((True → False) ∨ (((p1 → p3) → p2) ∨ False)) ∧ p4) ∧ (False ∧ p1))) ∧ p1) ∨ (True ∨ p1))) ∨ False) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_512475817050729350200540772299 : ((((p3 ∧ p2) ∨ (p2 ∨ (((p2 → p3) ∧ (p4 ∧ p3)) ∨ (((p5 ∨ ((p2 → p3) ∨ (p2 ∨ (False ∧ p5)))) → p5) ∨ (True ∨ p1))))) ∧ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
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
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_166441239456788604733875582982 : ((p2 ∨ ((p1 → (p5 ∨ (p5 → (((p1 ∧ p4) ∧ (True ∨ p3)) ∧ (p5 → False))))) ∧ p1)) ∨ (p2 ∨ ((p3 ∨ False) → (p3 ∨ (p5 ∧ p2))))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h2 =>
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- One of the premise coincides with the conclusion.
    exact h2
  case inr h3 =>
    -- False on the left can always be used.
    apply False.elim h3



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_115232436896460484491766392319 : ((((((p4 → p1) ∧ True) ∨ ((p2 → p5) ∨ p1)) ∨ p2) ∨ (((False ∨ p5) ∨ (p1 ∨ p2)) → (((False → p3) ∧ p5) → p4))) ∨ (True ∨ p4)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_42290557516893891337750889508 : (((p2 ∧ ((((p4 ∨ (((p2 ∨ ((p5 ∧ False) ∨ False)) ∧ p5) → p5)) ∨ p3) ∧ (((False → (p3 ∨ p1)) ∧ p2) ∧ p3)) ∧ p5)) ∨ True) ∨ p5) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_112129339970578199828096252085 : (((False ∧ (((True ∨ True) → ((True → (p4 ∧ (p3 ∧ ((False → p4) ∨ ((p3 → (p1 ∨ p4)) ∨ True))))) ∨ p1)) ∧ p3)) ∨ p1) ∨ (False ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_337534892812534415878507046197 : (p1 → ((((True ∧ p1) ∧ (((p2 ∨ p3) → ((False ∧ False) → p4)) → p2)) ∧ (p5 ∨ ((p5 → True) ∨ p5))) ∨ ((p2 ∨ (p1 ∨ False)) → p1))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h2
  -- Disjunctions on the left can always be decomposed.
  cases h2
  case inl h3 =>
    -- One of the premise coincides with the conclusion.
    exact h1
  case inr h4 =>
    -- Disjunctions on the left can always be decomposed.
    cases h4
    case inl h5 =>
      -- One of the premise coincides with the conclusion.
      exact h5
    case inr h6 =>
      -- False on the left can always be used.
      apply False.elim h6



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_230768425432922961352818351175 : (((True ∧ p1) ∨ True) → ((((((p5 ∧ p3) ∨ p2) ∧ (p3 → (False ∨ (True ∧ (p4 → p4))))) → p2) ∧ p4) ∨ (((p5 ∨ p1) ∧ p5) → p5))) := by
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
    -- Implications on the right can always be decomposed.
    intro h5
    -- Conjunctions on the left can always be decomposed.
    let h6 := h5.left
    let h7 := h5.right
    -- Disjunctions on the left can always be decomposed.
    cases h6
    case inl h8 =>
      -- One of the premise coincides with the conclusion.
      exact h7
    case inr h9 =>
      -- One of the premise coincides with the conclusion.
      exact h7
  case inr h10 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h11
    -- Conjunctions on the left can always be decomposed.
    let h12 := h11.left
    let h13 := h11.right
    -- Disjunctions on the left can always be decomposed.
    cases h12
    case inl h14 =>
      -- One of the premise coincides with the conclusion.
      exact h13
    case inr h15 =>
      -- One of the premise coincides with the conclusion.
      exact h13



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_1761115702595525511738957130 : (((((p2 → p1) ∨ p2) → ((((False → p2) ∨ ((True ∧ p2) ∨ p5)) → (p2 → p2)) → (p2 ∨ p4))) ∧ p2) ∨ (False → (p4 → p4))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_330504598297127369970227362659 : (True → (p4 ∨ (((p5 ∨ p5) ∨ (p1 ∧ (True → False))) ∨ ((False ∨ (((((True ∨ p4) ∨ True) → ((False ∨ p4) ∧ p2)) ∧ p1) → p2)) ∨ p4)))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h2
  -- Conjunctions on the left can always be decomposed.
  let h3 := h2.left
  let h4 := h2.right
  -- We want to use the implication h3 based on <expert-advice>. So we show its premise.
  have h5 : ((True ∨ p4) ∨ True) := by
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h3, we can now drive its conclusion.
  let h6 := h3 h5
  -- We need to get the right conjuct of h6 based on <expert-advice>.
  let h7 := h6.right
  -- One of the premise coincides with the conclusion.
  exact h7



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_253630895948352641602425698491 : ((p1 ∧ True) → ((False ∨ ((False → p2) → p4)) → ((((((False → True) → False) ∨ ((p1 ∨ p1) → p4)) ∧ False) ∨ p5) ∨ ((p4 ∨ True) ∨ p5)))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Disjunctions on the left can always be decomposed.
  cases h2
  case inl h3 =>
    -- False on the left can always be used.
    apply False.elim h3
  case inr h4 =>
    -- Conjunctions on the left can always be decomposed.
    let h5 := h1.left
    let h6 := h1.right
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_167805592671225317475986173927 : ((((((True ∨ (p5 ∨ True)) ∧ False) → (False ∨ p3)) → p1) ∧ (p5 ∧ (p2 → (p3 → p2)))) → ((((True → p4) ∨ p5) ∨ (p1 ∧ p1)) ∧ p1)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- Conjunctions on the left can always be decomposed.
  let h4 := h3.left
  let h5 := h3.right
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h4
  -- Conjunctions on the left can always be decomposed.
  let h6 := h1.left
  let h7 := h1.right
  -- Conjunctions on the left can always be decomposed.
  let h8 := h7.left
  let h9 := h7.right
  -- We want to use the implication h6 based on <expert-advice>. So we show its premise.
  have h10 : (((True ∨ (p5 ∨ True)) ∧ False) → (False ∨ p3)) := by
    -- Implications on the right can always be decomposed.
    intro h11
    -- Conjunctions on the left can always be decomposed.
    let h12 := h11.left
    let h13 := h11.right
    -- Disjunctions on the left can always be decomposed.
    cases h12
    case inl h14 =>
      -- False on the left can always be used.
      apply False.elim h13
    case inr h15 =>
      -- Disjunctions on the left can always be decomposed.
      cases h15
      case inl h16 =>
        -- False on the left can always be used.
        apply False.elim h13
      case inr h17 =>
        -- False on the left can always be used.
        apply False.elim h13
  -- We have shown the premise of h6, we can now drive its conclusion.
  let h18 := h6 h10
  -- One of the premise coincides with the conclusion.
  exact h18



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_231318610346897772269143984853 : (((True → False) ∨ p5) → (((p2 ∨ ((((p1 → p5) → True) ∧ p3) ∨ (False → False))) → (p3 → (p3 ∧ ((p2 → True) ∧ p2)))) ∨ (False → False))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h2 =>
    -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
    have h3 : True := by
      -- True on the right can always be proven directly.
      apply True.intro
    -- We have shown the premise of h2, we can now drive its conclusion.
    let h4 := h2 h3
    -- False on the left can always be used.
    apply False.elim h4
  case inr h5 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h6
    -- False on the left can always be used.
    apply False.elim h6



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_357461801127799269418859785601 : (p5 → ((p2 → p3) → (p4 → ((((p2 ∨ p5) → (((((p2 ∨ (False ∧ p5)) ∧ True) ∨ (p5 → p2)) → (True → p5)) → p3)) ∨ True) ∨ p3)))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Implications on the right can always be decomposed.
  intro h3
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_14818077899098418540073870084 : (((((((False → p5) ∨ (p2 → p3)) ∨ p3) ∨ (True ∨ ((p2 → p1) → p1))) → (p4 ∨ (False → ((p1 ∧ False) ∧ p3)))) ∨ (p1 ∨ p4)) ∧ True) := by
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
      -- Disjunctions on the left can always be decomposed.
      cases h3
      case inl h4 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- Implications on the right can always be decomposed.
        intro h5
        -- Conjunctions on the right can always be decomposed.
        apply And.intro
        -- Conjunctions on the right can always be decomposed.
        apply And.intro
        -- False on the left can always be used.
        apply False.elim h5
        -- False on the left can always be used.
        apply False.elim h5
        -- False on the left can always be used.
        apply False.elim h5
      case inr h6 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- Implications on the right can always be decomposed.
        intro h7
        -- Conjunctions on the right can always be decomposed.
        apply And.intro
        -- Conjunctions on the right can always be decomposed.
        apply And.intro
        -- False on the left can always be used.
        apply False.elim h7
        -- False on the left can always be used.
        apply False.elim h7
        -- False on the left can always be used.
        apply False.elim h7
    case inr h8 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Implications on the right can always be decomposed.
      intro h9
      -- Conjunctions on the right can always be decomposed.
      apply And.intro
      -- Conjunctions on the right can always be decomposed.
      apply And.intro
      -- False on the left can always be used.
      apply False.elim h9
      -- False on the left can always be used.
      apply False.elim h9
      -- False on the left can always be used.
      apply False.elim h9
  case inr h10 =>
    -- Disjunctions on the left can always be decomposed.
    cases h10
    case inl h11 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Implications on the right can always be decomposed.
      intro h12
      -- Conjunctions on the right can always be decomposed.
      apply And.intro
      -- Conjunctions on the right can always be decomposed.
      apply And.intro
      -- False on the left can always be used.
      apply False.elim h12
      -- False on the left can always be used.
      apply False.elim h12
      -- False on the left can always be used.
      apply False.elim h12
    case inr h13 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Implications on the right can always be decomposed.
      intro h14
      -- Conjunctions on the right can always be decomposed.
      apply And.intro
      -- Conjunctions on the right can always be decomposed.
      apply And.intro
      -- False on the left can always be used.
      apply False.elim h14
      -- False on the left can always be used.
      apply False.elim h14
      -- False on the left can always be used.
      apply False.elim h14
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_347846809079231552824287370152 : (p3 → (((p5 → p5) → True) → (((p3 ∧ (p1 ∧ True)) ∨ (((p4 ∧ True) ∨ p1) → (False ∧ (p2 → (p1 ∧ (p5 ∨ (p4 ∨ p4))))))) ∨ True))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_134381762115881237442763705188 : (((p4 ∨ (((p2 → True) → (p4 ∨ ((p2 ∨ (False → ((False ∨ p1) → p2))) → (True ∧ p2)))) ∨ (p3 ∨ p4))) ∨ True) ∨ ((p3 → p1) → p5)) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_185228337095657026444863070943 : ((False ∧ (((p3 ∧ (False ∧ p3)) ∧ True) ∧ (p2 ∧ (p4 → p1)))) ∨ (((((p3 ∧ False) ∧ False) ∨ ((p4 ∨ (p2 ∨ p1)) ∨ p1)) ∨ p1) → True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_50937234585831550944428284816 : ((((p5 ∨ (p1 ∨ ((p2 ∨ p3) ∨ (True → (False ∧ p5))))) ∧ (((p3 → True) ∧ p1) → p4)) ∧ ((p2 → ((True ∨ p3) ∨ p5)) → False)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_218363120017485101298848254263 : (((p3 → p2) ∨ (True ∨ True)) → (((((((True → False) → p2) ∨ (p4 → p5)) → (p2 ∧ ((p5 ∨ False) → p1))) → True) ∨ p2) → (False ∨ True))) := by
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
  case inr h8 =>
    -- Disjunctions on the left can always be decomposed.
    cases h1
    case inl h9 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- True on the right can always be proven directly.
      apply True.intro
    case inr h10 =>
      -- Disjunctions on the left can always be decomposed.
      cases h10
      case inl h11 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- True on the right can always be proven directly.
        apply True.intro
      case inr h12 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- True on the right can always be proven directly.
        apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_341798510806938891582238581634 : (p2 → (((((((p1 → (p4 ∧ (p3 ∧ p2))) ∨ p2) ∧ p3) ∧ ((p5 ∧ (p4 ∧ (p5 → (p2 → p1)))) ∨ p4)) ∨ True) → p1) → (p5 ∨ p1))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
  have h3 : (((((p1 → (p4 ∧ (p3 ∧ p2))) ∨ p2) ∧ p3) ∧ ((p5 ∧ (p4 ∧ (p5 → (p2 → p1)))) ∨ p4)) ∨ True) := by
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h2, we can now drive its conclusion.
  let h4 := h2 h3
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h4



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_317451622719753194806196671552 : (p4 ∨ (((True → False) → ((((((False → p1) ∧ p3) ∨ p5) ∨ False) ∧ ((p4 ∧ True) ∨ ((p2 ∧ p4) → ((False ∨ p5) → p4)))) ∧ p4)) ∧ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
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
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h6 : True := by
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h7 := h1 h6
  -- False on the left can always be used.
  apply False.elim h7
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_218842533985079033144606050912 : ((p2 ∧ ((p5 → p2) ∨ p1)) → (((True ∨ p2) → p5) ∨ (True ∨ ((p5 → (p4 ∧ False)) ∧ (p2 ∨ ((True ∨ p4) → (p5 → (p5 ∨ p1)))))))) := by
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
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- True on the right can always be proven directly.
    apply True.intro
  case inr h5 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- True on the right can always be proven directly.
    apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_157488342279333074648547313161 : ((((True → ((p5 ∨ ((p1 ∨ p2) ∨ p1)) → p2)) → (((p4 ∧ p5) → p5) → p3)) ∨ (p2 → True)) ∨ (p1 ∨ (p2 → (p3 ∨ (True ∨ False))))) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_54810669466292450249203883449 : (((p3 ∨ ((p4 → ((p2 ∨ p5) ∧ True)) → True)) → (p4 → (((p1 ∧ (((True ∧ (p5 ∨ p5)) ∧ (False ∨ True)) ∧ True)) → p4) → p1))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_137100935297231765319411192047 : ((True ∧ ((p3 ∧ (((p4 → p5) ∧ False) ∧ (((False ∨ (p1 → p5)) ∨ p2) ∧ ((p3 → p2) → p2)))) ∧ (True ∧ p4))) ∨ (False → (p2 → p1))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_354592603723903415637116923678 : (p5 → (((p4 ∨ (((p4 ∧ p3) ∧ (p2 ∨ (True → p2))) ∨ (((True → (True ∨ ((True ∨ True) ∨ p5))) ∨ (p4 ∨ p5)) ∨ p2))) ∧ p5) ∨ True)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_673925635101296116869483098540 : (((((p2 → p3) → (p2 ∧ (p4 → ((p2 → ((p3 → (((p3 ∨ (p5 ∧ True)) ∨ p4) ∨ False)) ∨ False)) ∧ p1)))) → (p1 ∨ (p4 ∨ p3))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_105967592038700762536747040752 : (((p3 ∨ (False ∨ ((((False ∧ ((p4 → False) → p5)) ∨ p1) ∧ p2) ∨ p3))) ∨ (((p5 ∧ (True ∨ p4)) ∧ (False ∧ p3)) → p2)) ∧ (p4 → p4)) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
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
  -- Disjunctions on the left can always be decomposed.
  cases h5
  case inl h6 =>
    -- Conjunctions on the left can always be decomposed.
    let h7 := h3.left
    let h8 := h3.right
    -- False on the left can always be used.
    apply False.elim h7
  case inr h9 =>
    -- Conjunctions on the left can always be decomposed.
    let h10 := h3.left
    let h11 := h3.right
    -- False on the left can always be used.
    apply False.elim h10
  -- Implications on the right can always be decomposed.
  intro h12
  -- One of the premise coincides with the conclusion.
  exact h12



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_325779230719392308993822955428 : (p5 ∨ (p2 ∨ (p3 ∨ ((((True → (p2 ∨ p5)) ∨ ((True ∨ p3) ∨ (False ∨ ((False → False) ∧ (p4 → (p3 ∨ False)))))) ∨ False) → (p2 ∨ True))))) := by
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
    -- Disjunctions on the left can always be decomposed.
    cases h2
    case inl h3 =>
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
        cases h8
        case inl h9 =>
          -- False on the left can always be used.
          apply False.elim h9
        case inr h10 =>
          -- Conjunctions on the left can always be decomposed.
          let h11 := h10.left
          let h12 := h10.right
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- True on the right can always be proven directly.
          apply True.intro
  case inr h13 =>
    -- False on the left can always be used.
    apply False.elim h13



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_64244775163839364155182149903 : ((False ∨ (p2 ∨ (((p2 → (((True ∨ p1) → ((p2 ∨ (False ∨ p1)) ∧ (((p5 ∧ p2) → (False → p5)) → p3))) ∨ p2)) → p4) ∨ p2))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_178838402757248022313075666142 : ((((False ∨ p5) ∨ True) → ((p5 → (p3 ∧ ((p1 ∨ True) → p4))) → p3)) ∨ (((p5 ∨ (p3 → (p5 ∧ True))) ∧ (p3 ∧ (True ∨ p2))) → p5)) := by
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
    cases h6
    case inl h7 =>
      -- One of the premise coincides with the conclusion.
      exact h4
    case inr h8 =>
      -- One of the premise coincides with the conclusion.
      exact h4
  case inr h9 =>
    -- Conjunctions on the left can always be decomposed.
    let h10 := h3.left
    let h11 := h3.right
    -- Disjunctions on the left can always be decomposed.
    cases h11
    case inl h12 =>
      -- We want to use the implication h9 based on <expert-advice>. So we show its premise.
      have h13 : p3 := by
        -- One of the premise coincides with the conclusion.
        exact h10
      -- We have shown the premise of h9, we can now drive its conclusion.
      let h14 := h9 h13
      -- We need to get the left conjuct of h14 based on <expert-advice>.
      let h15 := h14.left
      -- One of the premise coincides with the conclusion.
      exact h15
    case inr h16 =>
      -- We want to use the implication h9 based on <expert-advice>. So we show its premise.
      have h17 : p3 := by
        -- One of the premise coincides with the conclusion.
        exact h10
      -- We have shown the premise of h9, we can now drive its conclusion.
      let h18 := h9 h17
      -- We need to get the left conjuct of h18 based on <expert-advice>.
      let h19 := h18.left
      -- One of the premise coincides with the conclusion.
      exact h19



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_301825483294202996556225753669 : (False ∨ ((p2 ∨ p1) ∨ ((((((True ∨ p3) → True) → p3) ∨ (((p1 → True) ∨ ((p3 ∨ ((True → p5) ∨ p5)) ∨ p4)) ∧ False)) ∨ True) ∨ True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_644459025389043291071620062283 : ((((False ∨ (p3 → ((True → (((p1 → (False ∧ ((p4 ∨ ((p3 ∧ p4) → p3)) ∨ p3))) ∨ (p4 → (p1 ∨ p1))) ∨ p1)) ∨ False))) → p3) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_217809147177969258967080381409 : (((p2 ∨ (p3 ∧ p2)) → False) → (True → ((((False ∨ ((False → p1) ∧ p1)) ∨ (p2 → True)) → (p1 ∧ True)) → ((True → (p2 ∧ p4)) → p3)))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Implications on the right can always be decomposed.
  intro h3
  -- Implications on the right can always be decomposed.
  intro h4
  -- We want to use the implication h4 based on <expert-advice>. So we show its premise.
  have h5 : True := by
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h4, we can now drive its conclusion.
  let h6 := h4 h5
  -- We need to get the left conjuct of h6 based on <expert-advice>.
  let h7 := h6.left
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h8 : (p2 ∨ (p3 ∧ p2)) := by
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- One of the premise coincides with the conclusion.
    exact h7
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h9 := h1 h8
  -- False on the left can always be used.
  apply False.elim h9



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_113521743397336892146512843228 : (((((((p4 ∨ True) → p4) ∨ p4) → (p4 ∧ (p5 ∧ False))) → ((False ∧ (((p4 → True) ∧ p3) → p3)) ∨ p1)) ∨ (False → p2)) ∨ (True ∧ p4)) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- False on the left can always be used.
  apply False.elim h1



