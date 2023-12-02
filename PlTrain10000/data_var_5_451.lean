variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_767663656543088542141500993957 : (((p5 ∧ ((p2 ∧ (((p3 ∨ (p4 ∨ (((p2 → ((p4 ∨ (False ∧ p3)) ∨ ((p5 ∧ p3) ∨ p4))) ∨ p2) ∧ False))) → p1) → False)) ∨ p3)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_158396303743205906259706303661 : (((p4 → p1) ∧ (((False ∨ ((False ∨ p2) ∨ (p3 → (p5 ∨ False)))) ∨ p2) → (p5 → (True ∧ p4)))) ∨ ((p2 ∨ (p5 → (p4 → p2))) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_92487290286982169960714082438 : (((p4 ∨ True) → (((((((False → ((p4 ∨ p4) → (True ∨ p2))) ∨ p2) → False) ∨ True) ∧ p1) → ((p1 → False) → (False → False))) ∧ False)) → p2) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h2 : (p4 ∨ True) := by
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h3 := h1 h2
  -- We need to get the right conjuct of h3 based on <expert-advice>.
  let h4 := h3.right
  -- False on the left can always be used.
  apply False.elim h4



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_651506656146033107412554366581 : (((((p2 ∧ True) ∧ (p1 ∨ (p3 ∧ ((((False → p2) ∨ ((False ∨ p2) → p2)) → p5) → (((False → False) → p2) ∧ p3))))) ∧ (p4 ∨ p5)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_739035331657887578035159567997 : ((((p3 ∧ p3) ∨ (((p5 → True) ∧ p4) → ((False ∧ (True ∧ (((True ∨ ((False ∨ False) ∨ p1)) → (p4 ∧ p2)) ∨ (p3 ∨ p5)))) ∨ True))) ∨ p4) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_134109550827252203572665455747 : ((((((p3 → (True ∨ p3)) → ((p1 ∨ p4) ∧ p1)) ∧ ((p2 → ((False → p5) ∨ False)) ∧ False)) ∧ (p2 ∧ p4)) ∨ p3) ∨ (True ∨ (p5 ∨ True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_44038470097895838171935243895 : ((((p3 ∧ (((p3 ∨ p4) ∨ p3) → ((p1 → (p5 → (p3 ∧ (((p2 ∧ False) → (p1 ∧ p5)) ∨ p3)))) → p1))) → (p2 → False)) → p4) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_138149481901442013908031049491 : ((p1 → (((True ∨ True) → (False ∨ ((p3 → (True → (p4 ∧ p4))) → (p3 ∧ ((p3 → (p3 ∨ p5)) → False))))) ∨ True)) ∨ ((False ∨ p1) ∧ False)) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_190369910335877023807039291464 : ((((False ∨ p1) ∨ (p1 ∨ ((p2 ∨ p5) ∨ True))) ∨ p5) ∨ ((p5 ∧ False) → (p3 ∧ (((p1 → ((True ∨ p1) ∨ p1)) ∨ (p4 → False)) ∧ p2)))) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
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



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_159786938457144583703345521126 : (((True ∧ (((((((True ∧ p4) → False) → ((p3 ∨ p5) ∨ p3)) → False) → p2) ∨ p4) → p1)) ∨ p2) → ((True → (p2 ∧ p5)) ∨ (p1 ∨ True))) := by
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
    -- True on the right can always be proven directly.
    apply True.intro
  case inr h5 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_159040982786215700969406378998 : ((p5 ∨ ((((True ∨ True) → ((p5 → ((p5 ∧ (p4 ∨ p2)) → False)) ∧ True)) → (True ∨ p2)) ∧ False)) ∨ ((((p2 ∨ p4) ∨ p3) ∨ True) ∨ p2)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_328641171023825259504001666401 : (True → ((((((p2 → p3) ∧ p3) ∧ (p4 ∧ (True ∨ True))) → False) ∧ (p5 ∨ p1)) → ((p4 ∧ p1) ∨ ((((p4 ∨ p2) ∨ p2) ∨ p4) ∨ True)))) := by
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
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro
  case inr h6 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_184742589916047391480586025958 : ((((p5 → (p4 ∧ False)) ∨ False) ∧ ((False → True) → (p4 ∧ p5))) ∨ (True ∨ ((p5 ∨ p1) ∨ (p2 ∧ (((False ∨ (p5 ∨ p1)) ∨ p2) → True))))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_206862617315958170788418005994 : (((((p4 → True) ∨ p3) ∧ p2) ∧ p4) → ((((((False ∧ False) ∧ (False ∧ ((p3 ∧ (p3 → p1)) ∨ (p2 → p3)))) ∧ p4) ∧ False) ∨ False) ∨ p2)) := by
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
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h5
  case inr h7 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h5



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_244799226691196610566072844243 : ((p1 ∧ p1) ∨ ((p2 ∨ ((((p4 ∧ (p2 ∨ ((p1 ∧ p4) ∧ p4))) ∧ ((True ∨ p3) ∨ p2)) ∧ (True ∧ True)) ∨ ((True ∧ p3) → p3))) ∨ p2)) := by
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
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- One of the premise coincides with the conclusion.
  exact h3



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_58488690817603591656232973425 : (((p4 ∨ p1) ∧ (p3 ∨ (((p1 → p2) ∧ ((True ∧ (False → (p3 ∧ p3))) ∧ p3)) ∧ (((p3 ∨ False) ∨ ((False ∧ p1) ∨ True)) ∧ p2)))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_641304861345337300898603994933 : (((((False → p1) ∨ ((False ∨ (p3 → p2)) ∨ (((False ∨ (((p4 ∧ (p2 → p1)) ∧ (True → p2)) ∧ p3)) → p1) ∧ (p1 ∨ p5)))) → p4) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_780350696341725784271460362339 : (((p2 ∨ ((((p4 → False) ∨ p3) ∨ ((((True → p2) ∨ (p5 ∧ p4)) ∨ p3) ∨ ((p3 → p5) ∧ p5))) → (p4 ∨ (p4 ∨ (p4 ∧ p1))))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_147417479801554846576465844232 : ((((p5 ∧ (False → (p3 → p4))) → (((p1 ∧ True) → ((p3 ∧ (False → p3)) ∨ (p4 ∨ p3))) ∧ False)) ∨ p2) ∨ ((p5 → (p2 ∧ p1)) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_669991018541062085333901180592 : (((((p4 ∨ ((p1 → (p2 → (p3 ∧ True))) → (True → True))) → ((p4 ∧ (True → True)) → ((p2 → p5) ∨ False))) ∨ ((p1 ∨ True) ∨ p3)) ∨ p1) ∧ True) := by
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
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_56170879548017667992431489414 : (((p1 ∧ (p3 ∨ (p3 ∧ False))) ∨ (p4 → (((p3 → ((((True ∧ p2) → p5) ∨ ((p2 ∨ (p2 ∨ True)) ∨ p1)) ∧ p5)) → p3) ∧ p1))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_260526953269984369681420182195 : ((p3 → p1) → (((p1 ∧ (True ∧ p5)) → (p2 ∨ (p4 ∧ (((p5 → False) → p5) → (p3 ∧ (((p2 ∨ p2) ∨ False) → (p1 ∧ True))))))) ∨ True)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_192623079104356241010286725127 : ((((p2 ∨ ((True ∨ p3) ∨ (p1 ∧ p3))) ∧ p4) → p1) → ((((((p5 → p3) ∨ p4) → p4) → p5) ∨ True) ∧ (False → ((p3 ∧ p2) ∧ p4)))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- Implications on the right can always be decomposed.
  intro h2
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- False on the left can always be used.
  apply False.elim h2
  -- False on the left can always be used.
  apply False.elim h2
  -- False on the left can always be used.
  apply False.elim h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_111676733089100208940563235863 : ((((p5 → (p5 → (((True → p5) ∨ (True ∧ (p2 → (((((False → p3) → False) ∨ True) → False) ∨ p3)))) → p2))) ∨ p3) ∨ p4) ∨ (p3 ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_172640409816979131412091977361 : (((False ∨ p1) ∧ ((((True ∧ (p2 → p5)) ∨ (p4 ∨ (True ∧ True))) ∨ False) → p2)) ∨ (((((True ∧ (p1 → p5)) ∧ p5) ∧ True) ∧ p5) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_160631790644859669278783545024 : ((((False → p1) ∨ (False → (p5 ∨ ((p5 → p3) ∨ False)))) ∨ (((p2 ∨ (p1 ∧ p5)) ∨ p4) → True)) → (((p3 ∧ False) ∧ p5) ∨ (p4 ∨ True))) := by
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
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_776616893701061521659910824997 : (((p1 ∨ ((p2 ∨ (((((p2 ∧ p2) → p5) → (p3 ∧ ((p5 → ((p2 ∨ p1) ∨ True)) ∧ (p2 ∨ p4)))) ∧ p1) ∧ (False → False))) ∨ True)) ∨ p1) ∧ True) := by
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
theorem thm_5_vars_805896490910174680748939937051 : (((p4 → ((((((((True ∨ p5) ∧ (((p4 ∨ p1) ∧ ((True ∧ p4) ∨ p1)) ∧ False)) ∧ p1) ∨ p1) ∨ p1) ∨ (p3 ∧ False)) ∨ p3) ∧ p1)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_148065843379894932661202326899 : (((p3 → ((p2 → p4) ∧ (((p4 ∧ (True → p3)) → (p5 → ((p4 → p2) → p2))) → p5))) ∨ (p5 ∧ p3)) ∨ ((p3 ∧ (p2 ∧ p3)) → p3)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- Conjunctions on the left can always be decomposed.
  let h4 := h3.left
  let h5 := h3.right
  -- One of the premise coincides with the conclusion.
  exact h5



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_62792814459219356182583551863 : ((p4 ∧ (((((True ∨ (True ∧ ((p5 → False) ∧ p4))) ∨ p4) ∧ (p2 ∨ (p2 ∨ p5))) ∨ p4) ∨ ((p4 ∧ ((p4 ∧ p3) → p2)) ∧ p4))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_174139821898271850407183054777 : ((((p5 ∨ (((p3 → True) ∨ (p3 → p4)) ∧ (p5 → p5))) ∨ False) ∨ (True ∨ True)) → (p2 ∨ (((p2 → ((False → p5) ∨ p1)) ∧ p1) → True))) := by
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
        -- True on the right can always be proven directly.
        apply True.intro
      case inr h6 =>
        -- Conjunctions on the left can always be decomposed.
        let h7 := h6.left
        let h8 := h6.right
        -- Disjunctions on the left can always be decomposed.
        cases h7
        case inl h9 =>
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- Implications on the right can always be decomposed.
          intro h10
          -- True on the right can always be proven directly.
          apply True.intro
        case inr h11 =>
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- Implications on the right can always be decomposed.
          intro h12
          -- True on the right can always be proven directly.
          apply True.intro
    case inr h13 =>
      -- False on the left can always be used.
      apply False.elim h13
  case inr h14 =>
    -- Disjunctions on the left can always be decomposed.
    cases h14
    case inl h15 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Implications on the right can always be decomposed.
      intro h16
      -- True on the right can always be proven directly.
      apply True.intro
    case inr h17 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Implications on the right can always be decomposed.
      intro h18
      -- True on the right can always be proven directly.
      apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_135649391422217007221409924419 : ((((p2 ∨ (p2 ∧ (p1 → ((p3 ∨ p1) ∨ p5)))) → (((p5 ∨ False) → p3) ∨ p5)) → ((True ∨ (True ∨ p2)) → p4)) ∨ (p5 ∨ (False → p3))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_197977257498520096945677667600 : (((p1 ∨ p3) ∧ ((p4 → (p2 → p5)) → False)) ∨ (p1 → (p4 ∨ (p4 → ((((p2 ∨ p4) ∧ (((p3 ∨ True) → p4) ∨ p4)) ∨ True) ∨ p2))))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h2
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_102975932304051986815835706878 : (((((p1 ∨ p4) ∧ ((p5 ∧ (False ∨ (p2 ∧ ((False ∧ p3) → p1)))) ∨ True)) → ((p3 ∨ p4) ∧ (False ∧ (False ∨ p2)))) ∨ True) ∧ (p2 ∨ True)) := by
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
theorem thm_5_vars_741660246514807174496595334128 : ((((True → False) ∨ ((((p4 ∨ (((False ∨ p5) ∨ p2) ∨ p1)) ∨ (((p3 → True) → True) ∧ (p2 ∧ p5))) ∨ (p2 ∨ p3)) ∨ (p5 ∨ False))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_233181077415550989623190271591 : ((p5 ∧ (p3 ∨ True)) → (False ∨ (((p5 → ((p3 → ((p1 → (((True ∨ (p5 ∧ p4)) ∧ True) ∨ False)) ∧ True)) ∨ p1)) → False) → (p4 ∨ p2)))) := by
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
    -- Implications on the right can always be decomposed.
    intro h5
    -- We want to use the implication h5 based on <expert-advice>. So we show its premise.
    have h6 : (p5 → ((p3 → ((p1 → (((True ∨ (p5 ∧ p4)) ∧ True) ∨ False)) ∧ True)) ∨ p1)) := by
      -- Implications on the right can always be decomposed.
      intro h7
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- Implications on the right can always be decomposed.
      intro h8
      -- Conjunctions on the right can always be decomposed.
      apply And.intro
      -- Implications on the right can always be decomposed.
      intro h9
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- Conjunctions on the right can always be decomposed.
      apply And.intro
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- True on the right can always be proven directly.
      apply True.intro
      -- True on the right can always be proven directly.
      apply True.intro
      -- True on the right can always be proven directly.
      apply True.intro
    -- We have shown the premise of h5, we can now drive its conclusion.
    let h10 := h5 h6
    -- False on the left can always be used.
    apply False.elim h10
  case inr h11 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h12
    -- We want to use the implication h12 based on <expert-advice>. So we show its premise.
    have h13 : (p5 → ((p3 → ((p1 → (((True ∨ (p5 ∧ p4)) ∧ True) ∨ False)) ∧ True)) ∨ p1)) := by
      -- Implications on the right can always be decomposed.
      intro h14
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- Implications on the right can always be decomposed.
      intro h15
      -- Conjunctions on the right can always be decomposed.
      apply And.intro
      -- Implications on the right can always be decomposed.
      intro h16
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- Conjunctions on the right can always be decomposed.
      apply And.intro
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- True on the right can always be proven directly.
      apply True.intro
      -- True on the right can always be proven directly.
      apply True.intro
      -- True on the right can always be proven directly.
      apply True.intro
    -- We have shown the premise of h12, we can now drive its conclusion.
    let h17 := h12 h13
    -- False on the left can always be used.
    apply False.elim h17



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_775775476684945427136693283855 : (((False ∨ (p4 ∨ ((True → (p4 ∧ p5)) ∨ (p4 → ((((True ∧ p3) ∧ (((p1 ∧ (True → p2)) → p1) ∧ p2)) ∨ p5) ∧ (p2 → p3)))))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_347339002504500854434800135920 : (p3 → (((p4 → (((p4 → True) ∧ True) → p5)) ∨ p3) ∧ ((p3 ∧ (((True → (((p1 ∨ p4) ∨ p5) ∨ (p4 ∧ p1))) → p2) → p1)) ∨ p3))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_82210433425867434633959481724 : (((((((p1 → p1) ∨ (((p4 → p3) ∨ p3) ∨ p2)) → (True ∨ ((p5 → p2) ∧ p1))) → False) ∧ p2) ∧ (p3 ∨ ((p3 ∧ p1) → p1))) → p3) := by
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
    -- One of the premise coincides with the conclusion.
    exact h6
  case inr h7 =>
    -- We want to use the implication h4 based on <expert-advice>. So we show its premise.
    have h8 : (((p1 → p1) ∨ (((p4 → p3) ∨ p3) ∨ p2)) → (True ∨ ((p5 → p2) ∧ p1))) := by
      -- Implications on the right can always be decomposed.
      intro h9
      -- Disjunctions on the left can always be decomposed.
      cases h9
      case inl h10 =>
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- True on the right can always be proven directly.
        apply True.intro
      case inr h11 =>
        -- Disjunctions on the left can always be decomposed.
        cases h11
        case inl h12 =>
          -- Disjunctions on the left can always be decomposed.
          cases h12
          case inl h13 =>
            -- Show the left disjunct based on <expert-advice>.
            apply Or.inl
            -- True on the right can always be proven directly.
            apply True.intro
          case inr h14 =>
            -- Show the left disjunct based on <expert-advice>.
            apply Or.inl
            -- True on the right can always be proven directly.
            apply True.intro
        case inr h15 =>
          -- Show the left disjunct based on <expert-advice>.
          apply Or.inl
          -- True on the right can always be proven directly.
          apply True.intro
    -- We have shown the premise of h4, we can now drive its conclusion.
    let h16 := h4 h8
    -- False on the left can always be used.
    apply False.elim h16



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_262397690378470501157724709596 : (True ∧ (((p1 ∨ p2) → (((False ∨ p4) ∧ (((((((p4 → p1) → p3) ∧ True) → ((p3 ∧ p4) ∨ p2)) → p3) → p5) ∧ False)) ∧ True)) ∨ True)) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_306399185435847657752414776009 : (p1 ∨ ((False ∧ p2) ∨ ((p1 ∨ p3) ∨ ((False ∧ (p5 ∧ ((((p3 ∧ (False → p1)) → (p5 ∨ p4)) → True) ∨ (False ∨ (p3 → p2))))) ∨ True)))) := by
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
theorem thm_5_vars_228762196842398405764044843345 : ((p3 ∨ (p1 ∧ False)) ∨ (p1 → ((p1 ∧ (p1 ∨ ((p1 ∨ (False → p3)) ∨ p1))) → (False ∨ ((p5 ∧ (p2 ∨ True)) → (True ∨ (p1 → p3))))))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
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
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h6
    -- Conjunctions on the left can always be decomposed.
    let h7 := h6.left
    let h8 := h6.right
    -- Disjunctions on the left can always be decomposed.
    cases h8
    case inl h9 =>
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- True on the right can always be proven directly.
      apply True.intro
    case inr h10 =>
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- True on the right can always be proven directly.
      apply True.intro
  case inr h11 =>
    -- Disjunctions on the left can always be decomposed.
    cases h11
    case inl h12 =>
      -- Disjunctions on the left can always be decomposed.
      cases h12
      case inl h13 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- Implications on the right can always be decomposed.
        intro h14
        -- Conjunctions on the left can always be decomposed.
        let h15 := h14.left
        let h16 := h14.right
        -- Disjunctions on the left can always be decomposed.
        cases h16
        case inl h17 =>
          -- Show the left disjunct based on <expert-advice>.
          apply Or.inl
          -- True on the right can always be proven directly.
          apply True.intro
        case inr h18 =>
          -- Show the left disjunct based on <expert-advice>.
          apply Or.inl
          -- True on the right can always be proven directly.
          apply True.intro
      case inr h19 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- Implications on the right can always be decomposed.
        intro h20
        -- Conjunctions on the left can always be decomposed.
        let h21 := h20.left
        let h22 := h20.right
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
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Implications on the right can always be decomposed.
      intro h26
      -- Conjunctions on the left can always be decomposed.
      let h27 := h26.left
      let h28 := h26.right
      -- Disjunctions on the left can always be decomposed.
      cases h28
      case inl h29 =>
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- True on the right can always be proven directly.
        apply True.intro
      case inr h30 =>
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- True on the right can always be proven directly.
        apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_692426908975717989010323323392 : (((((p4 → ((p1 ∨ True) ∧ (p5 ∨ (False → ((p1 ∧ True) ∧ False))))) → p4) ∧ (True ∨ ((p1 ∨ (p1 ∧ ((True → True) ∧ False))) → True))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_595892854692138431674887799564 : ((((((p1 → (True → (((p2 ∧ p3) ∨ p4) ∨ p2))) → p2) ∨ ((p4 ∨ (p5 ∨ ((((p4 ∨ p1) ∧ p5) ∨ p2) ∨ False))) → p2)) ∧ True) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_66437678281490432094435932185 : ((True → ((((True → p3) ∨ (((p2 → p5) ∨ ((p3 → (p3 ∨ p5)) ∧ ((p4 → p1) ∨ p3))) ∧ (False ∧ (p2 ∨ p4)))) ∨ p5) ∧ p2)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_112177907896600782188807882013 : (((p4 ∧ ((p5 ∨ (((p4 → (p5 ∧ p2)) ∨ p5) → ((p1 ∨ p3) ∧ p3))) → (((p3 → p4) → (p2 ∨ False)) → p2))) ∨ p1) ∨ (p5 → True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_172984592900458308425207882217 : ((p5 ∧ ((((False ∨ (p4 ∨ (False ∧ ((p2 ∨ p2) ∨ p5)))) → p3) ∧ p4) ∧ p4)) ∨ (((((p5 ∧ (p2 ∨ True)) ∨ True) ∨ False) → p2) → p2)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h2 : (((p5 ∧ (p2 ∨ True)) ∨ True) ∨ False) := by
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h3 := h1 h2
  -- One of the premise coincides with the conclusion.
  exact h3



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_223416955700639119516118302751 : ((True ∨ (p2 → p3)) ∧ (p2 ∨ ((p3 ∧ (((p2 ∧ p2) ∨ ((False ∨ (p3 ∨ p5)) ∧ p3)) ∧ True)) ∨ (((p3 ∨ p3) ∨ (False → p5)) ∨ False)))) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro
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
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_114484522250416150779565351031 : ((((((p3 ∨ ((p4 ∧ False) ∨ ((p4 ∧ p5) ∨ p5))) ∨ p1) ∨ p5) ∧ ((p1 ∧ p3) ∧ p3)) → ((p3 ∧ p4) ∨ (p2 ∨ p3))) ∨ (p5 → p4)) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
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
      -- Disjunctions on the left can always be decomposed.
      cases h5
      case inl h6 =>
        -- Conjunctions on the left can always be decomposed.
        let h7 := h3.left
        let h8 := h3.right
        -- Conjunctions on the left can always be decomposed.
        let h9 := h7.left
        let h10 := h7.right
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- One of the premise coincides with the conclusion.
        exact h8
      case inr h11 =>
        -- Disjunctions on the left can always be decomposed.
        cases h11
        case inl h12 =>
          -- Conjunctions on the left can always be decomposed.
          let h13 := h12.left
          let h14 := h12.right
          -- False on the left can always be used.
          apply False.elim h14
        case inr h15 =>
          -- Disjunctions on the left can always be decomposed.
          cases h15
          case inl h16 =>
            -- Conjunctions on the left can always be decomposed.
            let h17 := h16.left
            let h18 := h16.right
            -- Conjunctions on the left can always be decomposed.
            let h19 := h3.left
            let h20 := h3.right
            -- Conjunctions on the left can always be decomposed.
            let h21 := h19.left
            let h22 := h19.right
            -- Show the right disjunct based on <expert-advice>.
            apply Or.inr
            -- Show the right disjunct based on <expert-advice>.
            apply Or.inr
            -- One of the premise coincides with the conclusion.
            exact h20
          case inr h23 =>
            -- Conjunctions on the left can always be decomposed.
            let h24 := h3.left
            let h25 := h3.right
            -- Conjunctions on the left can always be decomposed.
            let h26 := h24.left
            let h27 := h24.right
            -- Show the right disjunct based on <expert-advice>.
            apply Or.inr
            -- Show the right disjunct based on <expert-advice>.
            apply Or.inr
            -- One of the premise coincides with the conclusion.
            exact h25
    case inr h28 =>
      -- Conjunctions on the left can always be decomposed.
      let h29 := h3.left
      let h30 := h3.right
      -- Conjunctions on the left can always be decomposed.
      let h31 := h29.left
      let h32 := h29.right
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- One of the premise coincides with the conclusion.
      exact h30
  case inr h33 =>
    -- Conjunctions on the left can always be decomposed.
    let h34 := h3.left
    let h35 := h3.right
    -- Conjunctions on the left can always be decomposed.
    let h36 := h34.left
    let h37 := h34.right
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h35



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_158002214350722190955761283713 : (((p3 ∨ (p1 ∧ ((True ∧ (p4 ∨ True)) → False))) → (p4 ∧ ((p1 ∨ p5) ∨ (p1 → (p5 → p1))))) ∨ (p5 → ((p5 ∧ (False ∨ False)) ∨ p5))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_355850219532076177482401606823 : (p5 → (((False ∨ ((p1 ∨ ((p2 ∨ ((p2 ∨ p1) ∨ (False → True))) ∨ (p5 ∧ p4))) → (p3 ∨ p2))) ∨ (True ∨ p3)) ∨ ((p1 → p1) ∨ p1))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_139136624023312280363409650607 : ((((True ∧ (((p3 ∧ (p3 ∨ (True ∧ False))) ∨ ((p3 ∧ True) ∨ p5)) → True)) → ((p4 ∨ p2) ∧ (p5 ∨ p3))) ∨ p3) → (p1 ∨ (p5 ∨ p3))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h2 =>
    -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
    have h3 : (True ∧ (((p3 ∧ (p3 ∨ (True ∧ False))) ∨ ((p3 ∧ True) ∨ p5)) → True)) := by
      -- Conjunctions on the right can always be decomposed.
      apply And.intro
      -- True on the right can always be proven directly.
      apply True.intro
      -- Implications on the right can always be decomposed.
      intro h4
      -- True on the right can always be proven directly.
      apply True.intro
    -- We have shown the premise of h2, we can now drive its conclusion.
    let h5 := h2 h3
    -- We need to get the right conjuct of h5 based on <expert-advice>.
    let h6 := h5.right
    -- Disjunctions on the left can always be decomposed.
    cases h6
    case inl h7 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- One of the premise coincides with the conclusion.
      exact h7
    case inr h8 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- One of the premise coincides with the conclusion.
      exact h8
  case inr h9 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h9



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_238071010189430518016186243659 : ((True ∨ p2) ∧ ((p1 ∨ (((((p4 → (p3 ∧ ((True → p4) ∧ p4))) ∨ False) ∨ (p5 ∨ (p1 → True))) → p1) ∨ p4)) ∨ (p3 ∨ (False → True)))) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_215249542484073109772501493864 : ((False ∧ ((p5 → p1) → p4)) ∨ ((((p3 → p3) ∨ p1) ∨ True) ∧ ((((p2 ∨ (True → False)) → False) ∧ (((False → p4) → p4) → False)) ∨ True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
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
theorem thm_5_vars_707002402527754689487146070958 : (((((p2 ∧ (False ∨ (True ∧ (p1 ∨ p5)))) ∨ p1) ∨ (((p5 ∨ p2) → (p1 ∨ p2)) → (True ∨ ((False ∨ (False ∧ (p5 → p5))) ∧ p1)))) ∨ p2) ∧ True) := by
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



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_185530518257667288599715359175 : ((p3 ∨ ((p1 → ((p1 ∧ p1) ∨ p4)) → (p3 ∨ (p1 ∧ p1)))) ∨ (((((p4 ∧ p4) ∧ (p5 ∨ p4)) ∨ ((p1 ∧ p2) → p2)) ∨ p4) ∨ False)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
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
theorem thm_5_vars_3225302433898108414551286347 : ((p1 ∨ False) ∨ (p5 → ((p1 ∧ ((False ∨ (((p2 → ((False → ((p3 ∧ p1) ∨ p3)) → True)) → (True ∧ True)) ∧ p5)) ∧ p1)) ∨ p5))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_136998178191364182157934182373 : (((True ∨ p4) → ((False ∨ ((p5 → False) → (((p4 ∨ p5) → (False ∨ (p5 ∧ (True ∨ (p4 → p1))))) ∧ False))) ∧ p2)) ∨ (True ∨ (p4 ∧ p1))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_39663277069827617305244997691 : (((p3 ∨ (p5 ∨ (((((False → p5) ∨ ((((p1 ∧ True) ∨ p5) → (p3 ∧ p5)) ∧ (p4 → True))) → (p1 ∨ p4)) ∨ p3) ∨ p1))) ∧ False) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_32155702754356104406396374489 : ((p1 ∨ (((p5 ∨ ((p4 → p4) → p2)) ∨ (p1 → (p4 ∧ (p3 → False)))) → ((p1 ∧ p3) ∨ ((p5 ∨ (p5 ∧ p2)) ∨ (p2 → True))))) ∧ True) := by
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
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
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
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_353410166816502744884150621906 : (p4 → (p1 ∨ ((((((p4 → (p3 ∧ ((p2 ∨ (p1 ∧ p5)) ∧ p2))) ∨ (p3 → p1)) ∨ (p3 ∨ p2)) ∨ ((p1 ∧ False) ∨ False)) ∨ True) ∨ p2))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_237906538908838958569907043215 : ((True ∨ True) ∧ ((p2 ∧ True) ∨ (p2 → ((p3 ∨ p5) → (((p5 ∨ ((p3 ∧ False) ∧ ((False ∨ p4) → p1))) ∨ (p1 ∧ (p1 → p5))) ∨ p2))))) := by
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
  -- Implications on the right can always be decomposed.
  intro h2
  -- Disjunctions on the left can always be decomposed.
  cases h2
  case inl h3 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h1
  case inr h4 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_67324010436089306270547883843 : ((p1 → (((p5 ∧ (((p4 ∧ p2) ∧ ((p3 → ((p3 ∧ (p2 ∨ ((p4 ∨ (p5 ∨ p1)) ∧ False))) ∨ p2)) ∧ p2)) ∧ p3)) ∧ p1) ∨ p1)) ∨ p2) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_808651046364534255138037950217 : (((p4 → (p1 → ((((p2 ∧ ((p2 ∨ p3) ∧ p2)) ∨ False) → (p1 ∨ ((p1 → p3) ∨ (False ∨ (p1 → (False → (p4 → False))))))) → False))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_307118999189967931991528216361 : (p1 ∨ (False ∨ (((((p3 → (False → p1)) ∧ (((True → (p2 ∨ False)) → p1) ∨ p2)) ∧ ((p2 ∨ True) → ((p4 → p4) ∨ p5))) ∨ True) ∨ p4))) := by
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
theorem thm_5_vars_54532032562523295540338420923 : ((((p2 → p3) ∨ ((p2 ∨ (p1 ∧ p1)) ∧ p3)) ∨ ((False ∨ (p3 ∧ ((p3 → (p4 ∨ (False ∧ p1))) → (p4 → (p3 ∧ False))))) → p3)) ∨ p2) := by
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
    -- One of the premise coincides with the conclusion.
    exact h4



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_197248554734706576312055641076 : (((((True → p3) → (p2 → p5)) → True) → p1) ∨ (p5 → ((False ∨ ((p3 ∧ (p1 → (p1 ∨ False))) ∨ p3)) ∨ (True ∨ ((p4 ∨ p2) → True))))) := by
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
theorem thm_5_vars_326340958102335951389971863090 : (p5 ∨ (p5 → (((((((p3 ∨ True) ∨ p5) ∨ (((p5 ∨ (True ∨ p3)) → p3) ∨ p2)) ∧ (p3 ∧ p3)) → (p2 ∧ p1)) ∨ (False ∨ True)) ∨ p2))) := by
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
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_213801713786019865896466290121 : (((p2 ∧ (p4 ∨ p3)) ∨ p5) ∨ ((False ∨ p4) ∨ ((True → ((p3 → True) ∨ p2)) ∨ (p1 → (((p5 ∧ (p4 ∧ p2)) → False) ∨ (False ∧ p4)))))) := by
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
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_185444585629879011976391184760 : ((False ∨ ((p5 ∨ p1) ∨ ((False ∨ p5) → ((p1 ∧ p5) ∧ p1)))) ∨ (((p3 → p2) → ((p5 → (p1 ∨ (True ∨ (p5 → p4)))) ∨ p1)) → True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_54479512212614609598604540343 : (((((p2 ∧ p5) ∧ (p4 ∧ False)) ∨ (p3 ∧ True)) ∨ (False → ((p1 → ((True ∨ p2) ∨ p1)) ∧ (p3 ∨ (p3 ∧ ((p5 ∨ p5) ∧ p2)))))) ∨ p5) := by
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
  -- False on the left can always be used.
  apply False.elim h1
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_172174761128622108877898688152 : ((((p5 ∨ p4) ∨ ((p1 ∧ p1) → (p5 ∨ (p3 ∧ p3)))) ∨ ((True ∧ True) ∨ p1)) ∨ (p4 ∨ (p4 → (p1 ∧ ((p3 ∨ (False ∧ True)) ∨ p5))))) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
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
theorem thm_5_vars_786431126930345904520861384400 : (((p4 ∨ ((False ∨ ((p1 ∧ True) → ((((p2 ∨ (p4 → p5)) → p4) ∨ p4) ∨ True))) ∨ ((((False ∨ p5) → (p3 ∨ p4)) ∨ False) → p4))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_765628092059812832892320214705 : (((p4 ∧ (((((p4 ∧ p4) ∧ (p1 → p1)) → (p1 → (p5 ∨ p4))) ∧ p5) ∧ ((p5 → False) ∧ (True → ((False → (p4 → p1)) ∧ p1))))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_257204535717478710273725222260 : ((p2 ∨ p2) → ((((p4 → ((p5 ∧ p4) ∨ (p5 ∨ p5))) ∧ (p3 → p1)) → (True → (p2 ∧ p1))) ∨ (p5 ∨ (True ∨ ((True ∨ False) ∨ p3))))) := by
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
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- True on the right can always be proven directly.
    apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_597598102633437620411883135243 : ((((((p4 ∨ (p2 ∧ p4)) ∧ p1) → (p3 ∧ (p3 ∧ ((p5 ∧ ((False ∨ (False ∨ (p4 → False))) ∨ (p2 → p1))) ∨ (False ∨ p4))))) ∧ False) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_309828781425670065721478922647 : (p2 ∨ ((((False → (((p3 ∧ (p5 ∧ p4)) → p3) ∧ (((p5 → False) → p4) → (p3 ∧ p2)))) ∨ p3) ∨ p1) → (((p3 → False) ∨ True) ∨ p5))) := by
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
      -- True on the right can always be proven directly.
      apply True.intro
    case inr h4 =>
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



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_452132976977924468956240057666 : (((((p1 ∧ p5) ∨ ((p2 ∧ ((False ∨ p3) ∨ True)) → (False ∨ (True → (p5 ∨ ((True ∧ True) ∨ p3)))))) ∨ (p4 ∧ ((p5 ∨ p1) ∧ p2))) ∧ True) ∧ True) := by
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
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- Disjunctions on the left can always be decomposed.
  cases h3
  case inl h4 =>
    -- Disjunctions on the left can always be decomposed.
    cases h4
    case inl h5 =>
      -- False on the left can always be used.
      apply False.elim h5
    case inr h6 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Implications on the right can always be decomposed.
      intro h7
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- One of the premise coincides with the conclusion.
      exact h6
  case inr h8 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h9
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
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_313256303591199599475529437491 : (p3 ∨ (((p4 → True) → (p5 → (p1 ∨ ((True ∧ ((p5 ∨ p3) ∨ p5)) ∧ (p4 → (((True ∧ (p3 → p1)) ∧ (p1 ∧ p3)) ∨ p5)))))) ∨ p3)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
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
  -- One of the premise coincides with the conclusion.
  exact h2
  -- Implications on the right can always be decomposed.
  intro h3
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_160098048297658903438311924212 : (((p5 ∨ (False → (True ∧ (p1 → (((((p2 ∨ p1) → p3) ∧ (p1 ∨ False)) ∧ p5) → p2))))) → p2) → (((p4 ∨ p3) ∨ p5) → (p2 ∨ p5))) := by
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
      -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
      have h5 : (p5 ∨ (False → (True ∧ (p1 → (((((p2 ∨ p1) → p3) ∧ (p1 ∨ False)) ∧ p5) → p2))))) := by
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- Implications on the right can always be decomposed.
        intro h6
        -- Conjunctions on the right can always be decomposed.
        apply And.intro
        -- True on the right can always be proven directly.
        apply True.intro
        -- Implications on the right can always be decomposed.
        intro h7
        -- Implications on the right can always be decomposed.
        intro h8
        -- Conjunctions on the left can always be decomposed.
        let h9 := h8.left
        let h10 := h8.right
        -- Conjunctions on the left can always be decomposed.
        let h11 := h9.left
        let h12 := h9.right
        -- Disjunctions on the left can always be decomposed.
        cases h12
        case inl h13 =>
          -- False on the left can always be used.
          apply False.elim h6
        case inr h14 =>
          -- False on the left can always be used.
          apply False.elim h14
      -- We have shown the premise of h1, we can now drive its conclusion.
      let h15 := h1 h5
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- One of the premise coincides with the conclusion.
      exact h15
    case inr h16 =>
      -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
      have h17 : (p5 ∨ (False → (True ∧ (p1 → (((((p2 ∨ p1) → p3) ∧ (p1 ∨ False)) ∧ p5) → p2))))) := by
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- Implications on the right can always be decomposed.
        intro h18
        -- Conjunctions on the right can always be decomposed.
        apply And.intro
        -- True on the right can always be proven directly.
        apply True.intro
        -- Implications on the right can always be decomposed.
        intro h19
        -- Implications on the right can always be decomposed.
        intro h20
        -- Conjunctions on the left can always be decomposed.
        let h21 := h20.left
        let h22 := h20.right
        -- Conjunctions on the left can always be decomposed.
        let h23 := h21.left
        let h24 := h21.right
        -- Disjunctions on the left can always be decomposed.
        cases h24
        case inl h25 =>
          -- False on the left can always be used.
          apply False.elim h18
        case inr h26 =>
          -- False on the left can always be used.
          apply False.elim h26
      -- We have shown the premise of h1, we can now drive its conclusion.
      let h27 := h1 h17
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- One of the premise coincides with the conclusion.
      exact h27
  case inr h28 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h28



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_47239508083935040652178673120 : (((((p3 ∧ (p4 → True)) ∨ ((False ∧ p3) → False)) → (((p2 ∧ (p1 ∧ True)) ∧ p4) ∧ ((p1 ∧ (p4 → p2)) ∧ p1))) ∨ (p2 → p2)) ∨ False) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_627329366499485849344210116863 : (((((((((p5 → ((p5 ∨ p2) → (((p4 ∨ (False ∧ True)) → p3) ∧ p5))) → p2) → (p4 ∨ (p1 ∧ True))) ∨ True) → p2) ∧ p3) → p2) ∨ p3) ∧ True) := by
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
  have h4 : ((((p5 → ((p5 ∨ p2) → (((p4 ∨ (False ∧ True)) → p3) ∧ p5))) → p2) → (p4 ∨ (p1 ∧ True))) ∨ True) := by
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h2, we can now drive its conclusion.
  let h5 := h2 h4
  -- One of the premise coincides with the conclusion.
  exact h5
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_42127361090792907016303683524 : ((((p1 ∨ False) → ((p5 ∧ ((((p2 ∨ False) ∨ True) ∧ p4) → (p2 ∨ ((p5 ∨ p5) ∧ (p3 ∨ (p5 → (p1 ∨ p5))))))) ∨ p5)) ∨ True) ∨ False) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_134283711011305777062497392236 : ((((p5 ∧ False) ∨ ((p2 ∨ ((p1 → False) → p5)) ∨ (False → (p1 ∨ (False → ((p3 ∧ (True ∨ p5)) ∨ p2)))))) ∨ p4) ∨ ((True ∨ p2) → p3)) := by
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
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_684902356934312511813876582784 : ((((False ∧ (p1 ∨ (False ∧ (((p4 ∧ p2) ∧ (p3 ∧ (True → p5))) ∨ (False ∨ (p1 ∧ True)))))) ∨ ((p1 ∧ p5) ∨ ((p4 ∧ p2) → False))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_150517979882313705573910394169 : ((((((p4 ∨ (False → p2)) → ((True → (p5 → p3)) ∧ p3)) → p3) → (p3 → ((p4 → p2) ∧ p5))) ∧ p3) → (p3 ∧ (p2 ∨ (p1 → p3)))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- One of the premise coincides with the conclusion.
  exact h3
  -- Conjunctions on the left can always be decomposed.
  let h4 := h1.left
  let h5 := h1.right
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h6
  -- One of the premise coincides with the conclusion.
  exact h5



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_206314468183326104711295599966 : ((p1 ∨ ((p1 ∨ p4) → (p1 → p4))) ∨ ((((False → True) ∧ ((p4 ∨ (p3 → p1)) ∧ (p5 ∨ (p4 ∨ (True ∧ p2))))) ∧ p4) ∨ (p2 ∨ True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_693924396625116967857057116102 : (((((((p5 ∨ p4) → p5) ∨ ((True → (False ∧ p4)) ∨ p2)) ∧ (p2 ∧ p2)) ∨ (((((p3 → p1) → p1) ∨ (p1 → False)) ∧ p4) ∨ True)) ∨ p2) ∧ True) := by
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
theorem thm_5_vars_543478950563021207764284494 : ((((p1 ∧ (p5 ∧ (((p2 ∨ (True ∨ p3)) ∧ (False → (p4 ∧ True))) → p3))) ∧ ((((p2 ∧ p2) → p4) ∧ True) → p3)) ∨ True) ∨ False) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_340999252733048756790795297117 : (p2 → ((True ∧ ((p4 ∨ p1) ∧ ((((True ∨ ((p2 ∧ (p4 ∧ p5)) → p4)) → p3) ∨ (False → p4)) ∧ (p3 ∨ ((False ∨ p2) → p5))))) ∨ True)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_95221391934188181379227276537 : ((p4 ∧ ((p4 ∨ ((p3 → True) ∨ p2)) → (((((p5 ∧ p3) ∨ ((p2 ∨ p1) ∨ (True → p3))) ∨ ((p3 ∧ p5) ∧ p5)) ∨ p1) ∧ False))) → False) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- We want to use the implication h3 based on <expert-advice>. So we show its premise.
  have h4 : (p4 ∨ ((p3 → True) ∨ p2)) := by
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- One of the premise coincides with the conclusion.
    exact h2
  -- We have shown the premise of h3, we can now drive its conclusion.
  let h5 := h3 h4
  -- We need to get the right conjuct of h5 based on <expert-advice>.
  let h6 := h5.right
  -- False on the left can always be used.
  apply False.elim h6



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_774556216455265756082595860430 : (((False ∨ (((p5 ∨ ((p1 ∨ ((p4 → p3) ∧ p5)) ∨ (p2 ∧ p4))) ∧ True) ∧ (p5 → (((False → (p2 ∧ p5)) ∧ (False → False)) ∨ False)))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_67996923992783692735330893726 : ((p2 → ((p1 ∨ p4) ∨ ((p4 ∧ (((((p5 ∧ ((p2 ∧ p5) → (p5 ∧ p4))) ∨ (p5 ∧ p4)) ∧ True) → p4) → p3)) ∨ (False → p4)))) ∨ p5) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h2
  -- False on the left can always be used.
  apply False.elim h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_148714310398216907562253870134 : ((((p5 → (p2 → p1)) ∨ (p4 → (False ∧ p5))) → ((((p2 → p2) → (p1 ∧ p5)) ∨ (False ∧ False)) → p5)) ∨ ((p1 ∧ p3) ∨ (p5 → p5))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_305761852983387251868030692999 : (p1 ∨ (((((False ∧ False) ∨ p5) ∧ (p5 ∨ True)) ∨ p4) ∨ (p3 → (True ∨ ((True → (p3 → (((p1 ∧ p2) → p5) ∨ (p2 → p3)))) ∨ p3))))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_329703572479719595490597039123 : (True → ((True → False) → ((((p4 ∧ False) → (p4 ∧ p5)) ∧ ((p2 → (p1 ∨ p1)) → (p3 ∧ ((True → (p5 ∧ (p1 → p5))) → p3)))) ∨ p4))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
  have h3 : True := by
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h2, we can now drive its conclusion.
  let h4 := h2 h3
  -- False on the left can always be used.
  apply False.elim h4



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_244676216628616984438955721657 : ((p1 ∧ True) ∨ (((p3 ∨ ((True ∨ True) ∧ p1)) ∨ (p1 ∨ (((((True ∨ (True ∨ p3)) → True) → p1) ∨ (p2 ∨ p5)) ∨ (p2 → True)))) ∨ p5)) := by
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
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_655424265813604774630998912610 : (((((((False ∨ False) ∨ p3) ∧ ((False ∨ (((False → p1) ∧ (p2 ∨ False)) ∧ (p2 ∨ p3))) ∧ (True → p4))) ∨ (False ∨ True)) ∨ (False ∨ p2)) ∨ False) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
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
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_190968659852605838969857708021 : (((((False ∧ False) ∧ True) ∧ p4) ∨ ((p5 ∧ p4) ∨ p1)) ∨ ((((p1 → p5) ∧ p5) ∧ (False → ((True → True) → ((p1 → p5) → p4)))) → p5)) := by
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
  exact h5



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_217496506808990778013359177516 : ((((False ∨ p2) ∧ p4) → p1) → ((((p1 ∧ (p3 → (True ∨ (p2 ∨ p1)))) → (p4 → ((False ∧ p1) ∧ p2))) → p5) ∨ (True ∨ (p3 ∧ p3)))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



