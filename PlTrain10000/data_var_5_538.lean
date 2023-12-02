variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_738536403287694779216527229095 : ((((p1 ∧ p4) ∨ (p2 → ((((p4 ∧ (p2 ∧ (True → True))) ∨ (p3 ∧ False)) ∨ (p4 ∨ True)) ∨ ((False → (p2 → False)) → (p4 ∧ False))))) ∨ p2) ∧ True) := by
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
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_197200309318802023725239617260 : ((((((False ∨ p1) ∨ False) ∧ p4) ∨ p1) → p4) ∨ ((p4 ∧ ((((p3 ∨ p3) ∧ False) ∧ (p3 ∧ p4)) ∨ (p4 ∨ (True ∨ (p3 → p1))))) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_172080033708543693435853852955 : ((((False ∧ ((p5 ∧ True) ∧ False)) ∨ ((p4 → (p2 ∧ True)) ∨ p1)) → (p4 → p5)) ∨ ((p2 ∧ p4) ∨ ((True ∨ True) ∨ ((p1 ∨ p5) → False)))) := by
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
theorem thm_5_vars_185214456874101670806018031306 : ((True ∧ (p3 → ((p5 ∧ p4) ∨ ((p4 ∧ (p5 ∨ p5)) ∨ True)))) ∨ (True ∨ ((p5 ∨ (True ∨ p5)) ∧ ((False → (p2 → (True ∧ p2))) ∨ p5)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_173778170272523187019131813345 : ((((p4 → p1) ∧ (((p4 ∧ p2) ∨ (False → True)) ∧ (p2 ∨ (False ∧ p3)))) ∨ p2) → (p1 → (((p2 ∧ False) ∧ p2) ∨ ((p1 ∧ p1) ∨ False)))) := by
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
      cases h7
      case inl h11 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- Conjunctions on the right can always be decomposed.
        apply And.intro
        -- One of the premise coincides with the conclusion.
        exact h2
        -- One of the premise coincides with the conclusion.
        exact h2
      case inr h12 =>
        -- Conjunctions on the left can always be decomposed.
        let h13 := h12.left
        let h14 := h12.right
        -- False on the left can always be used.
        apply False.elim h13
    case inr h15 =>
      -- Disjunctions on the left can always be decomposed.
      cases h7
      case inl h16 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- Conjunctions on the right can always be decomposed.
        apply And.intro
        -- One of the premise coincides with the conclusion.
        exact h2
        -- One of the premise coincides with the conclusion.
        exact h2
      case inr h17 =>
        -- Conjunctions on the left can always be decomposed.
        let h18 := h17.left
        let h19 := h17.right
        -- False on the left can always be used.
        apply False.elim h18
  case inr h20 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Conjunctions on the right can always be decomposed.
    apply And.intro
    -- One of the premise coincides with the conclusion.
    exact h2
    -- One of the premise coincides with the conclusion.
    exact h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_309193827443142950917126018942 : (p2 ∨ ((((True ∧ ((((p2 ∧ p4) ∨ True) ∨ (p4 → p3)) ∧ p5)) ∨ ((((p1 → p1) ∧ (p3 → p3)) ∧ False) ∨ True)) ∨ True) ∧ (p1 ∨ True))) := by
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
theorem thm_5_vars_55326397257168153423491273395 : (((p3 ∨ ((p4 ∧ p4) ∨ (p2 ∨ p3))) ∨ (((p5 → (p2 → (p3 ∨ p4))) → (True ∨ (p3 ∨ False))) → (((True ∨ p4) ∨ p1) ∨ p1))) ∨ p4) := by
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
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_85286985550893295990924904420 : (((((False ∨ ((((True ∨ True) → p3) ∧ p3) → True)) → p3) ∧ p3) ∧ (p2 → (p3 ∧ (((p4 ∨ p5) ∨ ((False ∨ p5) ∨ p1)) → p4)))) → p3) := by
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
theorem thm_5_vars_208532056676986875721195753530 : (((True ∨ p4) → ((p3 ∧ p2) ∧ False)) → (((True ∧ p2) → (((((p1 ∨ p4) → ((p1 ∧ p4) ∧ True)) ∧ p5) ∧ p3) ∨ p5)) ∨ (True → True))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h2
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_140798334707449248105539878023 : ((((False → p4) → ((p2 ∧ ((p3 ∧ p4) ∧ p3)) ∧ (p1 ∨ p5))) ∧ (((True ∨ ((p2 ∧ p1) ∧ p2)) ∨ p1) → p3)) → (p3 ∧ (p2 → p2))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- We want to use the implication h3 based on <expert-advice>. So we show its premise.
  have h4 : ((True ∨ ((p2 ∧ p1) ∧ p2)) ∨ p1) := by
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h3, we can now drive its conclusion.
  let h5 := h3 h4
  -- One of the premise coincides with the conclusion.
  exact h5
  -- Implications on the right can always be decomposed.
  intro h6
  -- Conjunctions on the left can always be decomposed.
  let h7 := h1.left
  let h8 := h1.right
  -- One of the premise coincides with the conclusion.
  exact h6



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_115218172079991343075676917155 : (((p1 → ((p1 → (p2 ∨ True)) ∧ ((p4 ∨ p3) → True))) ∧ (((((p5 ∧ p2) ∨ (False ∨ (p2 ∨ p2))) → p3) → False) ∨ True)) ∨ (True → p5)) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h2
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- Implications on the right can always be decomposed.
  intro h3
  -- True on the right can always be proven directly.
  apply True.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_307847195561376235153744468651 : (p1 ∨ (p5 → ((((((p3 ∨ p2) → ((p5 ∨ (False ∧ (((p5 ∨ True) ∨ False) → p4))) → p4)) → p1) ∨ ((p2 → p1) ∨ p3)) ∧ False) ∨ p5))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_258025696006911937898061439456 : ((p4 ∨ p1) → (p3 → ((((True → (p1 ∧ p2)) ∨ p4) → ((False → (p2 ∨ (p1 ∧ p1))) → (((p1 → True) ∧ p1) ∧ p1))) ∨ (True ∨ p4)))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h3 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- True on the right can always be proven directly.
    apply True.intro
  case inr h4 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- True on the right can always be proven directly.
    apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_52135565471092288504613681674 : ((((p5 → (((((p4 ∧ (p2 ∧ False)) ∨ True) → p4) ∧ p5) → p3)) ∧ (p4 ∨ p5)) → ((p2 → (p4 ∧ (p2 → (p2 → p2)))) ∧ False)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_231696047616614002299036901693 : (((p1 ∧ p5) → True) → ((p4 ∨ (((True → ((p4 → p1) → (p1 ∧ p3))) ∨ (p5 → p4)) → ((True ∨ (p3 ∨ (False → p1))) → p3))) ∨ True)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_112270277128570624053068666352 : (((p5 ∨ (p2 ∨ ((((((p4 ∧ p1) ∨ ((((p4 → p2) ∧ (p3 → p5)) → p3) ∧ p2)) → p2) ∧ p3) ∧ False) ∨ p4))) ∨ p5) ∨ (False → p1)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_179064798425155598884507649410 : ((True ∧ ((((p4 ∨ (p4 ∧ (False → p1))) → (False ∧ p3)) → p5) → p3)) ∨ (p4 → ((True ∧ ((p1 → True) ∨ (p4 ∨ p1))) ∨ (p3 ∨ p3)))) := by
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
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_345446610304213662028981341325 : (p3 → ((((((False ∨ p1) ∨ (False ∧ p4)) ∧ p5) ∨ ((p5 ∨ False) → ((False ∨ ((p2 ∧ p3) → p3)) → (False ∨ p3)))) ∨ (p3 → p3)) ∨ p4)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h2
  -- One of the premise coincides with the conclusion.
  exact h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_179316725676752935888447039532 : ((False ∨ (p2 ∨ (((False → ((p5 → p2) ∨ False)) ∧ p1) ∧ (p3 ∧ p2)))) ∨ (True → (((True → (False → p5)) ∧ p5) ∨ ((p4 ∨ True) ∨ False)))) := by
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
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_669276029515471976974915778008 : (((((p2 → (((p4 ∧ p1) ∧ (p3 → True)) ∨ ((((p4 ∧ (p1 ∧ (p1 → p4))) ∧ p4) ∨ p1) → True))) → False) ∨ ((p4 ∧ True) ∨ True)) ∨ p3) ∧ True) := by
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
theorem thm_5_vars_206011507889348202287707465746 : ((p2 ∧ ((p3 ∧ (p3 ∧ p2)) ∧ p3)) ∨ ((p3 ∨ ((p2 ∨ (p1 ∧ ((True → (p3 → ((True ∨ (p3 ∨ True)) ∧ p4))) ∨ p2))) → p3)) → True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_264269308380461111142905700148 : (True ∧ ((((True ∧ p3) → p4) → (p4 → p2)) ∨ ((((True → p3) ∨ False) → (p1 ∨ p2)) ∨ (True → (True ∨ (p3 → ((False ∨ p5) ∨ False))))))) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- True on the right can always be proven directly.
  apply True.intro
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
theorem thm_5_vars_115471587431616790216018433910 : (((p3 ∨ ((((p4 → p5) ∨ p1) → p3) ∧ p2)) ∨ ((p1 ∧ ((p1 ∧ p1) → True)) ∧ (((p3 ∨ p3) ∨ p1) → (p4 → p3)))) ∨ (False → p1)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_345523537920345685249179450414 : (p3 → (((True ∨ ((p2 ∧ ((p2 ∧ False) ∧ (p5 ∨ (p5 → p5)))) → p3)) → ((((True → (p1 → p3)) ∧ p3) → p1) ∨ (p3 ∧ p2))) ∨ p3)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_299648795126986343930962153826 : (False ∨ ((((((p1 ∨ (p5 ∨ (p1 ∨ (p3 ∨ p3)))) ∨ (((p4 ∨ True) ∨ (p5 ∧ False)) → True)) → (False ∨ p5)) → p5) → (False ∧ p4)) → False)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h2 : ((((p1 ∨ (p5 ∨ (p1 ∨ (p3 ∨ p3)))) ∨ (((p4 ∨ True) ∨ (p5 ∧ False)) → True)) → (False ∨ p5)) → p5) := by
    -- Implications on the right can always be decomposed.
    intro h3
    -- We want to use the implication h3 based on <expert-advice>. So we show its premise.
    have h4 : ((p1 ∨ (p5 ∨ (p1 ∨ (p3 ∨ p3)))) ∨ (((p4 ∨ True) ∨ (p5 ∧ False)) → True)) := by
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Implications on the right can always be decomposed.
      intro h5
      -- True on the right can always be proven directly.
      apply True.intro
    -- We have shown the premise of h3, we can now drive its conclusion.
    let h6 := h3 h4
    -- Disjunctions on the left can always be decomposed.
    cases h6
    case inl h7 =>
      -- False on the left can always be used.
      apply False.elim h7
    case inr h8 =>
      -- One of the premise coincides with the conclusion.
      exact h8
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h9 := h1 h2
  -- We need to get the left conjuct of h9 based on <expert-advice>.
  let h10 := h9.left
  -- False on the left can always be used.
  apply False.elim h10



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_46881384796184936914651380348 : ((((((p5 ∨ (True → p2)) ∨ (((True ∧ p5) ∧ (p2 → p1)) ∨ ((((p1 → p5) → p1) → p5) ∧ p1))) ∧ p2) ∨ p5) ∨ (False → p1)) ∨ p2) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_875827189831859162597701789 : ((True → ((p3 → (False → p1)) ∧ ((((p5 → p3) ∧ True) ∧ (((p2 ∨ (p3 ∧ (p4 ∨ (False ∧ p2)))) ∧ True) ∧ False)) ∨ True))) ∨ p3) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
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
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_118574478940162333780601594074 : ((p4 ∨ (((((p1 ∧ (((((p4 → (True → p2)) ∧ True) → True) → (p4 ∧ p1)) ∧ False)) ∧ p1) ∧ p1) ∧ (True ∨ p1)) ∨ True)) ∨ (p1 → p4)) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_808157323913607218234854041025 : (((p4 → (p2 ∧ ((True ∧ p4) → ((((False ∧ True) ∧ p3) → (False ∧ p2)) → (p1 ∧ ((((p4 → (True → p5)) ∨ False) ∧ p1) ∨ p3)))))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_206658979118431417858079558986 : ((p1 → (p2 → (p3 ∨ (False ∧ p4)))) ∨ ((((p2 → ((True ∧ False) ∧ (p2 → p4))) ∧ p2) ∨ (p3 → p2)) ∨ ((False ∧ (p5 ∧ p2)) → p2))) := by
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
theorem thm_5_vars_136133353560859008163250896446 : ((((((p3 ∧ False) ∨ (p1 ∨ p1)) ∨ p4) ∨ p4) → ((False ∨ (p1 ∨ (p5 → (False → (p4 ∧ p2))))) ∨ (p3 ∧ p2))) ∨ (p4 ∨ (True ∧ p4))) := by
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
        -- Conjunctions on the left can always be decomposed.
        let h5 := h4.left
        let h6 := h4.right
        -- False on the left can always be used.
        apply False.elim h6
      case inr h7 =>
        -- Disjunctions on the left can always be decomposed.
        cases h7
        case inl h8 =>
          -- Show the left disjunct based on <expert-advice>.
          apply Or.inl
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- Show the left disjunct based on <expert-advice>.
          apply Or.inl
          -- One of the premise coincides with the conclusion.
          exact h8
        case inr h9 =>
          -- Show the left disjunct based on <expert-advice>.
          apply Or.inl
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- Show the left disjunct based on <expert-advice>.
          apply Or.inl
          -- One of the premise coincides with the conclusion.
          exact h9
    case inr h10 =>
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Implications on the right can always be decomposed.
      intro h11
      -- Implications on the right can always be decomposed.
      intro h12
      -- Conjunctions on the right can always be decomposed.
      apply And.intro
      -- False on the left can always be used.
      apply False.elim h12
      -- False on the left can always be used.
      apply False.elim h12
  case inr h13 =>
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h14
    -- Implications on the right can always be decomposed.
    intro h15
    -- Conjunctions on the right can always be decomposed.
    apply And.intro
    -- False on the left can always be used.
    apply False.elim h15
    -- False on the left can always be used.
    apply False.elim h15



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_172329382326303662766827095144 : ((((p2 ∧ (True ∧ (p1 → True))) → False) ∧ ((((p5 → p2) → False) → p3) → p4)) ∨ (True → (True ∧ (((p2 ∨ p3) → (True ∨ p4)) ∨ p2)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h2
  -- Disjunctions on the left can always be decomposed.
  cases h2
  case inl h3 =>
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- True on the right can always be proven directly.
    apply True.intro
  case inr h4 =>
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- True on the right can always be proven directly.
    apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_230635884759719231495795487544 : (((p2 → p5) ∧ p2) → ((((p2 ∧ (p4 → p3)) ∨ (p1 → p5)) → ((p3 ∨ (p3 → (True → p2))) ∨ True)) ∨ (((p3 ∧ p4) ∧ p3) ∨ p1))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h4
  -- Disjunctions on the left can always be decomposed.
  cases h4
  case inl h5 =>
    -- Conjunctions on the left can always be decomposed.
    let h6 := h5.left
    let h7 := h5.right
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro
  case inr h8 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_693955185083842789497018237511 : (((((((((False → p5) ∨ True) ∨ (False ∧ p3)) ∧ p4) → False) ∨ (True → p5)) ∨ (False ∧ ((False ∧ (p3 ∧ p5)) ∨ ((p2 ∧ False) ∧ p1)))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_111189625958554767404020448383 : (((((True → p1) ∧ True) ∧ (p1 ∧ ((((((p5 ∧ p2) ∧ (p5 → p3)) → p1) ∨ p5) ∨ ((p4 ∧ p2) ∧ False)) ∨ p5))) ∧ p2) ∨ (p4 ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_259756392962328292960267294584 : ((p1 → p2) → ((p4 ∨ (((p3 → (p2 ∨ False)) ∨ (False → p3)) ∨ (False ∨ (p2 ∧ p5)))) ∧ (p5 → (p2 ∨ (p4 → (p2 ∨ (p3 → p4))))))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h2
  -- False on the left can always be used.
  apply False.elim h2
  -- Implications on the right can always be decomposed.
  intro h3
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h4
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h5
  -- One of the premise coincides with the conclusion.
  exact h4



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_66055169538400120589339952078 : ((p5 ∨ ((((p3 ∧ (p3 → (p5 ∧ True))) ∧ ((p1 → ((((True ∨ p5) → p3) ∨ (p2 ∧ p1)) ∨ p5)) ∧ (p3 ∨ False))) → p5) ∨ False)) ∨ p3) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
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
  let h4 := h2.left
  let h5 := h2.right
  -- Conjunctions on the left can always be decomposed.
  let h6 := h3.left
  let h7 := h3.right
  -- Disjunctions on the left can always be decomposed.
  cases h7
  case inl h8 =>
    -- We want to use the implication h5 based on <expert-advice>. So we show its premise.
    have h9 : p3 := by
      -- One of the premise coincides with the conclusion.
      exact h8
    -- We have shown the premise of h5, we can now drive its conclusion.
    let h10 := h5 h9
    -- We need to get the left conjuct of h10 based on <expert-advice>.
    let h11 := h10.left
    -- One of the premise coincides with the conclusion.
    exact h11
  case inr h12 =>
    -- False on the left can always be used.
    apply False.elim h12



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_98997634994534826729310687386 : ((True → ((((p5 ∧ p5) ∨ ((False ∧ p2) ∨ p2)) ∧ ((True ∨ False) ∨ p4)) ∧ ((((p3 → (False ∨ p2)) ∨ True) ∨ (p3 ∨ p1)) → p4))) → p4) := by
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
  -- We want to use the implication h4 based on <expert-advice>. So we show its premise.
  have h5 : (((p3 → (False ∨ p2)) ∨ True) ∨ (p3 ∨ p1)) := by
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h4, we can now drive its conclusion.
  let h6 := h4 h5
  -- One of the premise coincides with the conclusion.
  exact h6



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_713541750836341648021015149900 : ((((p5 → (p1 → ((p3 → p5) ∧ False))) ∨ (((p2 ∨ p4) ∨ (p4 ∧ False)) ∨ (((p3 ∧ p5) → p1) ∧ (p3 ∨ ((p5 → False) ∨ p1))))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_337062719603996275678343592987 : (p1 → (((((True ∨ p1) ∨ p2) → ((((((False → p2) → p1) ∨ (((p2 → p2) ∨ True) ∧ p4)) ∨ p5) ∧ True) → p1)) → p4) ∨ (p1 ∨ p4))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_463436077141932103385060163874 : ((((False ∧ ((p3 ∧ (False ∧ False)) ∧ (False ∨ (((p3 ∨ p4) ∧ (False → True)) → p2)))) ∨ (((False ∧ (p2 ∧ p5)) → True) ∧ (p1 → p1))) ∧ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro
  -- Implications on the right can always be decomposed.
  intro h2
  -- One of the premise coincides with the conclusion.
  exact h2
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_357431995658754705754224815171 : (p5 → ((p4 ∨ p1) → (p3 ∨ ((p2 → ((True → ((p5 → (True ∧ ((True → False) ∧ p3))) ∧ ((p5 ∧ p3) → p4))) → p3)) ∨ (p3 ∨ p4))))) := by
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
    exact h3
  case inr h4 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Implications on the right can always be decomposed.
    intro h5
    -- Implications on the right can always be decomposed.
    intro h6
    -- We want to use the implication h6 based on <expert-advice>. So we show its premise.
    have h7 : True := by
      -- True on the right can always be proven directly.
      apply True.intro
    -- We have shown the premise of h6, we can now drive its conclusion.
    let h8 := h6 h7
    -- We need to get the left conjuct of h8 based on <expert-advice>.
    let h9 := h8.left
    -- We want to use the implication h9 based on <expert-advice>. So we show its premise.
    have h10 : p5 := by
      -- One of the premise coincides with the conclusion.
      exact h1
    -- We have shown the premise of h9, we can now drive its conclusion.
    let h11 := h9 h10
    -- We need to get the right conjuct of h11 based on <expert-advice>.
    let h12 := h11.right
    -- We need to get the left conjuct of h12 based on <expert-advice>.
    let h13 := h12.left
    -- We want to use the implication h13 based on <expert-advice>. So we show its premise.
    have h14 : True := by
      -- True on the right can always be proven directly.
      apply True.intro
    -- We have shown the premise of h13, we can now drive its conclusion.
    let h15 := h13 h14
    -- False on the left can always be used.
    apply False.elim h15



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_234750368758061281853217330248 : ((p4 → (p2 → False)) → ((((True ∨ ((True ∨ ((p2 → p2) ∨ (p2 → p3))) ∨ p1)) → True) → (p1 ∨ (p3 ∧ p2))) ∨ ((True ∧ p1) → p1))) := by
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
  exact h4



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_618737519309667849157315167387 : ((((((p4 ∧ True) → p3) ∧ ((((False ∨ (p5 ∨ False)) ∧ p4) → ((p4 → p3) → (True → ((False → True) ∨ (p5 → p2))))) → p1)) ∨ False) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_634245024636307924631334450369 : (((((p5 ∧ ((True ∧ ((True ∧ (p3 ∨ ((True ∧ p1) ∨ ((p5 ∨ True) ∨ (p2 → p2))))) ∨ False)) ∧ (p4 ∨ p2))) → (p1 ∧ p4)) → p3) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_198356240602199771090825148311 : ((p2 ∧ (False ∨ ((False ∧ True) ∧ (False ∨ True)))) ∨ (p5 ∨ ((True ∨ (True ∨ (p5 ∧ ((True ∧ ((p1 ∨ p5) ∧ (p1 → p1))) ∨ p1)))) ∨ p1))) := by
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
theorem thm_5_vars_746195850171071950747971881308 : ((((p1 ∨ p3) → ((p3 ∨ ((p2 → (p2 → p4)) ∨ p5)) ∧ (p5 ∧ (((p2 ∨ p4) → (((p5 → p2) ∧ True) → p3)) ∨ (p5 ∨ p1))))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_52700850765887054191674325981 : (((p3 → (((((False ∧ p5) → p1) ∨ True) → ((p4 ∧ p4) ∧ p5)) ∨ p3)) ∨ ((p2 ∧ (p3 ∧ (True ∨ p2))) → (p1 → (False → p1)))) ∨ False) := by
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
  -- False on the left can always be used.
  apply False.elim h3



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_172741619109958852528800911426 : (((True ∧ True) → (((p4 ∧ ((p1 → (p5 ∨ p4)) ∨ p5)) ∨ p3) ∨ (False → p3))) ∨ ((((p5 → p4) ∧ p4) ∧ (p3 ∨ p2)) ∧ (p5 ∨ p5))) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h4
  -- False on the left can always be used.
  apply False.elim h4



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_160514124317110526068230493740 : (((p5 ∨ ((p3 ∧ ((p1 ∧ False) ∧ (p5 ∨ False))) → (p1 ∧ p5))) ∧ (((p4 ∨ True) ∨ True) ∨ p4)) → ((((False ∨ True) → p1) ∧ False) ∨ True)) := by
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
      -- Disjunctions on the left can always be decomposed.
      cases h5
      case inl h6 =>
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
    case inr h10 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- True on the right can always be proven directly.
      apply True.intro
  case inr h11 =>
    -- Disjunctions on the left can always be decomposed.
    cases h3
    case inl h12 =>
      -- Disjunctions on the left can always be decomposed.
      cases h12
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
theorem thm_5_vars_697584781264692723689543506768 : ((((p1 ∨ ((p5 ∧ ((p3 ∧ (p1 ∨ (p2 ∧ False))) → p4)) ∨ True)) ∧ (((p5 ∧ (False ∧ (p2 ∧ (False ∧ p5)))) ∧ (p5 → p3)) ∨ p5)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_115422278082575685832939234569 : ((((p2 → ((p1 ∨ (p3 ∧ p4)) ∨ p3)) ∧ False) ∨ ((p5 → p2) ∧ (p2 ∧ ((p3 ∨ (True ∧ (False → (p2 → p2)))) ∨ p4)))) ∨ (False → p4)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_762410908759569971576424482733 : (((p3 ∧ ((p5 ∨ ((False ∨ (p3 ∧ p5)) → (((False ∧ (p2 ∨ (p2 → p5))) → (p4 ∧ p4)) → (p5 ∨ p3)))) → (p4 ∨ (p1 ∧ p2)))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_55999756008142311944699947278 : ((((p4 → (p1 → p1)) ∧ p3) ∨ (((((True → (p3 → ((((p1 → p3) ∧ p4) ∨ p3) ∨ True))) ∧ p5) ∨ True) → p1) ∨ (p3 → p3))) ∨ p3) := by
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
theorem thm_5_vars_158986508250408703348559413376 : ((p3 ∨ (((p2 ∨ True) ∨ p5) ∧ ((p4 ∨ ((((p5 → p1) → p1) ∨ (p1 → p3)) ∨ p5)) ∧ p1))) ∨ ((p4 ∨ (p2 ∨ (True ∨ p2))) ∨ p2)) := by
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
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_66203087505809271151696981293 : ((p5 ∨ ((p2 ∨ ((p3 → (p5 ∨ ((p1 → (p3 ∨ p2)) → (p4 → p2)))) ∨ p2)) ∧ ((p4 ∨ (p3 → (False → False))) ∧ (p4 ∨ p1)))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_61427874969816678730103415264 : ((p1 ∧ ((((((p4 ∨ (p4 → p4)) ∨ (p2 ∨ True)) → (p1 ∧ p2)) ∨ False) → ((p1 ∨ p2) ∨ (p3 ∧ ((False ∨ p1) → p5)))) → p3)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_172867071258791134265238070309 : ((p1 ∧ ((p3 ∨ (((True ∧ p5) ∨ p5) → ((p1 ∧ p5) → (p2 → p5)))) ∧ False)) ∨ (p2 ∨ ((((True ∧ False) ∧ True) ∧ False) ∨ (False → p2)))) := by
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
theorem thm_5_vars_232056701676867308574735042036 : (((p4 ∨ True) → False) → ((((((p3 ∧ False) → p5) → (p2 ∧ p3)) ∧ p3) ∧ (False ∧ (((True → ((p1 → p4) → p4)) → p4) ∨ p5))) ∨ p3)) := by
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
  -- False on the left can always be used.
  apply False.elim h3



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_53330821777799610709808525200 : (((((p2 ∨ ((p2 → ((False → False) → p5)) ∨ False)) ∧ p4) ∧ p1) → ((True ∨ p3) → ((p2 → (p5 ∧ (p3 ∧ (p2 ∧ p1)))) → p3))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_705904567184393613230646059489 : ((((((p3 → p3) → True) ∨ (p2 ∨ (p3 ∨ p2))) ∧ ((p5 ∧ ((p4 → p5) → (((p5 ∧ True) ∨ p2) ∧ (p4 ∧ True)))) ∨ (True ∨ p1))) ∨ False) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
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
theorem thm_5_vars_178640949451422351152117666330 : (((True ∨ (False ∨ (p2 → (True → p2)))) → (p4 ∧ ((p5 ∧ p1) ∨ False))) ∨ (((((p1 → p5) ∨ False) ∧ (p5 ∨ (p2 ∧ p5))) ∧ p4) → p4)) := by
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
  cases h4
  case inl h6 =>
    -- Disjunctions on the left can always be decomposed.
    cases h5
    case inl h7 =>
      -- One of the premise coincides with the conclusion.
      exact h3
    case inr h8 =>
      -- Conjunctions on the left can always be decomposed.
      let h9 := h8.left
      let h10 := h8.right
      -- One of the premise coincides with the conclusion.
      exact h3
  case inr h11 =>
    -- False on the left can always be used.
    apply False.elim h11



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_811164329402300065397682386091 : (((p5 → (p3 ∧ (((((p1 → (True ∨ p3)) ∨ p4) ∧ (p5 → p1)) ∧ p1) ∧ ((((p3 → p1) → (p5 → p2)) → (p2 ∨ p1)) ∨ p4)))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_608695000774991517881288381692 : (((((((True → (((True ∧ p4) → p1) ∨ (p2 → (((p5 ∨ (p5 ∨ True)) → p3) ∧ (p2 → True))))) ∨ True) → (p4 ∧ p4)) ∨ p1) ∨ True) ∨ p2) ∧ True) := by
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
theorem thm_5_vars_226525949035592175730253035896 : (((p3 → p2) ∨ p3) ∨ (((((p2 → (((p5 ∧ True) ∧ p1) ∧ True)) ∧ (p2 ∧ (False ∨ p3))) ∨ (True ∨ (p4 ∧ False))) ∨ (True ∨ p3)) ∨ p2)) := by
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
theorem thm_5_vars_342071080731244589546301386392 : (p2 → (((False ∧ p4) → ((p2 ∧ p4) → (p5 ∧ (p2 ∧ (p3 ∨ ((p4 → p1) ∧ (False ∧ (p3 ∨ (p5 ∨ False))))))))) → (p5 → (p1 ∨ p2)))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Implications on the right can always be decomposed.
  intro h3
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_613167467593731453287718193024 : ((((((((p3 ∧ (p2 → (((p3 ∧ p3) ∧ (p3 ∨ (p5 ∧ p3))) ∧ p4))) ∨ p5) ∧ (p5 ∧ p3)) → (p1 ∨ p2)) → (p2 → p5)) ∨ True) ∨ False) ∧ True) := by
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
theorem thm_5_vars_1799658201466123390342189670 : (((p2 ∧ p3) ∧ (((((p5 ∨ True) → p1) → (((False → False) → (p2 ∧ p3)) ∧ p5)) ∧ p5) ∨ (p5 ∨ p3))) ∨ (p1 → (False → p3))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- False on the left can always be used.
  apply False.elim h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_166494604508093512300576184033 : ((p3 ∨ (p1 ∧ ((p4 ∧ (p4 → (p3 ∨ ((p3 ∨ (False → (p3 → True))) ∨ p3)))) ∨ p3))) ∨ (True → ((True ∧ ((False ∨ True) ∨ p1)) ∨ p5))) := by
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
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_172347492958385426630405123117 : (((p2 → (p5 ∨ (p2 ∨ (True ∨ p4)))) ∧ (((False ∧ False) ∧ (p1 ∧ p1)) ∨ p1)) ∨ (p4 ∨ (False ∨ ((p4 → p1) ∨ ((p2 ∧ p3) → p2))))) := by
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
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- One of the premise coincides with the conclusion.
  exact h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_259394827588549576568543837024 : ((False → p3) → (((p1 → (True → ((True ∧ p1) → (p4 ∨ p4)))) → p1) ∨ (p5 → (((False ∧ True) → p2) ∧ (False → (p2 ∧ (p5 → p1))))))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h2
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h3
  -- Conjunctions on the left can always be decomposed.
  let h4 := h3.left
  let h5 := h3.right
  -- False on the left can always be used.
  apply False.elim h4
  -- Implications on the right can always be decomposed.
  intro h6
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- False on the left can always be used.
  apply False.elim h6
  -- Implications on the right can always be decomposed.
  intro h7
  -- False on the left can always be used.
  apply False.elim h6



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_174627337848893325325861072061 : ((((p2 ∧ p1) → (p1 ∨ p3)) → (p4 ∨ ((p2 → p4) → ((p2 → False) → p2)))) → ((p4 ∧ ((p5 → p1) → p1)) ∨ (p3 → (p3 → p3)))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h2
  -- Implications on the right can always be decomposed.
  intro h3
  -- One of the premise coincides with the conclusion.
  exact h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_152487063287676119359677216965 : ((((True ∨ p5) ∨ p3) ∨ (p3 ∨ ((((True → p3) ∨ (p1 ∨ ((p5 ∧ False) → p3))) ∨ False) ∧ (p5 → p3)))) → ((False ∨ p4) → (p3 ∨ p4))) := by
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
    -- Disjunctions on the left can always be decomposed.
    cases h1
    case inl h5 =>
      -- Disjunctions on the left can always be decomposed.
      cases h5
      case inl h6 =>
        -- Disjunctions on the left can always be decomposed.
        cases h6
        case inl h7 =>
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- One of the premise coincides with the conclusion.
          exact h4
        case inr h8 =>
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- One of the premise coincides with the conclusion.
          exact h4
      case inr h9 =>
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- One of the premise coincides with the conclusion.
        exact h9
    case inr h10 =>
      -- Disjunctions on the left can always be decomposed.
      cases h10
      case inl h11 =>
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- One of the premise coincides with the conclusion.
        exact h11
      case inr h12 =>
        -- Conjunctions on the left can always be decomposed.
        let h13 := h12.left
        let h14 := h12.right
        -- Disjunctions on the left can always be decomposed.
        cases h13
        case inl h15 =>
          -- Disjunctions on the left can always be decomposed.
          cases h15
          case inl h16 =>
            -- Show the right disjunct based on <expert-advice>.
            apply Or.inr
            -- One of the premise coincides with the conclusion.
            exact h4
          case inr h17 =>
            -- Disjunctions on the left can always be decomposed.
            cases h17
            case inl h18 =>
              -- Show the right disjunct based on <expert-advice>.
              apply Or.inr
              -- One of the premise coincides with the conclusion.
              exact h4
            case inr h19 =>
              -- Show the right disjunct based on <expert-advice>.
              apply Or.inr
              -- One of the premise coincides with the conclusion.
              exact h4
        case inr h20 =>
          -- False on the left can always be used.
          apply False.elim h20



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_39042118643204675475811787880 : ((((True ∧ p1) ∨ (((p4 ∧ p2) → ((p2 ∧ False) ∧ p3)) → ((p5 ∨ p3) ∨ (((p3 ∨ (p5 ∧ False)) ∨ (p5 ∧ p5)) ∨ p1)))) ∧ p5) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_612987837727301278209683011688 : (((((((((p5 ∨ p5) → ((((p1 → (p2 → p3)) ∨ (False ∨ p3)) ∧ p1) ∨ True)) ∧ (p4 → True)) ∨ p5) ∧ p3) → (p4 ∧ p1)) ∨ True) ∨ p5) ∧ True) := by
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
theorem thm_5_vars_324005786741744071738519946524 : (p5 ∨ ((p5 ∨ (p4 ∧ (p4 ∨ (p4 → (((p4 ∨ p2) ∧ p3) ∧ (p2 ∧ p2)))))) ∨ (p1 → ((True ∧ ((p4 ∨ False) → False)) ∨ (p4 → p1))))) := by
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



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_625751852696049973241383718396 : ((((p1 → ((True ∧ p2) ∨ ((((True ∨ (((p2 → p4) ∨ p1) ∨ p1)) → (p3 ∨ p3)) ∧ p4) ∨ (False → (p4 ∧ (p2 ∨ p4)))))) ∨ p3) ∨ p5) ∧ True) := by
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
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h2
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- False on the left can always be used.
  apply False.elim h2
  -- False on the left can always be used.
  apply False.elim h2
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_798196422791319353343526903065 : (((p1 → (((p4 ∨ (((p4 ∨ ((p1 ∧ (True ∧ (p5 → p5))) ∧ p2)) ∨ p4) ∧ p4)) ∧ (True → p1)) → (p5 → ((False ∧ p1) ∧ p1)))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_991429202378374104070960568194 : (((p4 ∧ ((((p3 ∧ (p2 ∨ True)) → ((p4 → p3) → p4)) → (((p1 → p2) → ((p3 ∧ ((p5 ∧ p2) ∨ p4)) ∨ False)) ∨ p4)) → p1)) → p1) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- We want to use the implication h3 based on <expert-advice>. So we show its premise.
  have h4 : (((p3 ∧ (p2 ∨ True)) → ((p4 → p3) → p4)) → (((p1 → p2) → ((p3 ∧ ((p5 ∧ p2) ∨ p4)) ∨ False)) ∨ p4)) := by
    -- Implications on the right can always be decomposed.
    intro h5
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h2
  -- We have shown the premise of h3, we can now drive its conclusion.
  let h6 := h3 h4
  -- One of the premise coincides with the conclusion.
  exact h6
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_33582270887166173008644350543 : ((p4 ∨ (p1 ∨ (False ∨ (((p1 → (False ∨ (p3 ∧ p4))) → False) ∨ ((((p3 → (((False → p4) ∧ True) ∨ p5)) → True) ∨ False) ∨ False))))) ∧ True) := by
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
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_257212123116800518602991790248 : ((p2 ∨ p2) → ((p5 ∨ ((True → (False ∧ p1)) ∧ p3)) → (((p1 → ((False ∧ p5) ∧ p2)) ∨ (p4 → ((p1 → (p5 ∧ p5)) → p2))) ∧ p2))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Disjunctions on the left can always be decomposed.
  cases h2
  case inl h3 =>
    -- Disjunctions on the left can always be decomposed.
    cases h1
    case inl h4 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Implications on the right can always be decomposed.
      intro h5
      -- Implications on the right can always be decomposed.
      intro h6
      -- One of the premise coincides with the conclusion.
      exact h4
    case inr h7 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Implications on the right can always be decomposed.
      intro h8
      -- Implications on the right can always be decomposed.
      intro h9
      -- One of the premise coincides with the conclusion.
      exact h7
  case inr h10 =>
    -- Conjunctions on the left can always be decomposed.
    let h11 := h10.left
    let h12 := h10.right
    -- Disjunctions on the left can always be decomposed.
    cases h1
    case inl h13 =>
      -- We want to use the implication h11 based on <expert-advice>. So we show its premise.
      have h14 : True := by
        -- True on the right can always be proven directly.
        apply True.intro
      -- We have shown the premise of h11, we can now drive its conclusion.
      let h15 := h11 h14
      -- We need to get the left conjuct of h15 based on <expert-advice>.
      let h16 := h15.left
      -- False on the left can always be used.
      apply False.elim h16
    case inr h17 =>
      -- We want to use the implication h11 based on <expert-advice>. So we show its premise.
      have h18 : True := by
        -- True on the right can always be proven directly.
        apply True.intro
      -- We have shown the premise of h11, we can now drive its conclusion.
      let h19 := h11 h18
      -- We need to get the left conjuct of h19 based on <expert-advice>.
      let h20 := h19.left
      -- False on the left can always be used.
      apply False.elim h20
  -- Disjunctions on the left can always be decomposed.
  cases h2
  case inl h21 =>
    -- Disjunctions on the left can always be decomposed.
    cases h1
    case inl h22 =>
      -- One of the premise coincides with the conclusion.
      exact h22
    case inr h23 =>
      -- One of the premise coincides with the conclusion.
      exact h23
  case inr h24 =>
    -- Conjunctions on the left can always be decomposed.
    let h25 := h24.left
    let h26 := h24.right
    -- Disjunctions on the left can always be decomposed.
    cases h1
    case inl h27 =>
      -- One of the premise coincides with the conclusion.
      exact h27
    case inr h28 =>
      -- One of the premise coincides with the conclusion.
      exact h28



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_337902161938396390537433253342 : (p1 → ((True ∨ (((((False → p4) → (p2 ∨ p4)) ∧ False) → p1) ∧ (p2 ∨ p3))) → (((p5 ∨ p2) ∨ ((p5 → p3) ∨ (p4 → p4))) ∨ p4))) := by
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
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h4
    -- One of the premise coincides with the conclusion.
    exact h4
  case inr h5 =>
    -- Conjunctions on the left can always be decomposed.
    let h6 := h5.left
    let h7 := h5.right
    -- Disjunctions on the left can always be decomposed.
    cases h7
    case inl h8 =>
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- One of the premise coincides with the conclusion.
      exact h8
    case inr h9 =>
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- Implications on the right can always be decomposed.
      intro h10
      -- One of the premise coincides with the conclusion.
      exact h9



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_198760929122870324673834940135 : ((True → ((True ∨ p5) → ((p4 ∨ p1) ∧ False))) ∨ ((p5 → (p5 → ((p4 ∧ (True ∧ (p2 ∧ (p5 ∨ p3)))) → (p2 ∧ (p5 ∧ True))))) → True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_123915868387531690209668990892 : ((((False ∨ ((p5 ∨ ((False → p4) ∨ p2)) ∧ (p3 ∨ p5))) → False) ∧ (True → ((p2 ∧ (p4 ∨ (True ∧ (p4 ∧ p4)))) ∧ True))) → (p1 ∨ p4)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- We want to use the implication h3 based on <expert-advice>. So we show its premise.
  have h4 : True := by
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h3, we can now drive its conclusion.
  let h5 := h3 h4
  -- We need to get the left conjuct of h5 based on <expert-advice>.
  let h6 := h5.left
  -- We need to get the right conjuct of h6 based on <expert-advice>.
  let h7 := h6.right
  -- Disjunctions on the left can always be decomposed.
  cases h7
  case inl h8 =>
    -- One of the premise coincides with the conclusion.
    exact h8
  case inr h9 =>
    -- Conjunctions on the left can always be decomposed.
    let h10 := h9.left
    let h11 := h9.right
    -- Conjunctions on the left can always be decomposed.
    let h12 := h11.left
    let h13 := h11.right
    -- One of the premise coincides with the conclusion.
    exact h13



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_708059845174422668852780790557 : ((((p3 ∨ (p3 ∨ ((p5 ∨ (p1 ∨ p2)) ∨ True))) ∨ (p2 ∧ (p2 ∨ (p3 ∧ (p4 ∧ (((p4 ∧ (p2 ∨ p3)) ∧ (True → p2)) → p4)))))) ∨ p2) ∧ True) := by
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
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_473852478051946542175493639171 : ((((p4 ∧ (p3 ∨ (p4 ∨ ((False ∧ (p3 → p3)) → (p2 ∧ True))))) → (p2 ∨ ((((True ∧ True) → False) ∨ ((p2 ∨ True) → True)) ∨ p2))) ∧ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
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
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h5
    -- True on the right can always be proven directly.
    apply True.intro
  case inr h6 =>
    -- Disjunctions on the left can always be decomposed.
    cases h6
    case inl h7 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Implications on the right can always be decomposed.
      intro h8
      -- True on the right can always be proven directly.
      apply True.intro
    case inr h9 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Implications on the right can always be decomposed.
      intro h10
      -- True on the right can always be proven directly.
      apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_111319203854070270841625068408 : (((p1 ∧ ((((p4 ∨ p4) → True) → p2) ∧ ((p2 → ((((p4 ∨ p5) ∧ False) → (p3 ∧ p2)) ∧ (True → False))) ∧ p5))) ∧ p1) ∨ (p1 ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_62015887276960805812377173651 : ((p2 ∧ ((True → (p1 → True)) ∧ (p3 ∨ ((((p5 ∧ True) ∧ ((((True → p1) ∧ (p4 ∧ p5)) ∧ False) ∨ p2)) ∨ (True → p2)) → p1)))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_208424865284777478224082495052 : (((p3 ∨ p2) ∨ (p2 ∧ (p3 ∨ p4))) → (((False ∧ (p1 → (p3 → ((True → (p4 ∨ (False ∧ p3))) ∧ (p2 ∨ (False ∨ p2)))))) ∨ True) ∨ p3)) := by
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
      -- One of the premise coincides with the conclusion.
      exact h3
    case inr h4 =>
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
    -- Disjunctions on the left can always be decomposed.
    cases h7
    case inl h8 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- One of the premise coincides with the conclusion.
      exact h8
    case inr h9 =>
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- True on the right can always be proven directly.
      apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_226720633060169630102215895580 : (((p1 ∧ p2) → False) ∨ ((True ∧ ((p4 ∧ ((p1 ∨ (p2 ∨ p1)) → (p1 ∧ p4))) ∨ p2)) ∨ ((False ∧ p4) → ((p1 ∧ (p1 ∨ p5)) ∨ p4)))) := by
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
theorem thm_5_vars_56173703611422988129833030326 : (((p2 ∧ ((p5 ∧ p4) ∨ True)) ∨ (p5 ∨ (p3 → ((p2 → (p2 ∨ (True ∨ (p5 ∨ (p1 ∧ False))))) → (False ∨ (False → (p5 ∧ p1))))))) ∨ p1) := by
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
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h3
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- False on the left can always be used.
  apply False.elim h3
  -- False on the left can always be used.
  apply False.elim h3



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_648961148789800427902768075048 : (((((((False ∧ ((((False ∨ ((p3 ∧ p2) ∧ p1)) ∧ p4) ∨ ((False ∨ False) → p3)) ∨ (p4 → p2))) ∧ p1) → True) → p1) ∧ (p1 → p1)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_355927999587257496761498601775 : (p5 → (((True → (((p3 ∨ p2) ∨ p2) → (False ∧ p4))) ∧ (((p5 → (p2 ∨ True)) ∧ (p1 ∨ (False → p3))) ∧ p3)) → ((p5 → p1) ∨ p1))) := by
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
  let h7 := h5.left
  let h8 := h5.right
  -- Disjunctions on the left can always be decomposed.
  cases h8
  case inl h9 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h9
  case inr h10 =>
    -- We want to use the implication h3 based on <expert-advice>. So we show its premise.
    have h11 : True := by
      -- True on the right can always be proven directly.
      apply True.intro
    -- We have shown the premise of h3, we can now drive its conclusion.
    let h12 := h3 h11
    -- We want to use the implication h12 based on <expert-advice>. So we show its premise.
    have h13 : ((p3 ∨ p2) ∨ p2) := by
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- One of the premise coincides with the conclusion.
      exact h6
    -- We have shown the premise of h12, we can now drive its conclusion.
    let h14 := h12 h13
    -- We need to get the left conjuct of h14 based on <expert-advice>.
    let h15 := h14.left
    -- False on the left can always be used.
    apply False.elim h15



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_314088306074063433468465112836 : (p3 ∨ (((((p3 ∨ ((p4 → p4) ∨ p5)) ∧ ((False → p2) → (False ∧ p2))) ∧ p5) ∧ (True ∧ ((p2 ∧ False) ∨ (p4 → p3)))) → (p4 ∧ p2))) := by
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
  -- Conjunctions on the left can always be decomposed.
  let h6 := h4.left
  let h7 := h4.right
  -- Disjunctions on the left can always be decomposed.
  cases h6
  case inl h8 =>
    -- Conjunctions on the left can always be decomposed.
    let h9 := h3.left
    let h10 := h3.right
    -- Disjunctions on the left can always be decomposed.
    cases h10
    case inl h11 =>
      -- Conjunctions on the left can always be decomposed.
      let h12 := h11.left
      let h13 := h11.right
      -- False on the left can always be used.
      apply False.elim h13
    case inr h14 =>
      -- We want to use the implication h7 based on <expert-advice>. So we show its premise.
      have h15 : (False → p2) := by
        -- Implications on the right can always be decomposed.
        intro h16
        -- False on the left can always be used.
        apply False.elim h16
      -- We have shown the premise of h7, we can now drive its conclusion.
      let h17 := h7 h15
      -- We need to get the left conjuct of h17 based on <expert-advice>.
      let h18 := h17.left
      -- False on the left can always be used.
      apply False.elim h18
  case inr h19 =>
    -- Disjunctions on the left can always be decomposed.
    cases h19
    case inl h20 =>
      -- Conjunctions on the left can always be decomposed.
      let h21 := h3.left
      let h22 := h3.right
      -- Disjunctions on the left can always be decomposed.
      cases h22
      case inl h23 =>
        -- Conjunctions on the left can always be decomposed.
        let h24 := h23.left
        let h25 := h23.right
        -- False on the left can always be used.
        apply False.elim h25
      case inr h26 =>
        -- We want to use the implication h7 based on <expert-advice>. So we show its premise.
        have h27 : (False → p2) := by
          -- Implications on the right can always be decomposed.
          intro h28
          -- False on the left can always be used.
          apply False.elim h28
        -- We have shown the premise of h7, we can now drive its conclusion.
        let h29 := h7 h27
        -- We need to get the left conjuct of h29 based on <expert-advice>.
        let h30 := h29.left
        -- False on the left can always be used.
        apply False.elim h30
    case inr h31 =>
      -- Conjunctions on the left can always be decomposed.
      let h32 := h3.left
      let h33 := h3.right
      -- Disjunctions on the left can always be decomposed.
      cases h33
      case inl h34 =>
        -- Conjunctions on the left can always be decomposed.
        let h35 := h34.left
        let h36 := h34.right
        -- False on the left can always be used.
        apply False.elim h36
      case inr h37 =>
        -- We want to use the implication h7 based on <expert-advice>. So we show its premise.
        have h38 : (False → p2) := by
          -- Implications on the right can always be decomposed.
          intro h39
          -- False on the left can always be used.
          apply False.elim h39
        -- We have shown the premise of h7, we can now drive its conclusion.
        let h40 := h7 h38
        -- We need to get the left conjuct of h40 based on <expert-advice>.
        let h41 := h40.left
        -- False on the left can always be used.
        apply False.elim h41
  -- Conjunctions on the left can always be decomposed.
  let h42 := h1.left
  let h43 := h1.right
  -- Conjunctions on the left can always be decomposed.
  let h44 := h42.left
  let h45 := h42.right
  -- Conjunctions on the left can always be decomposed.
  let h46 := h44.left
  let h47 := h44.right
  -- Disjunctions on the left can always be decomposed.
  cases h46
  case inl h48 =>
    -- Conjunctions on the left can always be decomposed.
    let h49 := h43.left
    let h50 := h43.right
    -- Disjunctions on the left can always be decomposed.
    cases h50
    case inl h51 =>
      -- Conjunctions on the left can always be decomposed.
      let h52 := h51.left
      let h53 := h51.right
      -- False on the left can always be used.
      apply False.elim h53
    case inr h54 =>
      -- We want to use the implication h47 based on <expert-advice>. So we show its premise.
      have h55 : (False → p2) := by
        -- Implications on the right can always be decomposed.
        intro h56
        -- False on the left can always be used.
        apply False.elim h56
      -- We have shown the premise of h47, we can now drive its conclusion.
      let h57 := h47 h55
      -- We need to get the right conjuct of h57 based on <expert-advice>.
      let h58 := h57.right
      -- One of the premise coincides with the conclusion.
      exact h58
  case inr h59 =>
    -- Disjunctions on the left can always be decomposed.
    cases h59
    case inl h60 =>
      -- Conjunctions on the left can always be decomposed.
      let h61 := h43.left
      let h62 := h43.right
      -- Disjunctions on the left can always be decomposed.
      cases h62
      case inl h63 =>
        -- Conjunctions on the left can always be decomposed.
        let h64 := h63.left
        let h65 := h63.right
        -- False on the left can always be used.
        apply False.elim h65
      case inr h66 =>
        -- We want to use the implication h47 based on <expert-advice>. So we show its premise.
        have h67 : (False → p2) := by
          -- Implications on the right can always be decomposed.
          intro h68
          -- False on the left can always be used.
          apply False.elim h68
        -- We have shown the premise of h47, we can now drive its conclusion.
        let h69 := h47 h67
        -- We need to get the right conjuct of h69 based on <expert-advice>.
        let h70 := h69.right
        -- One of the premise coincides with the conclusion.
        exact h70
    case inr h71 =>
      -- Conjunctions on the left can always be decomposed.
      let h72 := h43.left
      let h73 := h43.right
      -- Disjunctions on the left can always be decomposed.
      cases h73
      case inl h74 =>
        -- Conjunctions on the left can always be decomposed.
        let h75 := h74.left
        let h76 := h74.right
        -- False on the left can always be used.
        apply False.elim h76
      case inr h77 =>
        -- We want to use the implication h47 based on <expert-advice>. So we show its premise.
        have h78 : (False → p2) := by
          -- Implications on the right can always be decomposed.
          intro h79
          -- False on the left can always be used.
          apply False.elim h79
        -- We have shown the premise of h47, we can now drive its conclusion.
        let h80 := h47 h78
        -- We need to get the right conjuct of h80 based on <expert-advice>.
        let h81 := h80.right
        -- One of the premise coincides with the conclusion.
        exact h81



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_337648641056906564965444267793 : (p1 → (((p3 ∧ ((((((p2 ∨ p3) → p2) ∨ (p5 ∧ (p4 → True))) → p2) → False) ∨ p2)) ∧ True) ∨ (p4 → ((p4 ∨ (p5 ∨ p3)) → p4)))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h2
  -- Implications on the right can always be decomposed.
  intro h3
  -- Disjunctions on the left can always be decomposed.
  cases h3
  case inl h4 =>
    -- One of the premise coincides with the conclusion.
    exact h2
  case inr h5 =>
    -- Disjunctions on the left can always be decomposed.
    cases h5
    case inl h6 =>
      -- One of the premise coincides with the conclusion.
      exact h2
    case inr h7 =>
      -- One of the premise coincides with the conclusion.
      exact h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_342706811687952852755641435322 : (p2 → ((p1 → (((p3 ∧ True) ∨ p2) → (p3 ∧ (p3 ∧ False)))) → ((((False → p4) ∧ ((p5 → p1) ∨ True)) ∨ ((p3 ∧ False) ∨ False)) ∨ p3))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h3
  -- False on the left can always be used.
  apply False.elim h3
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_65772136508944222994593904885 : ((p4 ∨ ((((p3 ∨ (((p1 → ((p1 ∧ p4) ∨ p4)) → True) ∧ (False → p2))) → p1) ∨ p3) → ((p5 → (p5 → p3)) ∨ (True ∧ p3)))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_137326983943909222019673110102 : ((p2 ∧ (True ∧ ((((p4 → (p4 → True)) → (p2 ∧ (p5 ∨ p1))) → ((False → False) → (p1 ∨ p4))) ∨ (p5 ∧ True)))) ∨ (False → (p5 ∨ p2))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_309643061600728363526854021147 : (p2 ∨ (((p1 → False) ∨ ((p3 ∧ ((p3 ∧ (p5 ∧ p2)) ∧ ((p3 → p5) ∧ (False → False)))) ∧ (p5 → (p4 ∨ True)))) ∨ (True ∨ (p5 ∧ p2)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_134642256071461386740010729541 : ((((((p3 ∧ p3) → ((True ∧ (False ∧ (p5 ∨ p4))) ∨ p2)) ∨ p3) ∧ (True ∧ (True ∨ (True → (p4 ∨ True))))) → False) ∨ (False → (p4 → p1))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- False on the left can always be used.
  apply False.elim h1



