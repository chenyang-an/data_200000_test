variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_58821475642575638665654994663 : (((p5 → p5) ∧ ((((False ∨ p2) → (p2 ∨ p5)) → (False ∧ (((False ∧ p5) → True) ∨ (p3 ∨ ((p4 ∨ p4) → (p3 ∧ True)))))) ∧ True)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_299268949625478038808899657174 : (False ∨ ((((p2 → ((((p5 → p5) ∨ (p3 → p1)) ∧ (p5 → p1)) ∧ (True ∧ p3))) → p4) ∨ (False → (p5 ∧ (True ∨ (p3 ∧ p5))))) ∨ p2)) := by
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
  -- False on the left can always be used.
  apply False.elim h1
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_2090235916524599820240314706 : (((False ∨ (p1 → False)) → (p3 ∧ ((((p4 ∧ p3) ∨ False) ∧ (p4 ∧ (False → p2))) ∧ p5))) ∨ ((p4 → False) ∨ (p4 → (True ∧ p4)))) := by
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
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_186068245096509090340401056418 : ((((False → (((p2 → p5) ∨ p1) → (p5 ∧ p3))) ∨ p2) ∨ p3) → ((False → False) ∧ ((p5 → p5) → ((p4 → (p3 ∨ (False → p4))) ∨ p2)))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h2
  -- False on the left can always be used.
  apply False.elim h2
  -- Implications on the right can always be decomposed.
  intro h3
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h4 =>
    -- Disjunctions on the left can always be decomposed.
    cases h4
    case inl h5 =>
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- Implications on the right can always be decomposed.
      intro h6
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Implications on the right can always be decomposed.
      intro h7
      -- False on the left can always be used.
      apply False.elim h7
    case inr h8 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- One of the premise coincides with the conclusion.
      exact h8
  case inr h9 =>
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Implications on the right can always be decomposed.
    intro h10
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h11
    -- False on the left can always be used.
    apply False.elim h11



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_168706537134898978539221692408 : ((True ∨ ((((False ∨ True) ∨ (p2 ∧ (True → p4))) → (p5 ∨ (False ∨ True))) ∨ (True ∧ True))) → (p1 → ((p5 ∨ p4) ∨ (False → (p3 ∧ p4))))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h3 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h4
    -- Conjunctions on the right can always be decomposed.
    apply And.intro
    -- False on the left can always be used.
    apply False.elim h4
    -- False on the left can always be used.
    apply False.elim h4
  case inr h5 =>
    -- Disjunctions on the left can always be decomposed.
    cases h5
    case inl h6 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Implications on the right can always be decomposed.
      intro h7
      -- Conjunctions on the right can always be decomposed.
      apply And.intro
      -- False on the left can always be used.
      apply False.elim h7
      -- False on the left can always be used.
      apply False.elim h7
    case inr h8 =>
      -- Conjunctions on the left can always be decomposed.
      let h9 := h8.left
      let h10 := h8.right
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Implications on the right can always be decomposed.
      intro h11
      -- Conjunctions on the right can always be decomposed.
      apply And.intro
      -- False on the left can always be used.
      apply False.elim h11
      -- False on the left can always be used.
      apply False.elim h11



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_112154263758481666493718314383 : (((p2 ∧ (((p2 → True) ∧ (((p3 → (p1 ∧ p4)) ∨ (p1 ∧ True)) ∨ ((False ∧ p5) ∨ (p3 ∨ p1)))) ∨ (False ∨ p3))) ∨ True) ∨ (p2 → False)) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_49102485825659633389426927656 : (((((((False → True) ∧ p3) → False) → (False → (((p5 → (p5 ∨ p4)) ∨ p4) ∨ p4))) → (True → (False ∧ True))) ∨ ((p3 → True) ∨ p4)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_315008674365519388442447305477 : (p3 ∨ ((((False ∨ p3) ∨ ((p1 ∧ p2) ∨ p5)) ∨ True) ∨ (p1 ∨ (p4 ∧ ((p1 ∧ (p2 ∨ (p2 ∨ (False ∨ True)))) ∨ ((p2 → True) → p3)))))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_161816569285667152233453857676 : ((p5 ∨ (p5 ∧ ((p4 → ((p5 ∨ p5) ∨ ((((p1 ∨ True) ∨ True) ∨ False) ∨ (True ∨ False)))) ∨ p5))) → (((p5 ∧ p1) ∨ p2) ∨ (p2 → True))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h2 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h3
    -- True on the right can always be proven directly.
    apply True.intro
  case inr h4 =>
    -- Conjunctions on the left can always be decomposed.
    let h5 := h4.left
    let h6 := h4.right
    -- Disjunctions on the left can always be decomposed.
    cases h6
    case inl h7 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Implications on the right can always be decomposed.
      intro h8
      -- True on the right can always be proven directly.
      apply True.intro
    case inr h9 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Implications on the right can always be decomposed.
      intro h10
      -- True on the right can always be proven directly.
      apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_249700229503329574908390204438 : ((p5 ∨ p4) ∨ (p3 ∨ ((((((p1 ∧ p2) → (True → p3)) → p4) ∧ True) → (p1 → p3)) ∨ ((False → (((True ∨ p1) ∨ p4) ∧ p2)) ∨ True)))) := by
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
theorem thm_5_vars_181703749767866021734052387163 : ((p5 → (((p3 ∨ p5) → ((p2 ∧ False) ∨ p3)) ∨ (p2 ∧ (True ∨ p2)))) → (p3 → (((p2 → (True → False)) ∧ (p1 ∧ (False ∨ p2))) ∨ True))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_66162955534415622343648522321 : ((p5 ∨ ((p3 ∨ (((p3 ∨ p5) ∨ (p2 → (p5 ∧ ((p1 ∧ (p1 → p3)) ∨ p4)))) ∨ (p1 → (p5 ∧ p1)))) ∧ (p5 ∨ (p5 ∧ p5)))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_69030626993125112589014665195 : ((p5 → ((((((p4 ∧ (p4 ∧ (False ∨ p2))) ∨ (p4 → p4)) ∧ True) ∨ (p5 ∧ ((p5 ∨ p2) ∨ (p1 ∨ (p5 ∧ p2))))) → False) ∨ p5)) ∨ p4) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_238347539670933010115314102474 : ((False ∨ True) ∧ (p1 → (((p1 → p4) ∨ ((p5 ∨ p5) ∧ (((p3 ∨ (True → (False → True))) ∧ ((False → p2) ∨ p1)) → (p1 ∧ p3)))) ∨ True))) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_678782710578627341589699180293 : ((((True ∧ ((((((p2 ∧ ((False ∨ p5) → p5)) → p4) ∧ (p4 → (p3 ∨ False))) ∧ p5) ∧ p1) ∨ True)) ∨ ((p2 → True) → (False ∨ p1))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_40037256894836901933554339683 : (((((((p2 ∧ True) ∧ p3) ∨ (((p4 → p4) ∧ ((p3 ∧ p1) → ((False ∨ (p4 → p4)) → (p5 → p5)))) ∨ True)) ∧ p5) ∧ p3) ∨ p5) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_39716576035583076074890339818 : (((p5 ∨ (((False ∧ p5) ∨ (((p1 → ((True → p4) ∨ True)) → False) ∨ ((p5 ∧ ((False ∨ True) → (True ∧ p1))) → p3))) → p4)) ∧ p5) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_749846182067785533068373040040 : (((True ∧ ((p5 ∨ (((True → False) ∧ ((p3 → (((p2 ∨ p1) ∧ True) ∧ (p4 → (p5 → (p2 → True))))) ∨ p3)) ∧ (p3 ∧ p1))) ∨ p3)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_90927510189876346639680314611 : (((True → p1) ∧ ((p1 ∨ p5) ∧ (p5 → (((p4 ∧ (True ∧ (p3 → (p5 → (p3 → False))))) → (p3 ∧ ((p3 ∨ p4) ∨ p1))) ∨ p3)))) → p1) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- Conjunctions on the left can always be decomposed.
  let h4 := h3.left
  let h5 := h3.right
  -- Disjunctions on the left can always be decomposed.
  cases h4
  case inl h6 =>
    -- One of the premise coincides with the conclusion.
    exact h6
  case inr h7 =>
    -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
    have h8 : True := by
      -- True on the right can always be proven directly.
      apply True.intro
    -- We have shown the premise of h2, we can now drive its conclusion.
    let h9 := h2 h8
    -- One of the premise coincides with the conclusion.
    exact h9



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_49629314607083453786386933146 : (((((True ∨ p2) ∧ (True ∨ (True ∧ p3))) ∨ ((((p1 ∧ p3) ∨ p3) ∧ (p2 ∨ p1)) ∨ ((False → p4) → p2))) → ((p4 → False) ∨ p2)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_205590619152214497732259991234 : (((p3 → p2) ∧ (p2 ∨ (p3 ∨ p2))) ∨ ((True ∧ (((p5 ∧ True) → p4) → True)) ∧ ((p2 → ((p2 → (p4 ∧ p4)) ∧ (True → p1))) ∨ True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_777942041836549730922406858219 : (((p1 ∨ (((p3 → p1) ∧ p2) ∨ (((True → p5) → (((((p5 ∨ True) ∨ (True ∨ p4)) ∨ p2) → p3) → (p3 ∧ (p3 ∧ p5)))) ∧ True))) ∨ p1) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
  have h3 : (((p5 ∨ True) ∨ (True ∨ p4)) ∨ p2) := by
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h2, we can now drive its conclusion.
  let h4 := h2 h3
  -- One of the premise coincides with the conclusion.
  exact h4
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
  have h5 : (((p5 ∨ True) ∨ (True ∨ p4)) ∨ p2) := by
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h2, we can now drive its conclusion.
  let h6 := h2 h5
  -- One of the premise coincides with the conclusion.
  exact h6
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h7 : True := by
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h8 := h1 h7
  -- One of the premise coincides with the conclusion.
  exact h8
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_62838823719823512727875744459 : ((p4 ∧ (((p4 ∧ p4) → (False ∨ (p5 ∧ p1))) ∧ (p5 ∧ ((p4 ∨ (p4 ∨ ((p1 ∨ False) ∨ (((True → p3) ∨ p4) → True)))) ∨ True)))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_164694985367826815022018619699 : (((((((((False ∧ p4) → (p3 → (p4 ∨ p4))) ∧ p5) ∨ p2) → p5) → p3) ∨ p3) ∨ p2) ∨ (p4 → ((True ∨ True) ∧ (p4 → (p4 → p4))))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro
  -- Implications on the right can always be decomposed.
  intro h2
  -- Implications on the right can always be decomposed.
  intro h3
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_54866539672112411577177348435 : ((((p3 ∧ ((p2 ∧ p1) ∧ p4)) ∧ p2) ∧ ((p1 → (((p5 → p4) ∧ (False ∧ (((p2 → p5) ∨ True) ∧ False))) ∨ p4)) ∧ (True ∧ p4))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_588847943369521894465414075656 : (((((p1 ∨ (((False ∧ (False → False)) ∨ (True ∨ p1)) → (True → (p5 → ((False ∨ p3) → ((p5 → p2) → (p1 ∧ p5))))))) ∨ False) ∧ p1) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_115912242256164594074777388698 : ((((p2 → p3) ∧ (p1 ∨ p1)) ∨ ((((False → (True → True)) → (((p2 → (p5 → (p2 → p5))) ∧ p1) ∨ p4)) → p3) → p3)) ∨ (p5 ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_165693125002993149144765253365 : (((p4 ∧ ((p1 → True) ∨ (p4 ∧ p4))) → ((p1 → True) → (p5 ∧ ((p5 ∧ p2) ∨ False)))) ∨ (False ∨ ((False → (p1 ∨ (p2 → p2))) ∧ True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h1
  -- False on the left can always be used.
  apply False.elim h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_613044101819631734937382475330 : ((((((((p3 ∧ (((p4 → (p1 ∧ p4)) ∨ p5) → ((False → p2) → p2))) → ((p5 → p4) ∨ p5)) → p2) ∨ p2) → (p3 ∨ False)) ∨ p3) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_58502411472237319961474755319 : (((p4 ∨ p4) ∧ ((((True → p3) ∨ ((((True → p2) → p3) ∧ (((True ∧ p3) ∧ True) → p3)) ∨ (False → p2))) → p5) ∨ (p3 ∨ p4))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_731220611449125794429328968646 : ((((p3 ∨ (True ∨ p1)) → (p2 → ((False ∨ (p5 → p4)) ∨ (((p4 → (((p5 → p3) ∧ p2) ∨ True)) ∨ (p1 → (p3 ∨ False))) ∨ p4)))) ∨ p5) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
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
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h4
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- One of the premise coincides with the conclusion.
    exact h3
  case inr h5 =>
    -- Disjunctions on the left can always be decomposed.
    cases h5
    case inl h6 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- Implications on the right can always be decomposed.
      intro h7
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- True on the right can always be proven directly.
      apply True.intro
    case inr h8 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- Implications on the right can always be decomposed.
      intro h9
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- True on the right can always be proven directly.
      apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_215446464855916889041703226061 : ((p3 ∧ ((p2 → p3) → p1)) ∨ (((((((p5 → ((p5 ∨ p3) ∨ True)) ∨ (p2 ∨ p2)) → p2) ∧ p1) → (False ∧ False)) → (p4 ∧ p3)) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_324014089112930541353868133709 : (p5 ∨ (((p1 ∧ (p2 → ((p1 ∧ ((p5 ∨ True) ∨ p5)) ∧ (p3 ∧ p5)))) ∨ p5) → ((p5 ∨ ((p1 ∨ p2) → p4)) ∨ ((p2 ∧ p1) ∨ p1)))) := by
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
    -- One of the premise coincides with the conclusion.
    exact h3
  case inr h5 =>
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- One of the premise coincides with the conclusion.
    exact h5



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_194005148577398178783593629043 : ((p4 ∨ ((p3 → (p5 ∨ ((False ∧ p4) ∧ p1))) ∨ True)) → (((p1 ∨ (False ∨ (True ∧ (p2 ∧ ((p3 ∧ p2) ∧ p5))))) ∨ (False → p3)) ∧ True)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h2 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h3
    -- False on the left can always be used.
    apply False.elim h3
  case inr h4 =>
    -- Disjunctions on the left can always be decomposed.
    cases h4
    case inl h5 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Implications on the right can always be decomposed.
      intro h6
      -- False on the left can always be used.
      apply False.elim h6
    case inr h7 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Implications on the right can always be decomposed.
      intro h8
      -- False on the left can always be used.
      apply False.elim h8
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_208938230816719086117628095522 : ((p5 ∧ (p1 → (p3 → (p5 → p3)))) → (((p1 ∧ p1) ∨ (p5 ∨ p1)) ∧ ((((p3 ∨ p5) → (False ∧ (False ∨ (False ∧ True)))) ∧ True) → p3))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- One of the premise coincides with the conclusion.
  exact h2
  -- Implications on the right can always be decomposed.
  intro h4
  -- Conjunctions on the left can always be decomposed.
  let h5 := h4.left
  let h6 := h4.right
  -- Conjunctions on the left can always be decomposed.
  let h7 := h1.left
  let h8 := h1.right
  -- We want to use the implication h5 based on <expert-advice>. So we show its premise.
  have h9 : (p3 ∨ p5) := by
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h7
  -- We have shown the premise of h5, we can now drive its conclusion.
  let h10 := h5 h9
  -- We need to get the left conjuct of h10 based on <expert-advice>.
  let h11 := h10.left
  -- False on the left can always be used.
  apply False.elim h11



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_251792105886172877520254534637 : ((p3 → p4) ∨ (((p2 ∨ (p2 → p5)) ∨ (True ∧ (((((True → p2) ∧ ((p1 ∨ p1) ∧ p5)) ∧ (False ∧ p5)) ∨ p5) ∧ False))) ∨ (False → p1))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_658568621117808686981731243726 : ((((p2 ∨ (p5 ∨ (((False → (p1 ∨ p1)) → (p4 ∧ ((((True ∧ (p5 ∨ p1)) → True) → (p4 → p4)) → p3))) → False))) ∨ (p3 → p2)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_191947923737986436785985787882 : ((True → (p2 ∨ (p1 ∨ (p4 → ((True → p3) ∧ p5))))) ∨ (((((p4 ∧ True) → (p3 ∨ (p3 ∧ False))) ∨ p1) → ((p4 ∧ False) ∧ p4)) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_148222985462967809098435196566 : (((((((((p3 ∧ p1) → (p3 ∨ True)) ∧ p3) → p1) → (False ∨ p5)) → p5) ∨ True) ∨ (p5 ∨ (p2 → p1))) ∨ (True → (p1 → (True ∨ p1)))) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_179439666938534008245378894637 : ((p5 ∨ (((((p3 ∨ p2) ∧ True) ∧ p5) ∨ (p3 ∨ (p5 ∨ p3))) ∧ p1)) ∨ ((True ∧ (p1 ∧ True)) → ((p5 → (p5 ∨ (p2 → p2))) ∨ False))) := by
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
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h6
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- One of the premise coincides with the conclusion.
  exact h6



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_350868528088215517757116203054 : (p4 → (((p3 ∨ p5) → ((True → (p1 ∧ p3)) ∨ (((p1 → p2) ∧ (False ∧ (p4 → False))) ∨ (True → (p5 → (False → p5)))))) ∧ (p2 → p2))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h2
  -- Disjunctions on the left can always be decomposed.
  cases h2
  case inl h3 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h4
    -- Implications on the right can always be decomposed.
    intro h5
    -- Implications on the right can always be decomposed.
    intro h6
    -- False on the left can always be used.
    apply False.elim h6
  case inr h7 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h8
    -- Implications on the right can always be decomposed.
    intro h9
    -- Implications on the right can always be decomposed.
    intro h10
    -- False on the left can always be used.
    apply False.elim h10
  -- Implications on the right can always be decomposed.
  intro h11
  -- One of the premise coincides with the conclusion.
  exact h11



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_214694361442199102682827344801 : (((True ∧ p3) ∨ (p2 ∧ p5)) ∨ (((True ∧ p5) ∧ ((((p4 ∨ (False ∧ (p5 → (False ∧ False)))) ∨ (False ∧ p2)) ∧ p1) ∨ p1)) ∨ (True ∨ p1))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_651964294323269645904331578279 : ((((True ∧ (((True → ((((p2 ∨ ((True ∧ (p3 → False)) ∧ True)) ∧ False) ∨ True) ∧ False)) ∧ (p4 → p4)) ∧ (True ∨ False))) ∧ (p3 ∨ True)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_457611311514011676000388563798 : ((((((p3 ∧ ((p3 ∨ ((True ∧ (p5 → p3)) → p3)) → (p4 ∨ True))) ∧ p5) ∨ (p3 ∨ p4)) ∨ (False ∨ (True ∨ ((True → True) ∨ p5)))) ∧ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
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
theorem thm_5_vars_307666995236639433351210402719 : (p1 ∨ (p2 → (((((((p2 ∧ ((p2 → ((p5 ∨ p1) → (p2 ∧ p2))) → True)) ∨ False) ∧ p2) ∨ p3) ∧ True) → ((p1 ∧ False) ∨ p2)) ∨ p3))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h2
  -- Conjunctions on the left can always be decomposed.
  let h3 := h2.left
  let h4 := h2.right
  -- Disjunctions on the left can always be decomposed.
  cases h3
  case inl h5 =>
    -- Conjunctions on the left can always be decomposed.
    let h6 := h5.left
    let h7 := h5.right
    -- Disjunctions on the left can always be decomposed.
    cases h6
    case inl h8 =>
      -- Conjunctions on the left can always be decomposed.
      let h9 := h8.left
      let h10 := h8.right
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- One of the premise coincides with the conclusion.
      exact h7
    case inr h11 =>
      -- False on the left can always be used.
      apply False.elim h11
  case inr h12 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_113805164393378025685505081218 : (((True ∧ ((p4 → (p2 ∨ ((p1 → p2) → (p1 ∧ (((True ∨ (p4 ∧ p5)) ∨ p5) → (p4 ∨ p5)))))) ∨ p3)) → (False ∧ p4)) ∨ (p3 → True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_313351637147413669958374995368 : (p3 ∨ ((p1 → (p3 ∧ (((p2 ∨ (True → (False → p4))) ∧ p2) ∨ (p3 ∧ (p2 ∧ ((((p5 ∧ p2) → p5) ∨ p1) ∨ (p5 → p4))))))) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_318621614799576192163983354956 : (p4 ∨ (((False ∨ False) ∨ ((p4 → (((p3 ∨ False) ∨ p5) ∨ (p1 → False))) ∧ ((p5 ∨ (p5 ∨ ((p3 ∧ p4) → p4))) ∨ p2))) ∨ (p4 → True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_41355456170603026392412910424 : ((((((((p2 ∧ (True ∧ (p2 ∨ True))) ∨ True) → False) ∧ ((True ∨ p5) ∨ False)) ∧ p1) → (((False ∧ (p4 ∧ p3)) ∨ False) ∨ p3)) ∨ p2) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_230587446474065922692192972397 : (((p1 → p3) ∧ p5) → (((p4 ∨ ((p5 ∧ ((p1 ∨ ((p1 ∨ p4) ∨ False)) → p5)) ∧ ((p2 → (False ∧ p3)) ∨ True))) ∧ (True ∧ p1)) ∨ p5)) := by
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
theorem thm_5_vars_176264910841609142170961908057 : (((((p2 ∨ p5) ∨ (False → ((p1 ∧ False) → False))) ∨ p4) ∨ (p3 ∧ False)) ∧ ((((p2 ∧ (p2 → True)) ∨ p5) ∨ (p4 ∧ True)) ∨ (False → p2))) := by
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
  -- Implications on the right can always be decomposed.
  intro h2
  -- Conjunctions on the left can always be decomposed.
  let h3 := h2.left
  let h4 := h2.right
  -- False on the left can always be used.
  apply False.elim h4
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h5
  -- False on the left can always be used.
  apply False.elim h5



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_192077660551485553930544943466 : ((p3 → (p2 ∨ ((p4 ∨ True) → ((p5 ∧ p1) ∨ p1)))) ∨ (((False → (True ∨ ((p1 → (p1 ∨ ((True ∧ p5) ∨ p5))) ∨ p1))) ∨ p3) ∨ p2)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_42278551189313782425231322013 : (((p1 ∧ (False ∧ (((p5 ∧ (p3 ∨ p2)) → ((p3 → ((p5 → True) ∨ False)) ∧ ((p2 ∧ (p2 ∨ (p2 ∧ p2))) → True))) → p2))) ∨ True) ∨ False) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_312997615267127414131583610416 : (p3 ∨ (((((p3 ∨ (p5 → (True ∧ (p3 ∧ (True ∧ ((((p3 ∧ False) ∨ p1) → ((False ∨ p2) → p4)) ∧ True)))))) ∨ p3) → p1) ∨ True) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_263391621202533922910579252457 : (True ∧ (((((False ∧ (p3 → (False ∧ p2))) → (p2 ∨ ((p1 ∧ p4) → (True ∧ p2)))) → p5) ∧ (p5 → (p3 ∨ p1))) ∨ (p3 → (True → True)))) := by
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
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_198195522760484553660925506496 : (((p1 → p3) → (False ∨ (False ∨ (p4 → p2)))) ∨ (((p5 ∨ True) → ((p2 ∨ ((p1 ∨ p4) ∧ (p5 → (True ∧ p5)))) ∧ p4)) → (p4 ∨ p5))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h2 : (p5 ∨ True) := by
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h3 := h1 h2
  -- We need to get the right conjuct of h3 based on <expert-advice>.
  let h4 := h3.right
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- One of the premise coincides with the conclusion.
  exact h4



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_245111357825930326101872443306 : ((p2 ∧ True) ∨ (((((p1 ∧ (p4 ∨ (((p4 ∧ p5) ∨ p5) ∨ p1))) ∧ (True ∨ ((p3 ∧ p2) ∧ False))) ∧ p5) ∨ (p4 ∨ p4)) ∨ (p3 → True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_161723880561833443628810864878 : ((p3 ∨ ((p1 → (((p3 ∨ False) ∨ p4) ∨ ((True → p1) → (p3 → (p5 ∨ p2))))) ∧ (p5 → True))) → ((True ∧ ((p2 ∧ p5) ∧ p2)) ∨ True)) := by
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
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_309801321695961086411564857902 : (p2 ∨ (((p4 → ((p5 ∨ (p5 ∧ p4)) ∨ False)) ∧ (((p5 → p5) → ((p3 → (p3 ∨ p4)) → p4)) ∧ p3)) ∨ (((p5 ∨ p1) ∨ p1) → True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_173346603822952711955057004002 : ((p3 → (((p1 → p3) → (p2 ∧ ((p2 ∨ p3) ∧ ((p4 ∨ False) ∧ p1)))) ∧ p3)) ∨ (((p4 ∨ p3) → ((p2 → (True → p5)) → p4)) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_340953426397069032926486717460 : (p2 → (((False ∧ (p2 → p3)) ∨ (((p4 ∨ ((p2 ∨ ((p3 ∨ False) ∧ p2)) → (((p4 ∨ (p3 ∨ True)) ∧ p5) ∨ p2))) → False) → False)) ∨ p3)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h2
  -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
  have h3 : (p4 ∨ ((p2 ∨ ((p3 ∨ False) ∧ p2)) → (((p4 ∨ (p3 ∨ True)) ∧ p5) ∨ p2))) := by
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h4
    -- Disjunctions on the left can always be decomposed.
    cases h4
    case inl h5 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- One of the premise coincides with the conclusion.
      exact h5
    case inr h6 =>
      -- Conjunctions on the left can always be decomposed.
      let h7 := h6.left
      let h8 := h6.right
      -- Disjunctions on the left can always be decomposed.
      cases h7
      case inl h9 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- One of the premise coincides with the conclusion.
        exact h8
      case inr h10 =>
        -- False on the left can always be used.
        apply False.elim h10
  -- We have shown the premise of h2, we can now drive its conclusion.
  let h11 := h2 h3
  -- False on the left can always be used.
  apply False.elim h11



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_232954827276271984141798648707 : ((p3 ∧ (p4 ∨ p5)) → ((p1 → (p2 ∧ (((p2 ∨ ((((p4 → ((p5 ∨ False) ∨ True)) ∧ p4) ∨ True) ∧ True)) → p5) ∨ (False → p3)))) ∨ p3)) := by
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
    -- One of the premise coincides with the conclusion.
    exact h2
  case inr h5 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_719640750503739676814467490729 : ((((p5 ∨ (p4 ∨ (p4 ∨ p2))) ∨ ((False ∧ (p1 ∨ ((p4 ∨ (True ∨ (False → (False ∨ (p1 → True))))) ∨ p5))) ∨ (True ∨ (p1 ∧ True)))) ∨ p1) ∧ True) := by
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
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_165739060865318980079441628416 : ((((p2 → (p4 ∧ False)) ∨ p3) ∨ ((p2 ∧ p3) ∧ ((p5 ∧ p2) ∨ (True ∨ (p1 ∨ False))))) ∨ (True → (True ∨ ((p1 → (True ∧ False)) ∧ True)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_308371731772728118609017533895 : (p2 ∨ ((((((p2 ∨ p4) ∨ ((((p3 ∧ p4) → p4) → p3) → (((p2 ∧ p2) ∨ True) ∧ p1))) → (p2 ∧ (True → p1))) ∨ True) ∨ False) ∨ p5)) := by
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
theorem thm_5_vars_183970499680146651431108723280 : (((p3 → (True ∧ (False ∧ (((True ∧ False) ∨ p4) ∨ p2)))) ∧ p2) ∨ (((p5 ∨ (p1 → p5)) ∧ (False ∧ (p4 ∨ ((False ∧ p5) ∨ False)))) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_337160648966817561156250133256 : (p1 → (((p4 ∧ (True ∨ (p5 ∨ ((p5 ∨ (p2 → ((p2 ∨ (p1 → True)) → (p5 ∨ False)))) ∨ (True ∨ (True ∨ True)))))) ∧ p3) → (p2 ∨ p3))) := by
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
  cases h6
  case inl h7 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h4
  case inr h8 =>
    -- Disjunctions on the left can always be decomposed.
    cases h8
    case inl h9 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- One of the premise coincides with the conclusion.
      exact h4
    case inr h10 =>
      -- Disjunctions on the left can always be decomposed.
      cases h10
      case inl h11 =>
        -- Disjunctions on the left can always be decomposed.
        cases h11
        case inl h12 =>
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- One of the premise coincides with the conclusion.
          exact h4
        case inr h13 =>
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- One of the premise coincides with the conclusion.
          exact h4
      case inr h14 =>
        -- Disjunctions on the left can always be decomposed.
        cases h14
        case inl h15 =>
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- One of the premise coincides with the conclusion.
          exact h4
        case inr h16 =>
          -- Disjunctions on the left can always be decomposed.
          cases h16
          case inl h17 =>
            -- Show the right disjunct based on <expert-advice>.
            apply Or.inr
            -- One of the premise coincides with the conclusion.
            exact h4
          case inr h18 =>
            -- Show the right disjunct based on <expert-advice>.
            apply Or.inr
            -- One of the premise coincides with the conclusion.
            exact h4



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_158313287706207579589739475484 : (((False ∨ (p2 ∨ p4)) → ((p3 ∨ (False ∧ p3)) ∧ (True → ((p5 ∨ ((True ∨ p5) ∧ p4)) ∧ p1)))) ∨ (True ∨ (p5 ∨ (p3 ∧ (p3 → p5))))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_39341443599065378350768624030 : (((p2 ∧ ((p4 → p4) → ((p3 ∨ (((p3 ∧ p4) → (p1 → (p4 ∧ False))) → p3)) ∨ (p3 → (((p3 ∧ p4) → p5) ∨ p5))))) ∧ p2) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_351035336231665363263635548316 : (p4 → (((((p5 ∨ (False → False)) ∨ ((p3 ∧ (p3 → ((p5 → p4) ∨ False))) ∧ (p1 ∧ (p3 → False)))) ∧ (p3 ∨ p5)) ∨ False) → (False ∨ p4))) := by
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
    -- Disjunctions on the left can always be decomposed.
    cases h4
    case inl h6 =>
      -- Disjunctions on the left can always be decomposed.
      cases h6
      case inl h7 =>
        -- Disjunctions on the left can always be decomposed.
        cases h5
        case inl h8 =>
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- One of the premise coincides with the conclusion.
          exact h1
        case inr h9 =>
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- One of the premise coincides with the conclusion.
          exact h1
      case inr h10 =>
        -- Disjunctions on the left can always be decomposed.
        cases h5
        case inl h11 =>
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- One of the premise coincides with the conclusion.
          exact h1
        case inr h12 =>
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- One of the premise coincides with the conclusion.
          exact h1
    case inr h13 =>
      -- Conjunctions on the left can always be decomposed.
      let h14 := h13.left
      let h15 := h13.right
      -- Conjunctions on the left can always be decomposed.
      let h16 := h14.left
      let h17 := h14.right
      -- Conjunctions on the left can always be decomposed.
      let h18 := h15.left
      let h19 := h15.right
      -- Disjunctions on the left can always be decomposed.
      cases h5
      case inl h20 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- One of the premise coincides with the conclusion.
        exact h1
      case inr h21 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- One of the premise coincides with the conclusion.
        exact h1
  case inr h22 =>
    -- False on the left can always be used.
    apply False.elim h22



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_742289867830800281686082984595 : ((((p1 → p2) ∨ (((False ∧ (p4 ∨ ((p2 → p1) ∨ (((((p4 → p3) ∨ False) ∧ True) ∧ False) → (p2 ∨ p2))))) ∨ p1) ∨ (True ∨ False))) ∨ p5) ∧ True) := by
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
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_171362722177936004471533406279 : ((((((p5 ∨ (True → (p4 ∨ False))) ∨ (p4 ∧ p3)) ∨ p4) ∨ (False ∨ p5)) ∧ False) ∨ (((p1 ∧ p5) ∨ ((p4 ∨ (False ∨ False)) ∨ False)) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_174475335224252835207488175276 : ((((True → (p2 → p4)) ∨ (p2 → p3)) ∧ (p5 → ((p3 → (p1 ∧ p3)) ∧ p4))) → ((((((False ∧ p3) → True) ∨ False) → p4) ∧ p2) ∨ True)) := by
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
    -- True on the right can always be proven directly.
    apply True.intro
  case inr h5 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_66466225701025638603478520171 : ((True → ((p4 ∨ ((p5 ∧ (p1 → ((True → ((p3 → (p2 ∨ (p5 ∨ ((False ∧ True) ∨ p2)))) ∨ p5)) ∧ (False ∨ p2)))) ∨ p3)) ∧ False)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_111528823663812688738767376151 : (((((p4 ∨ (((p3 ∧ (((((p1 ∨ p3) ∨ p3) ∨ (True ∨ p5)) ∨ (False → p5)) → p2)) ∧ p1) ∧ False)) ∧ p1) ∧ p4) ∨ False) ∨ (p4 → True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_695613162743980851330396889278 : (((((p5 ∨ ((p3 → (p5 → p4)) ∧ p1)) ∧ (p5 → (p3 → (True ∨ p4)))) → (((p4 ∨ (True ∨ False)) ∧ p1) ∨ ((p4 ∨ True) ∨ True))) ∨ p4) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
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
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro
  case inr h5 =>
    -- Conjunctions on the left can always be decomposed.
    let h6 := h5.left
    let h7 := h5.right
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_152215626368161840781866426956 : ((((p1 ∨ (p2 ∧ True)) ∨ (p2 ∧ p5)) ∧ ((p2 ∨ p3) → (True ∨ ((True ∨ ((p5 → True) → p1)) ∧ p4)))) → ((p1 ∨ (p3 ∧ p3)) ∨ True)) := by
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
      -- Conjunctions on the left can always be decomposed.
      let h7 := h6.left
      let h8 := h6.right
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



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_260613700313943832464712243769 : ((p3 → p2) → ((((True → p5) ∧ p5) ∧ p2) ∨ ((((((p4 ∧ p4) ∧ p1) ∨ (False ∨ p3)) ∨ (((False → p1) ∧ False) → p1)) ∨ p4) ∨ p5))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h2
  -- Conjunctions on the left can always be decomposed.
  let h3 := h2.left
  let h4 := h2.right
  -- False on the left can always be used.
  apply False.elim h4



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_45930809845063178975431871771 : (((p4 → (False → ((False ∧ (((True ∧ (True ∨ p1)) ∧ p3) → ((p5 ∧ p5) → (((p2 → p5) ∧ False) ∧ (p3 ∧ True))))) → p3))) → p1) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_40160172625755319535608704208 : (((((p2 ∨ ((p1 ∨ ((p3 ∨ p3) ∧ False)) ∧ (True ∨ False))) ∨ ((p4 ∧ ((p2 ∧ (True ∨ p2)) → (False → p5))) ∧ p1)) ∧ p2) ∨ True) ∨ False) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_783393444120647946805555852264 : (((p3 ∨ (((((p1 ∨ p3) ∨ p4) → (((p1 → p2) → (p3 ∨ (p2 → False))) → p1)) ∨ p3) → (p4 ∨ (p5 ∨ (p1 → (p3 → p1)))))) ∨ p3) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
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
    -- Implications on the right can always be decomposed.
    intro h3
    -- Implications on the right can always be decomposed.
    intro h4
    -- One of the premise coincides with the conclusion.
    exact h3
  case inr h5 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h6
    -- Implications on the right can always be decomposed.
    intro h7
    -- One of the premise coincides with the conclusion.
    exact h6
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_733347455954911269994880435616 : ((((p4 ∧ True) ∧ ((((p1 ∧ (((((p3 → p1) ∧ True) → p1) → p4) ∨ p3)) → ((True ∧ True) → (p1 → p2))) → (p4 ∨ p3)) ∨ False)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_158338494753449607460320715734 : (((p2 ∧ p1) ∧ (((((((p4 ∧ p3) → p1) ∧ (p2 ∧ False)) ∨ p2) ∧ (False → p4)) → p5) → p5)) ∨ ((p2 ∧ ((p1 → False) ∨ True)) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_51014840980590109346762621289 : (((False ∧ ((p3 → p1) → (((((p1 ∨ p2) ∨ False) ∧ p4) → ((p3 ∧ p5) ∧ p3)) ∨ True))) ∧ (((p3 ∧ p2) → (p3 → p4)) ∨ p5)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_137828992523311085611777303584 : ((p3 ∨ ((((((p4 ∨ ((p1 ∨ p5) ∧ False)) → p5) → p4) ∧ (p1 ∧ (p4 → (p1 → p4)))) ∨ p2) ∨ (True ∧ p2))) ∨ ((False ∧ p4) → p1)) := by
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
theorem thm_5_vars_345671272540376527301731143197 : (p3 → ((p1 ∨ (((True → (p1 ∨ ((p1 ∨ (((p3 → p1) ∧ p2) ∨ p4)) ∧ True))) → (True → (False ∧ p3))) ∧ ((p2 → False) → p2))) ∨ p3)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_33159909080135218166059403423 : ((p3 ∨ (p2 ∨ ((((p4 ∧ p4) ∧ p2) ∨ (p3 ∨ (((True → (False → p2)) ∨ True) → (((False → p2) ∧ p1) ∨ False)))) ∨ (True ∨ True)))) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
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
theorem thm_5_vars_349990279514521806152774648762 : (p4 → ((((p2 ∨ (p3 ∧ ((False ∨ (((p1 ∧ p4) ∧ p2) ∧ (p3 ∨ (p1 ∧ p4)))) → p4))) ∧ (p3 → ((False ∨ False) ∨ p2))) ∨ False) ∨ True)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_43925238188442894113577078717 : ((((((p5 ∨ (True ∨ ((p2 ∨ ((True ∧ (p5 → p3)) ∨ ((p5 → p3) ∨ p4))) ∨ True))) ∧ True) ∨ (p2 → p4)) ∨ (p5 ∧ p5)) → p1) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_308576560266485460933539530007 : (p2 ∨ (((p2 ∧ (True ∨ (True ∧ True))) ∨ ((p3 ∨ (p4 ∧ (p4 ∨ (True ∧ p1)))) ∨ (p4 → (p5 → (True ∧ (False → (p2 ∨ p3))))))) ∨ p4)) := by
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
  -- Implications on the right can always be decomposed.
  intro h2
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- Implications on the right can always be decomposed.
  intro h3
  -- False on the left can always be used.
  apply False.elim h3



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_668384746601229248180131539984 : ((((((((True ∨ ((p3 ∧ p5) ∨ ((p5 ∧ (p5 ∨ p1)) → (p1 ∧ p5)))) ∧ p2) → (p1 ∨ p5)) ∧ False) ∧ p2) ∨ ((True ∨ p2) ∨ False)) ∨ p5) ∧ True) := by
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
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_135614969854831896883509579903 : (((p1 ∨ ((p1 → False) ∨ ((((p3 ∨ p5) ∧ True) ∧ False) ∧ ((p4 ∨ p2) ∧ p4)))) ∨ ((p5 → (p1 → True)) ∨ p5)) ∨ ((p4 → True) ∨ False)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_177393649095722468234984404197 : ((p5 ∨ (((((p1 ∧ p3) ∨ (p1 ∧ (p4 ∨ p5))) → p3) ∧ True) ∨ True)) ∧ ((p2 ∨ (True → (p2 → ((p1 → (False ∧ p4)) ∨ p1)))) ∨ True)) := by
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
theorem thm_5_vars_256152989146436343391810362635 : ((False ∨ True) → ((((p2 ∨ ((p2 ∧ False) ∨ (((p1 ∧ p4) → (True → p4)) → p5))) ∨ (p2 ∨ (False → p1))) ∨ ((p1 → False) ∨ p2)) ∨ p1)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h2 =>
    -- False on the left can always be used.
    apply False.elim h2
  case inr h3 =>
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h4
    -- False on the left can always be used.
    apply False.elim h4



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_204365817896470937055594339747 : (((p2 ∨ (p2 → (True → False))) ∧ False) ∨ (((((p2 ∨ False) ∨ p1) ∧ p5) ∨ (p1 → (False → (((p3 → True) ∨ p5) ∧ (p2 ∨ p4))))) ∨ p1)) := by
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
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- False on the left can always be used.
  apply False.elim h2
  -- False on the left can always be used.
  apply False.elim h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_302633962259409404035354645954 : (False ∨ (p2 ∨ ((((p4 ∨ ((p4 → (True ∨ p2)) → False)) → p1) → ((((p5 → False) ∨ p1) ∧ (p3 ∧ p4)) ∧ p4)) ∨ ((p1 → p1) ∨ p5)))) := by
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
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_58893055164288623468712745874 : (((False ∧ p3) ∨ (p3 ∧ (p5 ∧ ((False → p4) ∧ (p3 ∨ (((p1 → (p1 → p2)) → p1) ∨ ((((p2 → p3) → p3) → False) ∨ p4))))))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_150437901141187706020373586481 : (((((((p1 → (((((p5 → p5) → p2) ∧ False) ∨ (p2 ∨ p4)) ∨ p5)) ∧ p2) ∧ p1) ∨ p2) → p3) ∧ p2) → ((p5 ∨ (True → False)) ∨ True)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_180186404034886643601338191368 : ((((((p1 ∨ p2) ∨ p3) ∧ p1) → ((False ∨ (False → p5)) ∨ False)) → True) → (((((True → ((p1 ∨ True) ∧ p5)) → p1) ∧ p5) ∧ True) ∨ True)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_352168996239618613140648196642 : (p4 → (((p1 ∨ (True → True)) ∧ True) ∧ (p4 → (((((p5 ∨ True) ∨ p1) → (p5 → (True → (False ∧ p3)))) → p5) ∨ ((True ∨ False) ∨ False))))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
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
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



