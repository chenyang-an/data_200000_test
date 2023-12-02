variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_207930775213828572749478770112 : (((p3 ∨ (False ∨ False)) ∧ (p2 → p4)) → (((((p3 → (p1 → ((p3 ∨ (p1 → (p2 ∧ p5))) → p4))) → p4) ∧ p5) ∨ (True ∧ True)) ∨ p4)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- Disjunctions on the left can always be decomposed.
  cases h2
  case inl h4 =>
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Conjunctions on the right can always be decomposed.
    apply And.intro
    -- True on the right can always be proven directly.
    apply True.intro
    -- True on the right can always be proven directly.
    apply True.intro
  case inr h5 =>
    -- Disjunctions on the left can always be decomposed.
    cases h5
    case inl h6 =>
      -- False on the left can always be used.
      apply False.elim h6
    case inr h7 =>
      -- False on the left can always be used.
      apply False.elim h7



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_60995749527638721364262823290 : ((False ∧ (((p3 ∨ (p3 ∧ (True → (p2 → (p1 ∧ ((True ∨ ((p1 ∨ (True ∨ p5)) ∧ True)) ∧ (True ∧ p3))))))) ∧ (p3 → p4)) → p1)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_257881696373642601324418743762 : ((p4 ∨ True) → ((((p4 ∨ p3) → p4) → p1) → (p3 → (p1 → (((p1 ∨ p4) ∧ p5) → (p2 ∨ ((True ∨ ((False ∨ p2) → False)) ∧ p1))))))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Implications on the right can always be decomposed.
  intro h3
  -- Implications on the right can always be decomposed.
  intro h4
  -- Implications on the right can always be decomposed.
  intro h5
  -- Conjunctions on the left can always be decomposed.
  let h6 := h5.left
  let h7 := h5.right
  -- Disjunctions on the left can always be decomposed.
  cases h6
  case inl h8 =>
    -- Disjunctions on the left can always be decomposed.
    cases h1
    case inl h9 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Conjunctions on the right can always be decomposed.
      apply And.intro
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- True on the right can always be proven directly.
      apply True.intro
      -- One of the premise coincides with the conclusion.
      exact h4
    case inr h10 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Conjunctions on the right can always be decomposed.
      apply And.intro
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- True on the right can always be proven directly.
      apply True.intro
      -- One of the premise coincides with the conclusion.
      exact h4
  case inr h11 =>
    -- Disjunctions on the left can always be decomposed.
    cases h1
    case inl h12 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Conjunctions on the right can always be decomposed.
      apply And.intro
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- True on the right can always be proven directly.
      apply True.intro
      -- One of the premise coincides with the conclusion.
      exact h4
    case inr h13 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Conjunctions on the right can always be decomposed.
      apply And.intro
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- True on the right can always be proven directly.
      apply True.intro
      -- One of the premise coincides with the conclusion.
      exact h4



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_303710048244981460344412972522 : (p1 ∨ (((((p4 ∨ (p2 ∨ p3)) ∧ (((p1 ∧ (((p4 ∨ (p1 → True)) ∨ False) ∧ p5)) ∨ p2) ∧ (True → (p5 ∨ False)))) ∨ True) ∧ True) ∨ False)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_773600590934387626768995147623 : (((False ∨ (((p5 ∨ True) → ((((p1 ∨ ((True ∧ (p1 ∨ p5)) → p5)) ∧ (p4 ∧ p2)) → (p2 ∧ ((p4 ∨ p5) → False))) ∧ p3)) ∨ p1)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_63954238034502148164729504513 : ((False ∨ ((p2 ∨ (False ∨ (((p2 ∧ (True ∧ (True ∨ False))) → (p3 ∨ (p2 → p5))) ∨ (((p3 ∧ (p5 → p4)) → p1) ∨ p3)))) ∨ True)) ∨ p3) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_639528608865409688798174466980 : ((((((p1 ∨ p5) ∨ p1) ∧ (((p4 → (True → False)) → (p1 → p3)) ∧ ((((((p4 → p5) → p1) ∧ p3) ∧ True) ∨ p2) ∨ p2))) → p5) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_147261129522459821844958166879 : ((((((p2 ∨ p1) → (((((p3 ∧ True) → ((True ∧ p1) ∨ True)) ∧ p1) → p4) → p3)) ∧ p4) ∨ False) ∨ p2) ∨ (p3 ∨ (True ∨ (p3 ∨ p1)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_232005956621699383199693538827 : (((p2 ∨ p4) → True) → (p3 → ((p3 → False) → ((((p4 ∨ (p5 ∨ (p4 ∨ (p3 ∨ ((p2 → p2) ∧ p4))))) → (p3 → False)) ∨ p2) ∧ p2)))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Implications on the right can always be decomposed.
  intro h3
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- We want to use the implication h3 based on <expert-advice>. So we show its premise.
  have h4 : p3 := by
    -- One of the premise coincides with the conclusion.
    exact h2
  -- We have shown the premise of h3, we can now drive its conclusion.
  let h5 := h3 h4
  -- False on the left can always be used.
  apply False.elim h5
  -- We want to use the implication h3 based on <expert-advice>. So we show its premise.
  have h6 : p3 := by
    -- One of the premise coincides with the conclusion.
    exact h2
  -- We have shown the premise of h3, we can now drive its conclusion.
  let h7 := h3 h6
  -- False on the left can always be used.
  apply False.elim h7



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_601088096764803541590119500840 : ((((p1 ∧ (p1 ∧ ((True → (True ∧ p2)) ∨ (p5 ∨ (((False ∨ p2) ∨ ((p3 ∨ True) → p3)) → (((True ∨ p4) ∨ False) → p3)))))) ∧ False) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_191268696658723352879260276936 : (((False ∨ False) ∧ ((p1 ∧ (p2 → p4)) → (p2 ∧ False))) ∨ (p2 → (((p3 ∧ p2) ∨ p4) → ((p2 ∨ (((p3 → p4) ∧ p2) ∨ False)) ∧ p2)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Disjunctions on the left can always be decomposed.
  cases h2
  case inl h3 =>
    -- Conjunctions on the left can always be decomposed.
    let h4 := h3.left
    let h5 := h3.right
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- One of the premise coincides with the conclusion.
    exact h1
  case inr h6 =>
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- One of the premise coincides with the conclusion.
    exact h1
  -- Disjunctions on the left can always be decomposed.
  cases h2
  case inl h7 =>
    -- Conjunctions on the left can always be decomposed.
    let h8 := h7.left
    let h9 := h7.right
    -- One of the premise coincides with the conclusion.
    exact h1
  case inr h10 =>
    -- One of the premise coincides with the conclusion.
    exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_624486037631512217065776789134 : ((((p4 ∨ ((p4 ∧ (((False → ((p1 ∧ p2) ∨ p1)) → ((p4 ∨ (p4 → p3)) ∨ False)) → ((True ∨ (p2 ∧ p5)) → p1))) ∧ p1)) ∨ p2) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_692039415411790079065202488620 : (((((((p1 → ((True → p3) → (False ∨ p1))) ∧ True) ∨ (p3 → p4)) ∧ True) ∧ ((((p3 ∧ p4) → (p2 ∧ p5)) ∨ p4) ∧ (False ∧ False))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_111714756495513144010908920224 : ((((((p1 ∧ ((True → (p4 ∧ (True → p1))) ∨ True)) ∨ p3) → (((True ∨ p2) → False) ∨ (p1 → (False ∨ p5)))) → p2) ∨ p2) ∨ (True ∧ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_41491967818754860975141935347 : ((((((p5 ∧ False) ∧ ((p4 ∧ p3) ∧ (p5 → (False ∧ True)))) ∨ True) → (((True → (((False ∧ p4) ∨ p5) ∨ True)) ∧ True) ∧ p4)) ∨ p1) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_301517891232790697971432333417 : (False ∨ (((False ∧ False) ∧ p5) ∨ (False ∨ ((p4 → p4) ∨ (p2 ∨ ((((p2 → p1) ∧ p4) ∧ ((p2 ∨ (False → p4)) → (p2 ∨ p1))) → p2)))))) := by
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
theorem thm_5_vars_329091270329709449934721732429 : (True → ((False → (p2 ∨ (p5 → p3))) ∧ (((p3 ∧ (((p2 → ((p4 ∧ ((True ∧ False) ∨ p4)) → p3)) → p5) → True)) ∧ (False ∨ p2)) → p3))) := by
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
  -- Conjunctions on the left can always be decomposed.
  let h4 := h3.left
  let h5 := h3.right
  -- Conjunctions on the left can always be decomposed.
  let h6 := h4.left
  let h7 := h4.right
  -- Disjunctions on the left can always be decomposed.
  cases h5
  case inl h8 =>
    -- False on the left can always be used.
    apply False.elim h8
  case inr h9 =>
    -- One of the premise coincides with the conclusion.
    exact h6



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_51162360408302429770117975733 : (((((p2 → (((p5 → ((p2 ∨ p5) ∨ (False ∧ p5))) → p3) ∧ p3)) → p2) ∧ (p1 ∨ True)) ∨ (False → (((p5 → p1) ∨ p5) → p5))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_326099232291495864318541362409 : (p5 ∨ (p1 → (((p4 → (False ∨ ((True ∧ (p5 ∧ p2)) → False))) ∨ ((p5 ∨ p2) → ((p2 → p4) ∨ ((p5 ∨ p5) ∧ (p5 ∨ True))))) ∨ p1))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_199344786389789884436273530034 : ((((p3 ∧ ((p1 ∨ p2) ∨ p4)) → False) ∨ p3) → ((((((p4 ∨ (p3 → ((p5 ∨ p1) → p3))) ∨ p3) → p3) ∧ p2) → p3) ∧ (True ∨ p2))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h2
  -- Conjunctions on the left can always be decomposed.
  let h3 := h2.left
  let h4 := h2.right
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h5 =>
    -- We want to use the implication h3 based on <expert-advice>. So we show its premise.
    have h6 : ((p4 ∨ (p3 → ((p5 ∨ p1) → p3))) ∨ p3) := by
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Implications on the right can always be decomposed.
      intro h7
      -- Implications on the right can always be decomposed.
      intro h8
      -- Disjunctions on the left can always be decomposed.
      cases h8
      case inl h9 =>
        -- One of the premise coincides with the conclusion.
        exact h7
      case inr h10 =>
        -- One of the premise coincides with the conclusion.
        exact h7
    -- We have shown the premise of h3, we can now drive its conclusion.
    let h11 := h3 h6
    -- One of the premise coincides with the conclusion.
    exact h11
  case inr h12 =>
    -- One of the premise coincides with the conclusion.
    exact h12
  -- Disjunctions on the left can always be decomposed.
  cases h1
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



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_62087541012584138873931155165 : ((p2 ∧ (p3 ∧ (((p5 → (((p4 ∨ (p4 ∨ p5)) → (p4 ∧ p4)) ∨ True)) → p2) → ((((False ∨ p3) → p4) ∧ False) ∧ (p3 → p3))))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_191900757878950264542191548296 : ((p5 ∨ ((((p1 → p4) ∨ p2) → p3) ∨ (p2 ∨ p5))) ∨ (p1 → (((False ∨ (False ∧ True)) → p1) ∧ ((False → (False ∨ (p4 ∧ p5))) ∨ p2)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h2
  -- Disjunctions on the left can always be decomposed.
  cases h2
  case inl h3 =>
    -- False on the left can always be used.
    apply False.elim h3
  case inr h4 =>
    -- Conjunctions on the left can always be decomposed.
    let h5 := h4.left
    let h6 := h4.right
    -- False on the left can always be used.
    apply False.elim h5
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h7
  -- False on the left can always be used.
  apply False.elim h7



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_654363706668484255919154061957 : (((((((((p3 ∨ p4) ∧ p4) ∨ ((p3 → p5) → p3)) → p5) ∨ (p2 → (True → (((p1 → p5) → p1) ∨ p4)))) ∨ p4) ∨ (p2 → True)) ∨ False) ∧ True) := by
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
theorem thm_5_vars_354930909302457355678028065855 : (p5 → ((p3 ∨ (p3 ∧ (((((p1 ∨ (p1 ∧ (p4 ∧ p1))) ∨ False) ∨ ((p5 ∧ (p4 ∧ p5)) ∨ p4)) → (True → (p1 ∨ p4))) ∧ p3))) ∨ True)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_692644209957787118103279682433 : (((((p2 ∧ (p1 → ((True ∨ (p5 → True)) → p4))) → (p3 ∧ (p1 ∨ p1))) ∧ (p5 ∨ (((p2 → p3) ∧ ((p1 → p5) → False)) ∨ p4))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_206503836006726368465692059382 : ((p5 ∨ (True ∧ (p3 → (False ∧ p1)))) ∨ ((((p1 → (False ∧ (p1 ∨ p5))) → (p4 → ((p1 ∨ p5) ∧ (False ∧ p3)))) ∨ p2) → (p1 → p1))) := by
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
theorem thm_5_vars_26617862640082489909226007383 : (((p2 ∧ p5) ∨ (((((p3 ∨ p2) ∧ ((((p2 → p4) → ((((p1 ∧ False) ∨ p3) → True) ∨ p2)) ∧ True) ∨ p3)) ∧ p4) ∨ p2) ∨ True)) ∧ True) := by
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
theorem thm_5_vars_316474794978284369125018444802 : (p3 ∨ (p1 ∨ (True → (((((True → (p1 → (p4 → (p1 ∧ p3)))) ∨ (p5 ∧ True)) → (p2 ∨ (False ∨ (p4 → p5)))) ∨ True) ∨ (True ∨ p5))))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_323830194028748887716556845399 : (p5 ∨ ((((((False ∧ p2) → (True ∧ p1)) → False) ∧ (p4 → p2)) ∧ ((False → p3) ∨ (p1 → p5))) → ((((p4 → p1) ∧ p4) ∨ p5) ∧ True))) := by
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
  cases h3
  case inl h6 =>
    -- We want to use the implication h4 based on <expert-advice>. So we show its premise.
    have h7 : ((False ∧ p2) → (True ∧ p1)) := by
      -- Implications on the right can always be decomposed.
      intro h8
      -- Conjunctions on the right can always be decomposed.
      apply And.intro
      -- True on the right can always be proven directly.
      apply True.intro
      -- Conjunctions on the left can always be decomposed.
      let h9 := h8.left
      let h10 := h8.right
      -- False on the left can always be used.
      apply False.elim h9
    -- We have shown the premise of h4, we can now drive its conclusion.
    let h11 := h4 h7
    -- False on the left can always be used.
    apply False.elim h11
  case inr h12 =>
    -- We want to use the implication h4 based on <expert-advice>. So we show its premise.
    have h13 : ((False ∧ p2) → (True ∧ p1)) := by
      -- Implications on the right can always be decomposed.
      intro h14
      -- Conjunctions on the right can always be decomposed.
      apply And.intro
      -- True on the right can always be proven directly.
      apply True.intro
      -- Conjunctions on the left can always be decomposed.
      let h15 := h14.left
      let h16 := h14.right
      -- False on the left can always be used.
      apply False.elim h15
    -- We have shown the premise of h4, we can now drive its conclusion.
    let h17 := h4 h13
    -- False on the left can always be used.
    apply False.elim h17
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_260771288457105932693047019166 : ((p3 → p5) → ((p4 ∨ (((p2 → (p2 ∨ (p1 ∨ ((True ∨ p4) ∧ (p1 ∧ p2))))) → p1) ∧ ((True → True) ∧ ((p2 → p2) ∨ p5)))) ∨ True)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_139605677646180279679918655364 : ((((((p1 ∧ (p3 ∨ (p2 → ((p2 ∨ False) → False)))) → p3) ∧ p2) ∨ (((True ∧ (p4 → p1)) ∨ False) → True)) → False) → (p4 ∨ (p3 ∨ p5))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h2 : ((((p1 ∧ (p3 ∨ (p2 → ((p2 ∨ False) → False)))) → p3) ∧ p2) ∨ (((True ∧ (p4 → p1)) ∨ False) → True)) := by
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h3
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h4 := h1 h2
  -- False on the left can always be used.
  apply False.elim h4



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_62535309933473269873298026737 : ((p3 ∧ (False ∨ ((((((p3 → p5) ∨ True) → p1) ∧ p2) ∨ p3) ∧ (False ∧ ((False ∨ True) ∧ ((p2 → (p4 ∨ (p4 ∧ p4))) ∧ False)))))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_232962664238966840974382534791 : ((p3 ∧ (True → False)) → (p1 → (((p3 ∨ ((p4 ∧ p2) ∨ ((False → (p3 ∨ p4)) → True))) → (p2 ∨ (False ∧ (False ∨ p1)))) ∧ (p5 → p3)))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h3
  -- Disjunctions on the left can always be decomposed.
  cases h3
  case inl h4 =>
    -- Conjunctions on the left can always be decomposed.
    let h5 := h1.left
    let h6 := h1.right
    -- We want to use the implication h6 based on <expert-advice>. So we show its premise.
    have h7 : True := by
      -- True on the right can always be proven directly.
      apply True.intro
    -- We have shown the premise of h6, we can now drive its conclusion.
    let h8 := h6 h7
    -- False on the left can always be used.
    apply False.elim h8
  case inr h9 =>
    -- Disjunctions on the left can always be decomposed.
    cases h9
    case inl h10 =>
      -- Conjunctions on the left can always be decomposed.
      let h11 := h10.left
      let h12 := h10.right
      -- Conjunctions on the left can always be decomposed.
      let h13 := h1.left
      let h14 := h1.right
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- One of the premise coincides with the conclusion.
      exact h12
    case inr h15 =>
      -- Conjunctions on the left can always be decomposed.
      let h16 := h1.left
      let h17 := h1.right
      -- We want to use the implication h17 based on <expert-advice>. So we show its premise.
      have h18 : True := by
        -- True on the right can always be proven directly.
        apply True.intro
      -- We have shown the premise of h17, we can now drive its conclusion.
      let h19 := h17 h18
      -- False on the left can always be used.
      apply False.elim h19
  -- Implications on the right can always be decomposed.
  intro h20
  -- Conjunctions on the left can always be decomposed.
  let h21 := h1.left
  let h22 := h1.right
  -- One of the premise coincides with the conclusion.
  exact h21



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_111202231686638788345383355556 : (((((False → p4) ∧ p2) ∨ (((p1 ∨ ((p4 ∧ p4) → p5)) ∧ True) ∨ (((((True → False) ∨ True) → True) → p1) ∧ p3))) ∧ p2) ∨ (False → p3)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_134058447633784897218407449786 : ((((p3 → ((True ∧ ((p3 ∧ ((p4 ∨ False) → p2)) ∧ (((p5 → True) → p1) → (p1 → False)))) → False)) ∨ True) ∨ False) ∨ ((p4 ∧ p3) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_114213272922517865256842075744 : ((((False ∧ (p1 → p2)) → (p4 → (p3 ∧ (((p5 ∧ p2) ∨ (p3 → (p5 ∧ (p1 ∧ True)))) → p5)))) → (p4 ∨ (p5 ∧ p5))) ∨ (True ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_217008570917406672605109052914 : ((((False ∧ p4) ∧ True) ∨ p1) → (((((False ∧ (p2 ∨ p4)) → False) ∨ ((p3 ∧ p4) → p4)) ∨ p5) → (((p2 ∧ p2) ∧ (p3 ∨ p5)) ∨ True))) := by
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
      cases h1
      case inl h5 =>
        -- Conjunctions on the left can always be decomposed.
        let h6 := h5.left
        let h7 := h5.right
        -- Conjunctions on the left can always be decomposed.
        let h8 := h6.left
        let h9 := h6.right
        -- False on the left can always be used.
        apply False.elim h8
      case inr h10 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- True on the right can always be proven directly.
        apply True.intro
    case inr h11 =>
      -- Disjunctions on the left can always be decomposed.
      cases h1
      case inl h12 =>
        -- Conjunctions on the left can always be decomposed.
        let h13 := h12.left
        let h14 := h12.right
        -- Conjunctions on the left can always be decomposed.
        let h15 := h13.left
        let h16 := h13.right
        -- False on the left can always be used.
        apply False.elim h15
      case inr h17 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- True on the right can always be proven directly.
        apply True.intro
  case inr h18 =>
    -- Disjunctions on the left can always be decomposed.
    cases h1
    case inl h19 =>
      -- Conjunctions on the left can always be decomposed.
      let h20 := h19.left
      let h21 := h19.right
      -- Conjunctions on the left can always be decomposed.
      let h22 := h20.left
      let h23 := h20.right
      -- False on the left can always be used.
      apply False.elim h22
    case inr h24 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- True on the right can always be proven directly.
      apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_190134133554961101364009927102 : ((((p1 ∨ p2) ∧ ((True → (p3 → p4)) ∧ True)) ∧ p2) ∨ (((((p4 ∨ (p5 ∧ (p4 → p1))) → p3) ∧ p1) ∨ ((False ∧ p1) → False)) ∨ p4)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
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
theorem thm_5_vars_42500779004959750331691440280 : (((False ∨ (((p3 ∧ ((True → p3) ∧ p1)) ∧ (((True ∨ True) → ((p2 ∧ (True ∧ p3)) ∨ p4)) ∨ p3)) ∨ (p4 → (p4 ∨ p5)))) ∨ p4) ∨ p2) := by
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
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_115519712470305975055890863043 : ((((True ∨ p3) ∧ (((p1 → p4) ∧ p4) → p4)) → (True → (p2 ∧ ((p5 ∧ p3) → (((True ∧ p3) ∧ p4) → (p4 ∧ False)))))) ∨ (p3 ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_165898835485740482867305398700 : (((p4 ∧ (p5 → p2)) → ((p2 ∧ False) ∨ ((p3 ∧ (p2 ∧ ((p2 → p2) ∨ p3))) ∧ p3))) ∨ ((False → ((p4 ∧ (p3 ∨ p2)) → p4)) ∨ p4)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
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
  cases h4
  case inl h5 =>
    -- False on the left can always be used.
    apply False.elim h1
  case inr h6 =>
    -- False on the left can always be used.
    apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_179199410788958942344549527216 : ((p3 ∧ (p1 ∨ ((p5 ∧ p1) ∨ ((True → (p1 → False)) → (p4 ∨ True))))) ∨ ((False ∧ (p1 ∧ (p5 ∧ (p4 → ((False ∨ True) ∧ p5))))) → p2)) := by
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
theorem thm_5_vars_46265243562790240040666068378 : ((((p3 ∧ (False ∨ ((((p3 ∧ p1) ∧ (p5 ∨ ((p2 ∨ (False ∧ (p5 ∨ p1))) ∨ p1))) → p2) → True))) → (False ∧ True)) ∧ (p5 → p3)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_55870235594913915814683898931 : (((True ∨ ((True ∧ p3) ∧ p1)) ∧ (((p5 → (p4 ∨ p2)) → p2) ∧ ((p2 ∨ ((p3 ∨ ((p5 → False) ∧ (p4 ∨ p5))) ∧ p2)) ∨ p3))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_349977838589447893343599040681 : (p4 → (((((((p5 ∨ (p2 ∨ ((p1 ∨ p5) → p2))) → p5) ∧ (p1 → ((p5 → p2) ∧ (p5 → (p4 ∨ p3))))) ∧ p4) ∨ p5) ∨ p3) ∨ True)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_138048131893456491995147059410 : ((True → (((True ∨ True) → p4) → ((((p3 → p4) → p3) ∨ (p1 ∨ p4)) → (p2 → (p5 ∧ ((p3 ∧ True) ∧ p3)))))) ∨ ((True ∨ p3) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_218221409351444291325101507033 : (((p4 ∧ p3) ∨ (p5 ∧ p5)) → ((p3 ∧ (True ∨ (p3 → p2))) → (((False ∨ False) ∧ ((p4 ∧ p5) → (p2 → (True ∧ p4)))) ∨ (True ∧ p3)))) := by
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
    -- Disjunctions on the left can always be decomposed.
    cases h1
    case inl h6 =>
      -- Conjunctions on the left can always be decomposed.
      let h7 := h6.left
      let h8 := h6.right
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Conjunctions on the right can always be decomposed.
      apply And.intro
      -- True on the right can always be proven directly.
      apply True.intro
      -- One of the premise coincides with the conclusion.
      exact h8
    case inr h9 =>
      -- Conjunctions on the left can always be decomposed.
      let h10 := h9.left
      let h11 := h9.right
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Conjunctions on the right can always be decomposed.
      apply And.intro
      -- True on the right can always be proven directly.
      apply True.intro
      -- One of the premise coincides with the conclusion.
      exact h3
  case inr h12 =>
    -- Disjunctions on the left can always be decomposed.
    cases h1
    case inl h13 =>
      -- Conjunctions on the left can always be decomposed.
      let h14 := h13.left
      let h15 := h13.right
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Conjunctions on the right can always be decomposed.
      apply And.intro
      -- True on the right can always be proven directly.
      apply True.intro
      -- One of the premise coincides with the conclusion.
      exact h15
    case inr h16 =>
      -- Conjunctions on the left can always be decomposed.
      let h17 := h16.left
      let h18 := h16.right
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Conjunctions on the right can always be decomposed.
      apply And.intro
      -- True on the right can always be proven directly.
      apply True.intro
      -- One of the premise coincides with the conclusion.
      exact h3



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_314009492910539359640654849125 : (p3 ∨ ((p2 ∧ (p1 ∧ (p4 ∨ (False ∨ (((p4 ∨ (p3 ∨ p3)) ∨ (False → (True ∨ ((p3 → p2) ∧ (p2 ∨ True))))) → True))))) ∨ (True ∧ True))) := by
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
theorem thm_5_vars_98805521660096037434626052213 : ((True → ((((True ∨ (False → p1)) ∨ (((p1 → (p5 → False)) → (p1 → ((p3 ∧ False) ∧ (p3 ∨ p3)))) ∨ True)) ∨ (False → False)) ∧ p5)) → p5) := by
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
  -- One of the premise coincides with the conclusion.
  exact h4



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_357995758532579255632182211578 : (p5 → (False ∨ ((((p3 → True) ∨ (((True ∧ False) ∧ False) → (False → p3))) → p1) ∨ (((p4 ∧ p5) ∨ (((True ∧ False) → p1) → True)) ∨ p4)))) := by
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
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_635845008320589097086421654044 : ((((((p2 → True) ∧ (p3 ∨ (p1 ∧ ((p4 → (p3 ∨ (p2 → ((False ∧ p4) ∧ True)))) → p5)))) → (p3 → ((p5 ∨ p1) → p1))) → p5) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_56712877594076458483417895220 : ((((p5 ∧ p3) ∨ False) ∧ (((p5 ∨ (p5 ∨ ((False → p5) ∨ (p1 ∧ False)))) → ((p4 ∧ (((True → False) → True) → True)) ∧ p1)) ∧ p2)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_656151802850528309571003761178 : ((((((False ∧ (((((p3 ∨ p3) ∨ (True → p2)) ∧ p5) ∨ p3) ∨ p4)) ∨ p5) ∨ (((p1 ∨ False) ∧ (p5 ∨ p1)) ∧ p4)) ∨ (False → p4)) ∨ p5) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- False on the left can always be used.
  apply False.elim h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_247392917020991537574153660845 : ((False ∨ p1) ∨ (p3 ∨ (p5 → ((p4 ∧ ((p3 ∨ p3) ∧ (p4 ∧ ((True ∧ (p4 ∧ p2)) ∨ (True ∧ p3))))) ∨ ((False ∧ (True ∨ p2)) → True))))) := by
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
theorem thm_5_vars_45931244671788490192376770012 : (((p4 → (p1 → ((True → (p3 ∧ ((False → (((p4 ∧ p3) ∨ ((p5 ∨ p3) ∨ p4)) → (p2 ∧ (p5 ∧ p3)))) ∧ True))) ∧ False))) → False) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_122196708679526194368263269467 : (((((p2 ∨ p2) → ((p1 ∨ (True ∧ ((p1 ∨ True) ∧ ((True → p3) → True)))) ∧ True)) → ((p1 ∧ p1) ∧ True)) ∧ (p5 → False)) → (True ∧ p1)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
  have h4 : ((p2 ∨ p2) → ((p1 ∨ (True ∧ ((p1 ∨ True) ∧ ((True → p3) → True)))) ∧ True)) := by
    -- Implications on the right can always be decomposed.
    intro h5
    -- Conjunctions on the right can always be decomposed.
    apply And.intro
    -- Disjunctions on the left can always be decomposed.
    cases h5
    case inl h6 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Conjunctions on the right can always be decomposed.
      apply And.intro
      -- True on the right can always be proven directly.
      apply True.intro
      -- Conjunctions on the right can always be decomposed.
      apply And.intro
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- True on the right can always be proven directly.
      apply True.intro
      -- Implications on the right can always be decomposed.
      intro h7
      -- True on the right can always be proven directly.
      apply True.intro
    case inr h8 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Conjunctions on the right can always be decomposed.
      apply And.intro
      -- True on the right can always be proven directly.
      apply True.intro
      -- Conjunctions on the right can always be decomposed.
      apply And.intro
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- True on the right can always be proven directly.
      apply True.intro
      -- Implications on the right can always be decomposed.
      intro h9
      -- True on the right can always be proven directly.
      apply True.intro
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h2, we can now drive its conclusion.
  let h10 := h2 h4
  -- We need to get the left conjuct of h10 based on <expert-advice>.
  let h11 := h10.left
  -- We need to get the left conjuct of h11 based on <expert-advice>.
  let h12 := h11.left
  -- One of the premise coincides with the conclusion.
  exact h12



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_179052179546400441840778263105 : (((p4 → True) → (((p5 ∨ p4) → (False ∨ (False ∧ True))) ∨ (p3 ∨ True))) ∨ ((((p1 ∨ False) ∧ True) → p2) → ((p3 ∧ (False ∨ False)) ∧ p4))) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_115310279732024186272326302920 : (((((((p3 → p2) → p4) ∧ p1) ∨ True) → (p1 ∨ p2)) → ((((p2 ∨ p2) → ((p5 ∧ (p4 ∧ p2)) ∨ True)) ∨ True) ∨ True)) ∨ (p4 → p4)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_138157592101723116222945191969 : ((p1 → ((p5 → (p2 ∨ ((((((p3 ∧ p2) ∧ p3) → p2) ∨ (p1 → (p1 → (p5 ∧ p3)))) ∨ p2) → p1))) → p3)) ∨ ((p2 → p2) ∨ p1)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_762745837013033203790346591313 : (((p3 ∧ ((((True ∨ p4) ∧ p4) ∧ (p4 ∨ (p1 ∧ (p2 → p2)))) ∨ ((p2 ∧ False) ∧ (((p1 ∨ (p4 ∨ p4)) ∨ p3) → (True ∨ p1))))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_621912923891909992471510394699 : ((((p1 ∧ (False ∧ ((((p4 ∨ (p1 → ((False → p1) ∨ ((p4 → p3) ∧ p3)))) ∨ False) ∧ (p5 ∨ (p1 → (p2 → p5)))) ∨ True))) ∨ True) ∨ p4) ∧ True) := by
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
theorem thm_5_vars_114289764786200112102709162091 : (((((((p2 ∧ ((p3 ∧ p2) ∧ (p2 → p3))) → (True ∧ p3)) ∧ p4) ∨ p5) ∧ (False ∨ p1)) ∧ (p1 → ((p4 ∧ p2) ∧ p3))) ∨ (False → False)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_126687356903217769288201670257 : ((p4 ∧ (((p3 ∧ (((p1 ∧ ((p3 → p1) → (p2 → p2))) ∧ p1) → ((p2 ∧ True) ∨ True))) ∨ ((True → p3) → False)) → p5)) → (p5 ∨ p4)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_117158080661402899545544688724 : ((True ∧ (((((p5 ∧ (((True ∨ (p1 → False)) ∧ p5) → ((p5 ∧ p2) → (True → p4)))) → p4) ∨ p1) → (p3 ∨ p2)) ∨ True)) ∨ (p4 ∧ p5)) := by
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
theorem thm_5_vars_347107330734817599416838587984 : (p3 → (((((p3 ∨ p1) ∨ p2) ∧ (p1 ∨ (p4 ∧ p1))) → (p4 ∨ (p4 ∧ p3))) ∨ (p3 ∧ ((False ∨ (p2 ∧ (p4 ∨ p5))) → (p3 ∨ p1))))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- One of the premise coincides with the conclusion.
  exact h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Disjunctions on the left can always be decomposed.
  cases h2
  case inl h3 =>
    -- False on the left can always be used.
    apply False.elim h3
  case inr h4 =>
    -- Conjunctions on the left can always be decomposed.
    let h5 := h4.left
    let h6 := h4.right
    -- Disjunctions on the left can always be decomposed.
    cases h6
    case inl h7 =>
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- One of the premise coincides with the conclusion.
      exact h1
    case inr h8 =>
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- One of the premise coincides with the conclusion.
      exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_613270642259508444286714247651 : ((((((False → (p5 ∧ (p3 ∧ (False ∧ p2)))) ∧ ((p1 ∨ True) ∧ (p3 → (False ∨ (((p3 → True) ∨ False) ∨ p1))))) → (p4 ∧ p4)) ∨ True) ∨ p2) ∧ True) := by
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
theorem thm_5_vars_134367368320356625993100034322 : (((p2 ∨ ((((((p4 ∨ False) ∧ p5) → ((True ∧ False) ∧ (p3 → p4))) ∧ (p2 → (True ∧ p4))) → p3) ∧ p5)) ∨ True) ∨ ((p4 ∨ p2) ∧ p2)) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_150455880028629157823270693413 : (((((False → p1) ∨ (p4 ∨ ((((p5 ∧ (p2 ∧ False)) ∨ True) → (p4 ∨ p5)) ∨ (p2 ∨ p4)))) → p5) ∧ p3) → (p2 ∨ ((p1 ∨ True) ∨ p2))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_148002423359845002072378361707 : ((((p5 → ((True ∧ (((p4 → True) → p2) ∧ p4)) → ((False ∧ (p5 ∨ p2)) ∨ p3))) → p5) ∨ (p4 ∧ False)) ∨ (False → (p4 ∧ (True ∧ p4)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- False on the left can always be used.
  apply False.elim h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_324512876295458094833855403283 : (p5 ∨ ((p5 ∨ ((p5 ∨ False) → p1)) ∨ (p2 → (p5 → ((True ∧ (((False ∨ p4) ∧ (p2 ∧ (p4 ∨ (False → p4)))) ∨ True)) ∨ (False → p5)))))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
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
theorem thm_5_vars_57300596045399591111061086119 : ((((p4 → p2) → p5) ∨ (True → (p1 ∧ ((p2 ∧ (((p5 ∧ ((p3 ∧ ((False ∧ p2) ∨ True)) ∨ (p1 → True))) ∨ p1) ∧ p2)) → p5)))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_752600448002678764745310513662 : (((False ∧ ((((((p4 ∧ ((p2 ∨ (p5 ∧ ((((p5 ∧ p1) ∧ p5) ∧ (p3 → p4)) ∧ p2))) → p1)) ∨ p1) ∧ p1) ∧ False) ∨ p3) ∨ p5)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_114356521392815982663908896374 : (((((False ∧ (False ∧ (((False ∨ (False ∧ p5)) ∨ ((p3 ∧ False) → p1)) ∨ p1))) ∧ p3) ∧ p2) ∨ ((p4 ∧ p5) → (p2 ∨ p5))) ∨ (False ∨ p2)) := by
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
  -- One of the premise coincides with the conclusion.
  exact h3



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_227424696407806167101549069163 : (((p5 → p1) → p1) ∨ (p1 → ((p2 ∧ ((p5 ∧ (p4 → ((True ∨ (p1 ∧ (p1 → (p1 ∨ p3)))) → p5))) → p1)) ∨ ((p4 ∧ True) → True)))) := by
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
theorem thm_5_vars_748199686700140087531924649382 : ((((p1 → p5) → (((p4 ∧ p2) ∧ (p3 ∨ (p1 ∧ ((p1 → (True ∨ (False ∧ True))) ∧ p3)))) ∨ (((p3 ∧ False) ∨ (p3 ∨ p5)) ∧ p5))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_54711717853008157511488037357 : ((((p4 → ((False ∨ p2) ∨ p2)) ∨ (True ∨ p1)) → ((((p1 ∧ True) ∧ p2) → (p3 ∨ p5)) ∨ (p2 ∨ ((p3 → p1) ∧ (p1 → p5))))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_346787148288033742822410145947 : (p3 → (((p2 ∨ (False ∧ (p2 ∧ p5))) ∧ ((p2 → p4) ∨ (((True ∨ (p1 → (p4 → p5))) ∧ p5) ∧ p2))) ∨ (((p5 ∨ True) ∨ False) → True))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h2
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_115189801297771088772857888613 : (((((p3 → (p2 ∧ True)) ∨ p5) → (p3 → (p1 → True))) ∧ (((True ∨ (False → p5)) → (p4 → ((p5 ∨ p2) → p3))) ∧ p5)) ∨ (p5 → p5)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_136421899805782200499919536501 : ((((p4 ∧ (p4 → p5)) ∨ p4) → (((p5 → p1) → False) ∨ ((False → (p3 ∧ p5)) ∧ (p5 → (p5 ∨ (p3 ∨ False)))))) ∨ ((p5 ∧ p1) → False)) := by
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
    -- Conjunctions on the right can always be decomposed.
    apply And.intro
    -- Implications on the right can always be decomposed.
    intro h5
    -- Conjunctions on the right can always be decomposed.
    apply And.intro
    -- False on the left can always be used.
    apply False.elim h5
    -- False on the left can always be used.
    apply False.elim h5
    -- Implications on the right can always be decomposed.
    intro h6
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- One of the premise coincides with the conclusion.
    exact h6
  case inr h7 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Conjunctions on the right can always be decomposed.
    apply And.intro
    -- Implications on the right can always be decomposed.
    intro h8
    -- Conjunctions on the right can always be decomposed.
    apply And.intro
    -- False on the left can always be used.
    apply False.elim h8
    -- False on the left can always be used.
    apply False.elim h8
    -- Implications on the right can always be decomposed.
    intro h9
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- One of the premise coincides with the conclusion.
    exact h9



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_659293089779933314194071549771 : ((((p5 → ((((p5 ∨ (p1 → (p1 ∨ ((p4 → ((p5 → False) ∧ True)) ∧ False)))) → (p3 ∨ p3)) ∨ p2) ∧ (p1 ∧ p5))) ∨ (False → p3)) ∨ p5) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- False on the left can always be used.
  apply False.elim h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_312323065177504150715119565925 : (p2 ∨ (p2 → ((False ∧ p3) ∨ (((p4 ∧ False) → True) ∧ (True → (((False ∨ ((((p3 ∧ True) → True) ∧ p4) ∨ p1)) ∨ (p3 → p2)) ∨ p1)))))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h2
  -- True on the right can always be proven directly.
  apply True.intro
  -- Implications on the right can always be decomposed.
  intro h3
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h4
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_677305245487812508882788975782 : (((((False ∧ (p2 → ((((p4 ∧ p4) ∨ True) ∨ p1) ∧ ((False → p3) ∨ ((p5 → p1) ∧ p4))))) ∧ p1) ∨ (False ∨ (p2 → (p2 ∨ True)))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_47268147758647832912318975026 : (((((False ∧ (p1 ∨ p5)) → p2) ∧ ((((p2 ∧ p1) → p2) ∧ (p2 → (p4 → p2))) → (p2 ∨ ((p5 → p1) → p2)))) ∨ (p1 → p1)) ∨ p5) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_790215051621739451333025601775 : (((p5 ∨ (False ∧ (((False ∧ (((p1 ∧ ((p4 → True) ∨ True)) ∨ p2) ∧ False)) ∨ False) ∧ ((True → ((p2 ∧ p3) ∨ p5)) ∨ (p3 → p3))))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_350125700696936737441505419489 : (p4 → ((((p5 ∨ (((True ∧ True) → (p2 ∧ (((p2 → p5) ∨ p3) → p4))) ∧ p4)) ∨ p1) → (p3 ∧ ((p5 ∨ p4) ∨ (False ∨ p3)))) ∨ True)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_165950024092869263673014715708 : (((p3 ∨ p3) ∧ (((p3 ∨ (p5 → (p3 ∨ True))) → (p5 → ((p1 ∨ True) ∧ True))) ∧ p2)) ∨ (((p1 ∧ False) ∧ ((p2 ∨ p2) ∨ True)) → False)) := by
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
  apply False.elim h5



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_41189487415379040962565996392 : ((((((False ∨ ((p4 → False) ∨ p1)) ∨ p5) ∧ ((((p4 → p4) ∨ p4) ∨ (False → (p5 ∧ p4))) ∨ p2)) → (p2 ∨ (True → p1))) ∨ True) ∨ p2) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_49127901436133876952442960631 : (((((((p2 → p5) → (p3 → p1)) ∨ p2) ∧ ((p1 ∨ p4) ∧ p4)) ∨ ((True ∧ ((p2 ∧ p4) ∨ p2)) ∨ p5)) ∨ (p2 ∧ (p4 ∧ p1))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_670333554627175525690857442413 : (((((p3 → (p2 ∨ p5)) ∧ ((p3 → (p1 ∨ p2)) ∧ ((p2 ∧ ((p5 ∨ (p3 ∨ p4)) → (p3 ∧ p3))) ∧ p1))) ∨ (p4 → (p4 ∨ p5))) ∨ p4) ∧ True) := by
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
  -- One of the premise coincides with the conclusion.
  exact h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_215957759101550091330465961706 : ((p4 ∨ ((p3 ∧ p4) ∨ p4)) ∨ (p4 ∨ ((p4 → (p2 → p2)) ∨ ((True ∨ (p2 ∨ ((p4 ∨ (False → (False → (p5 ∨ p4)))) ∧ p1))) ∨ p1)))) := by
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
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_723227330698852163315199223386 : (((((p2 → False) ∨ p3) ∧ ((p1 ∨ (p1 ∨ (p2 ∧ p3))) ∧ ((p2 ∧ ((p1 ∨ (((False ∧ p3) ∧ p1) ∨ (p3 → p3))) ∧ p2)) → False))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_25226612397342814935975915921 : ((((p5 ∨ p4) ∧ p2) → ((p5 → ((p4 → (True ∧ (p1 → p1))) → (p1 ∨ p4))) ∨ ((True ∨ ((p3 ∧ (p5 ∧ True)) ∧ p1)) ∧ p5))) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
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
    -- Conjunctions on the right can always be decomposed.
    apply And.intro
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- True on the right can always be proven directly.
    apply True.intro
    -- One of the premise coincides with the conclusion.
    exact h4
  case inr h5 =>
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Implications on the right can always be decomposed.
    intro h6
    -- Implications on the right can always be decomposed.
    intro h7
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h5
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_677536026317689615778240878283 : (((((p5 ∧ ((p4 → (((p1 ∨ p3) ∧ (((False ∧ p2) ∨ (p2 ∧ False)) ∨ p4)) ∨ False)) ∨ p5)) ∨ True) ∨ (p4 ∧ ((p1 ∧ p4) ∧ p3))) ∨ p4) ∧ True) := by
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
theorem thm_5_vars_215421943471247847927531426283 : ((p3 ∧ ((p4 ∨ p5) ∧ False)) ∨ ((p5 ∧ p3) → (p1 ∨ ((False ∨ True) → ((p1 ∨ ((p4 ∨ False) ∨ p1)) ∨ (p4 → (p3 ∧ (p5 ∨ p4)))))))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
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
    -- Implications on the right can always be decomposed.
    intro h7
    -- Conjunctions on the right can always be decomposed.
    apply And.intro
    -- One of the premise coincides with the conclusion.
    exact h3
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- One of the premise coincides with the conclusion.
    exact h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_4293516252723835750520098262 : (True → ((p4 → (False ∧ (p3 ∧ (p3 ∨ p3)))) ∨ ((p1 ∨ (((p4 ∨ (p1 → False)) ∧ p2) ∨ (False → ((p4 ∨ p4) → p3)))) ∨ False))) := by
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
  -- Implications on the right can always be decomposed.
  intro h2
  -- Implications on the right can always be decomposed.
  intro h3
  -- Disjunctions on the left can always be decomposed.
  cases h3
  case inl h4 =>
    -- False on the left can always be used.
    apply False.elim h2
  case inr h5 =>
    -- False on the left can always be used.
    apply False.elim h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_156613259753122927237260839761 : ((((p3 ∨ ((((p2 ∨ True) ∨ (((p1 ∧ (p2 → p4)) → p2) → p1)) → True) → p2)) ∧ p3) ∧ p3) ∨ (((p4 ∨ p4) ∧ p4) ∨ (True ∧ True))) := by
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
theorem thm_5_vars_350930269225658918495729021146 : (p4 → ((((p4 ∧ (((False → (True ∨ p2)) ∧ (p4 ∨ p4)) → p4)) ∧ (((p1 ∨ (p5 ∨ False)) → (p4 → p3)) ∨ p3)) → p5) ∨ (False → True))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h2
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_40309464222170199153654431938 : (((((((((p4 → p3) → (True ∧ p2)) ∨ True) ∨ (p1 ∧ True)) ∧ ((False ∨ (False ∨ ((p3 ∧ p5) → p4))) ∧ p3)) ∧ p3) ∨ p2) ∨ p3) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_147241048000956166614938493860 : (((((p4 ∧ (p1 → (p3 ∧ ((p3 ∧ (p1 ∧ p2)) ∧ (p5 ∨ p3))))) → (False ∧ (p3 ∨ p1))) ∧ True) ∨ p2) ∨ (True ∨ ((p4 ∨ False) ∨ p2))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_111406769599140064109731152009 : (((p2 ∨ ((((p2 ∨ p5) ∨ p5) ∨ (p1 → (p1 → p3))) ∧ ((p1 → ((p5 ∨ (False ∨ p1)) ∨ (p4 ∨ p4))) ∨ False))) ∧ p1) ∨ (p2 → p2)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- One of the premise coincides with the conclusion.
  exact h1



