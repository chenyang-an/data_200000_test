variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_112121723886405971459779907851 : (((True ∧ ((True ∧ (p5 ∧ (p5 ∧ ((p3 ∨ p3) ∨ (p5 → ((p1 ∧ (True → True)) ∧ True)))))) ∧ (p2 ∨ (p1 ∨ p4)))) ∨ True) ∨ (p3 ∨ False)) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_763377363521182832487429603673 : (((p3 ∧ (True ∧ (((((True ∨ ((p5 ∨ p2) ∧ p1)) → p2) → (p2 ∧ p3)) ∨ (((p3 → True) → (p3 ∧ False)) → (False → p2))) ∧ p2))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_205634665338859455502967379011 : (((p3 ∧ p3) ∨ ((p1 ∨ p5) ∨ p3)) ∨ (p2 → (p2 ∧ (p2 ∧ (p1 ∨ (True ∨ (((True → (False ∨ p5)) → p1) → ((p3 ∧ False) ∧ p4)))))))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- One of the premise coincides with the conclusion.
  exact h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- One of the premise coincides with the conclusion.
  exact h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_740482627860842792096744679477 : ((((p1 ∨ p5) ∨ (((((p5 ∨ p1) ∧ p4) ∧ (p4 → p3)) → (p3 ∧ (((p4 → p4) ∧ p2) ∧ (True ∧ p1)))) → ((True ∧ p2) → p4))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_172950995665770564332900480611 : ((p3 ∧ (p4 ∨ (p1 ∨ (((p3 ∨ (p5 ∨ p3)) → (p4 → True)) → (True → p3))))) ∨ (((((p1 ∨ p5) → (p4 ∨ p4)) → True) ∨ p3) ∨ p2)) := by
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



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_769064975293898885255945980997 : (((p5 ∧ (((p1 → p1) ∨ p4) → ((p2 ∧ (((p5 → ((True ∧ (True ∧ p2)) ∧ (p4 → (p1 ∨ p1)))) ∧ (False ∧ True)) → p5)) → p5))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_719531640137653658662634990080 : ((((p3 ∨ ((p1 → p2) ∨ p2)) ∨ (True → (p5 ∨ ((((((p5 → False) → p1) ∨ (p1 → p1)) ∨ (True → p3)) ∧ p4) ∨ (p1 → p1))))) ∨ p2) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h2
  -- One of the premise coincides with the conclusion.
  exact h2
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_196723971187913127746903874397 : (((((False ∧ p2) → (False ∧ False)) → p2) ∧ p1) ∨ (p2 → (((p1 ∨ ((False → p4) ∨ (p4 ∨ (p2 → True)))) → (p4 → (p4 ∧ p4))) ∨ p1))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h2
  -- Implications on the right can always be decomposed.
  intro h3
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Disjunctions on the left can always be decomposed.
  cases h2
  case inl h4 =>
    -- One of the premise coincides with the conclusion.
    exact h3
  case inr h5 =>
    -- Disjunctions on the left can always be decomposed.
    cases h5
    case inl h6 =>
      -- One of the premise coincides with the conclusion.
      exact h3
    case inr h7 =>
      -- Disjunctions on the left can always be decomposed.
      cases h7
      case inl h8 =>
        -- One of the premise coincides with the conclusion.
        exact h8
      case inr h9 =>
        -- One of the premise coincides with the conclusion.
        exact h3
  -- Disjunctions on the left can always be decomposed.
  cases h2
  case inl h10 =>
    -- One of the premise coincides with the conclusion.
    exact h3
  case inr h11 =>
    -- Disjunctions on the left can always be decomposed.
    cases h11
    case inl h12 =>
      -- One of the premise coincides with the conclusion.
      exact h3
    case inr h13 =>
      -- Disjunctions on the left can always be decomposed.
      cases h13
      case inl h14 =>
        -- One of the premise coincides with the conclusion.
        exact h14
      case inr h15 =>
        -- One of the premise coincides with the conclusion.
        exact h3



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_50780957700286450229195568403 : (((p3 ∨ (((p3 ∨ p4) ∨ p5) ∨ ((((p4 ∧ (False ∧ True)) ∧ (p3 ∨ p3)) → p3) ∨ (p4 ∨ False)))) → (p4 → (False ∨ (p2 → p2)))) ∨ p3) := by
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
    -- Implications on the right can always be decomposed.
    intro h4
    -- One of the premise coincides with the conclusion.
    exact h4
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
          -- Implications on the right can always be decomposed.
          intro h9
          -- One of the premise coincides with the conclusion.
          exact h9
        case inr h10 =>
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- Implications on the right can always be decomposed.
          intro h11
          -- One of the premise coincides with the conclusion.
          exact h11
      case inr h12 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- Implications on the right can always be decomposed.
        intro h13
        -- One of the premise coincides with the conclusion.
        exact h13
    case inr h14 =>
      -- Disjunctions on the left can always be decomposed.
      cases h14
      case inl h15 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- Implications on the right can always be decomposed.
        intro h16
        -- One of the premise coincides with the conclusion.
        exact h16
      case inr h17 =>
        -- Disjunctions on the left can always be decomposed.
        cases h17
        case inl h18 =>
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- Implications on the right can always be decomposed.
          intro h19
          -- One of the premise coincides with the conclusion.
          exact h19
        case inr h20 =>
          -- False on the left can always be used.
          apply False.elim h20



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_317791565609515081869438744768 : (p4 ∨ (((True → ((p2 ∨ p3) ∧ (False ∧ ((p1 ∧ False) ∧ p2)))) ∨ ((p5 ∧ p2) ∨ ((((p3 ∧ p2) ∧ (p4 → p4)) → True) ∨ p1))) ∨ p5)) := by
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
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_178872444733354868931931773317 : (((False ∧ False) ∧ (((True → (True → (p2 → p2))) → (True → False)) ∧ p3)) ∨ (p2 ∨ ((False ∨ True) ∨ (p3 ∧ (p3 ∧ (p4 ∨ (p5 → p4))))))) := by
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
theorem thm_5_vars_194064592561989027341393487373 : ((True → (((False → (p2 ∧ p4)) ∨ (p5 ∧ p4)) ∧ False)) → ((((p4 → (((p5 → ((p2 → True) ∨ p5)) → False) ∧ p3)) ∧ p1) ∨ False) ∨ p4)) := by
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
  -- False on the left can always be used.
  apply False.elim h4



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_608924013733306651725371738530 : ((((((((False ∨ (True ∧ ((p5 ∧ (p5 → True)) → p3))) → (p3 ∨ p2)) ∨ p5) → ((p1 ∧ (p4 → (p1 → p5))) ∧ p1)) ∨ p3) ∨ p4) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_304101871646596712865430160499 : (p1 ∨ ((p1 → ((((p1 ∨ ((True ∧ p1) → ((p3 ∧ p4) → ((p4 → True) ∨ (True ∨ p5))))) → p4) ∧ (True ∨ (p5 ∨ True))) ∨ p1)) ∨ p4)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_304737017166755061920112032280 : (p1 ∨ ((((True ∧ ((p4 ∧ p3) ∧ p5)) ∨ False) ∨ ((p3 ∨ (False ∧ ((p1 → p2) → p2))) ∧ (p2 ∨ ((p5 ∧ False) → p2)))) ∨ (p5 → True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_692012965364491904191159237248 : (((((((p4 ∨ p2) ∧ ((True ∨ (p1 ∧ (True ∧ p3))) → p2)) ∨ p3) ∧ p4) ∧ ((((True → ((p3 ∧ True) ∧ p3)) ∧ True) ∨ p3) → p4)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_801072372053116118515200548138 : (((p2 → (((p2 ∨ (((False ∨ ((p1 ∧ p5) ∨ (p1 → (p2 ∨ (p3 ∨ p2))))) ∧ p4) ∨ p2)) → (p4 ∨ p1)) → ((True ∧ p5) → False))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_248786744952208858640888861200 : ((p3 ∨ p3) ∨ (False ∨ (((((True ∧ (((True ∧ (p2 → (False ∨ p1))) ∧ (p2 ∨ p4)) ∧ p3)) → p1) → p1) ∧ (True ∧ False)) ∨ (False → p2)))) := by
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
theorem thm_5_vars_65197169962302191293313415078 : ((p3 ∨ ((((((p1 → (((True ∨ p1) ∧ (False ∧ True)) ∨ p4)) ∨ p1) ∧ True) ∧ (p4 ∨ ((p1 → (False → p5)) → p2))) ∧ False) ∨ p3)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_429659156224529809357734566626 : (((((p4 ∨ ((((False ∧ (p2 ∨ (p4 ∨ p5))) ∧ p4) ∨ p4) ∨ (False → p5))) ∨ ((p3 → ((p1 ∨ p4) ∨ p4)) ∧ p3)) ∨ (p1 → p1)) ∧ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- One of the premise coincides with the conclusion.
  exact h1
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_116949948071839515183741030224 : (((p2 ∧ p2) → ((p4 → (((((p2 ∧ p5) ∨ (p3 → p3)) → (p3 ∧ (p4 → p1))) ∨ p3) ∨ ((p3 ∨ p5) → p1))) ∨ True)) ∨ (p4 → p5)) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
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
theorem thm_5_vars_622385294089062205562082017726 : ((((p3 ∧ (((p2 ∧ ((False ∨ (p2 ∨ (p1 ∧ p1))) → (p1 ∨ p1))) → (p4 → False)) ∨ ((p3 ∧ p1) → ((True → p3) ∨ p4)))) ∨ True) ∨ p4) ∧ True) := by
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
theorem thm_5_vars_652238543548693849452390614530 : ((((p2 ∧ (p1 ∨ (((False ∨ (True ∧ p3)) ∧ p5) ∧ (p3 ∧ ((p1 ∧ False) ∨ (((False → (p3 → True)) → False) → False)))))) ∧ (False → p5)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_52060892092846374843351961596 : (((p5 → ((False ∧ p3) ∧ ((((True ∧ (p2 ∨ (False ∧ False))) → True) → p1) → p5))) ∨ (((False ∧ False) ∨ ((p2 ∧ p4) → True)) → p2)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_194265481645993792682301523656 : ((p5 → ((((p4 ∨ (p3 ∧ p2)) ∨ p5) ∨ p3) → p1)) → ((((p1 ∧ False) ∨ (p5 → False)) ∨ ((p5 ∧ p2) → (True ∨ (True ∧ p4)))) ∨ p2)) := by
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
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_196717144245851233934154352844 : ((((((True ∨ False) → False) → p5) → p2) ∧ p3) ∨ (False ∨ (((p4 ∧ False) ∨ p4) ∨ (p2 → (((p2 ∧ p3) ∧ (p5 ∧ False)) → (p3 ∧ p2)))))) := by
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
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Conjunctions on the left can always be decomposed.
  let h3 := h2.left
  let h4 := h2.right
  -- Conjunctions on the left can always be decomposed.
  let h5 := h3.left
  let h6 := h3.right
  -- Conjunctions on the left can always be decomposed.
  let h7 := h4.left
  let h8 := h4.right
  -- False on the left can always be used.
  apply False.elim h8
  -- Conjunctions on the left can always be decomposed.
  let h9 := h2.left
  let h10 := h2.right
  -- Conjunctions on the left can always be decomposed.
  let h11 := h9.left
  let h12 := h9.right
  -- Conjunctions on the left can always be decomposed.
  let h13 := h10.left
  let h14 := h10.right
  -- False on the left can always be used.
  apply False.elim h14



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_715076581167207665591114810783 : ((((p3 ∨ ((p1 → (False ∧ False)) → False)) → (p2 ∨ (((((p3 → p3) → (p2 ∨ p3)) → (True ∧ p4)) ∨ (p1 → True)) ∨ (p2 ∧ p5)))) ∨ False) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h2 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h3
    -- True on the right can always be proven directly.
    apply True.intro
  case inr h4 =>
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
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_136955447206740111233766720913 : (((True ∧ p5) → (((False ∧ False) ∨ ((p1 ∧ True) ∧ (p5 ∨ ((p5 ∨ (p3 → (True → p1))) ∧ (p5 → p3))))) ∧ p3)) ∨ (True → (False → p2))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- False on the left can always be used.
  apply False.elim h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_340774546220554902226908175692 : (p2 → ((((p4 → ((p4 ∧ p5) → ((p1 ∨ False) ∨ (((p4 → p5) ∨ (False ∨ p1)) ∨ (((p1 → p3) → p2) → p2))))) ∨ p3) → p4) ∨ p2)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_603643069609946228074166183194 : ((((p4 ∨ (((((True ∨ (False → p4)) ∧ True) ∨ ((p2 ∧ p5) ∨ (False ∧ (p4 ∨ (False ∧ (p2 ∧ p2)))))) ∧ (p4 ∨ p3)) ∧ p2)) ∧ p1) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_164749661929828632806488692327 : (((((((p4 ∨ (p2 ∨ p2)) ∧ True) → (p5 ∧ (p5 ∨ p4))) → p2) → (p1 ∧ p2)) ∨ True) ∨ ((p3 ∧ p5) ∧ ((True ∨ (p2 ∧ p2)) ∨ p1))) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_52432655698587921076478930954 : ((((False ∨ p5) → (True ∧ (((p1 ∧ p2) ∨ True) ∧ (False ∨ (p4 ∨ False))))) ∧ ((p3 ∧ (p4 → ((p4 → p3) → (p4 ∨ p5)))) → False)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_721682990628944186007952996545 : ((((False ∨ ((p1 → p4) ∧ p5)) → (((False → False) ∧ p4) → (p2 → ((p2 ∨ ((((p1 ∧ p4) → p5) → (p4 ∧ False)) → False)) → False)))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_683313340487400297962994386036 : ((((p3 ∨ (((p2 ∧ p3) ∨ (True → (p3 ∧ (p5 ∧ p5)))) ∧ (((False ∨ p5) ∨ p1) → p2))) ∧ (((p4 → p3) ∨ (p2 ∧ p5)) → False)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_171449558892708157318781608831 : (((p2 ∧ (((False → p2) ∧ ((p1 → p1) → False)) ∧ (p5 → (False ∨ p1)))) ∧ p3) ∨ ((p2 ∨ ((False ∨ (True ∧ p4)) ∧ p2)) → (p2 ∨ p4))) := by
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
    -- Conjunctions on the left can always be decomposed.
    let h4 := h3.left
    let h5 := h3.right
    -- Disjunctions on the left can always be decomposed.
    cases h4
    case inl h6 =>
      -- False on the left can always be used.
      apply False.elim h6
    case inr h7 =>
      -- Conjunctions on the left can always be decomposed.
      let h8 := h7.left
      let h9 := h7.right
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- One of the premise coincides with the conclusion.
      exact h5



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_695582906545562124376296036118 : (((((True ∧ ((((p5 ∧ p5) ∧ p1) ∨ p4) → False)) → (p4 → (p2 ∨ p3))) → ((((((p1 ∨ p4) → p4) ∨ p1) ∧ p4) ∧ p1) ∧ p1)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_678539767982731526361376661215 : (((((p4 ∧ (p1 → p1)) ∨ (((p4 ∧ (((True ∧ False) → ((p4 ∧ True) → False)) → p1)) ∨ True) ∨ p5)) ∨ (p2 → ((p4 → True) ∨ p5))) ∨ p1) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
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
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_258536372077840712638245237621 : ((p5 ∨ p3) → (((((p5 ∧ (((False ∧ p4) ∧ ((p5 ∧ p3) → False)) → p3)) ∧ False) → (True ∨ (p2 ∨ p3))) → p1) ∨ ((p4 ∧ p2) ∨ True))) := by
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
theorem thm_5_vars_179032923199124963088351863989 : (((p4 ∨ p3) → ((((True → p4) ∧ p4) ∧ p2) ∨ ((p1 ∧ p2) ∧ False))) ∨ (p2 ∨ (True ∧ (False → (((p1 ∧ (p1 ∨ p1)) ∧ False) ∧ True))))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- False on the left can always be used.
  apply False.elim h1
  -- False on the left can always be used.
  apply False.elim h1
  -- False on the left can always be used.
  apply False.elim h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_350942700879827924267603339626 : (p4 → ((((((False ∨ p1) ∧ p4) ∨ (p2 ∨ (p4 → ((p3 → (p5 → ((p3 ∧ p4) ∨ p3))) ∨ p1)))) ∨ True) → (p5 ∨ False)) ∨ (False → True))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h2
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_876616549202332491409280364374 : ((((((p2 → True) ∨ (p3 ∧ (((True → p1) ∨ ((True ∧ ((False ∧ p2) ∧ p1)) ∨ p4)) ∧ p4))) → (True ∧ (p2 ∧ False))) ∧ (p2 → p2)) → p1) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
  have h4 : ((p2 → True) ∨ (p3 ∧ (((True → p1) ∨ ((True ∧ ((False ∧ p2) ∧ p1)) ∨ p4)) ∧ p4))) := by
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Implications on the right can always be decomposed.
    intro h5
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h2, we can now drive its conclusion.
  let h6 := h2 h4
  -- We need to get the right conjuct of h6 based on <expert-advice>.
  let h7 := h6.right
  -- We need to get the right conjuct of h7 based on <expert-advice>.
  let h8 := h7.right
  -- False on the left can always be used.
  apply False.elim h8
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_105124103198166274721466494975 : ((((((((p3 ∧ p1) → p2) → (p5 ∧ ((False → p5) ∧ p1))) ∨ False) ∨ p4) ∨ (p2 ∨ (p4 → p4))) ∨ (p5 ∨ (True ∧ p3))) ∧ (True ∨ True)) := by
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
  -- One of the premise coincides with the conclusion.
  exact h1
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_217866419778303890145831100064 : (((False → (False ∨ p3)) → False) → (((p2 → (True ∧ (p3 → ((p2 ∧ p3) → True)))) → (p5 ∨ (((p3 → p5) ∨ (False ∧ False)) ∧ p2))) ∨ p4)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h2 : (False → (False ∨ p3)) := by
    -- Implications on the right can always be decomposed.
    intro h3
    -- False on the left can always be used.
    apply False.elim h3
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h4 := h1 h2
  -- False on the left can always be used.
  apply False.elim h4



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_229002570367603095348351615418 : ((p5 ∨ (p2 ∧ True)) ∨ ((p1 ∨ ((((True → p4) ∧ (p4 → ((False ∧ (p3 → False)) ∨ p5))) ∧ ((p3 ∨ (p1 ∧ p1)) → p2)) → p5)) ∨ p1)) := by
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
  -- Conjunctions on the left can always be decomposed.
  let h4 := h2.left
  let h5 := h2.right
  -- We want to use the implication h5 based on <expert-advice>. So we show its premise.
  have h6 : p4 := by
    -- We want to use the implication h4 based on <expert-advice>. So we show its premise.
    have h7 : True := by
      -- True on the right can always be proven directly.
      apply True.intro
    -- We have shown the premise of h4, we can now drive its conclusion.
    let h8 := h4 h7
    -- One of the premise coincides with the conclusion.
    exact h8
  -- We have shown the premise of h5, we can now drive its conclusion.
  let h9 := h5 h6
  -- Disjunctions on the left can always be decomposed.
  cases h9
  case inl h10 =>
    -- Conjunctions on the left can always be decomposed.
    let h11 := h10.left
    let h12 := h10.right
    -- False on the left can always be used.
    apply False.elim h11
  case inr h13 =>
    -- One of the premise coincides with the conclusion.
    exact h13



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_41013779117649247756266617228 : (((((((False ∨ True) ∨ ((p2 → p4) ∧ True)) → ((True ∨ (True → ((False ∨ False) ∧ p1))) ∨ (p4 → True))) ∨ p5) → (False ∧ p5)) ∨ True) ∨ p2) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_64487875713184495948141113119 : ((p1 ∨ ((True ∧ ((((((p5 → p3) ∧ True) → (True ∨ False)) → (p4 ∧ p1)) ∨ False) ∧ (p5 ∨ p3))) → (True → (True → (p1 ∧ True))))) ∨ p1) := by
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
  -- Conjunctions on the left can always be decomposed.
  let h4 := h1.left
  let h5 := h1.right
  -- Conjunctions on the left can always be decomposed.
  let h6 := h5.left
  let h7 := h5.right
  -- Disjunctions on the left can always be decomposed.
  cases h6
  case inl h8 =>
    -- Disjunctions on the left can always be decomposed.
    cases h7
    case inl h9 =>
      -- We want to use the implication h8 based on <expert-advice>. So we show its premise.
      have h10 : (((p5 → p3) ∧ True) → (True ∨ False)) := by
        -- Implications on the right can always be decomposed.
        intro h11
        -- Conjunctions on the left can always be decomposed.
        let h12 := h11.left
        let h13 := h11.right
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- True on the right can always be proven directly.
        apply True.intro
      -- We have shown the premise of h8, we can now drive its conclusion.
      let h14 := h8 h10
      -- We need to get the right conjuct of h14 based on <expert-advice>.
      let h15 := h14.right
      -- One of the premise coincides with the conclusion.
      exact h15
    case inr h16 =>
      -- We want to use the implication h8 based on <expert-advice>. So we show its premise.
      have h17 : (((p5 → p3) ∧ True) → (True ∨ False)) := by
        -- Implications on the right can always be decomposed.
        intro h18
        -- Conjunctions on the left can always be decomposed.
        let h19 := h18.left
        let h20 := h18.right
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- True on the right can always be proven directly.
        apply True.intro
      -- We have shown the premise of h8, we can now drive its conclusion.
      let h21 := h8 h17
      -- We need to get the right conjuct of h21 based on <expert-advice>.
      let h22 := h21.right
      -- One of the premise coincides with the conclusion.
      exact h22
  case inr h23 =>
    -- False on the left can always be used.
    apply False.elim h23
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_168333772023682525677350596585 : (((p5 → p3) ∧ (p5 ∨ (((p2 ∧ (False ∨ p2)) ∨ (((p2 ∨ p5) ∨ True) → p1)) → p3))) → ((p3 ∨ p4) → ((False ∨ p3) ∨ (False → p5)))) := by
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
    -- Disjunctions on the left can always be decomposed.
    cases h5
    case inl h6 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Implications on the right can always be decomposed.
      intro h7
      -- False on the left can always be used.
      apply False.elim h7
    case inr h8 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Implications on the right can always be decomposed.
      intro h9
      -- False on the left can always be used.
      apply False.elim h9
  case inr h10 =>
    -- Conjunctions on the left can always be decomposed.
    let h11 := h1.left
    let h12 := h1.right
    -- Disjunctions on the left can always be decomposed.
    cases h12
    case inl h13 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Implications on the right can always be decomposed.
      intro h14
      -- False on the left can always be used.
      apply False.elim h14
    case inr h15 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Implications on the right can always be decomposed.
      intro h16
      -- False on the left can always be used.
      apply False.elim h16



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_116374544610434179139403121403 : ((((p4 ∨ p1) → False) → (((p4 → (True → (((p2 → (False ∨ p2)) → (True ∨ p5)) → p1))) ∨ p2) ∧ (p2 → (p4 → False)))) ∨ (False ∧ p5)) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h2
  -- Implications on the right can always be decomposed.
  intro h3
  -- Implications on the right can always be decomposed.
  intro h4
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h5 : (p4 ∨ p1) := by
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- One of the premise coincides with the conclusion.
    exact h2
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h6 := h1 h5
  -- False on the left can always be used.
  apply False.elim h6
  -- Implications on the right can always be decomposed.
  intro h7
  -- Implications on the right can always be decomposed.
  intro h8
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h9 : (p4 ∨ p1) := by
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- One of the premise coincides with the conclusion.
    exact h8
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h10 := h1 h9
  -- False on the left can always be used.
  apply False.elim h10



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_311023031583784916488265031625 : (p2 ∨ ((False ∧ p3) ∨ ((p4 ∧ False) ∨ ((p1 ∧ p3) → (((((p4 → (((p2 → p4) ∧ p3) → (p2 ∧ p2))) ∨ p5) → p5) ∨ p1) ∨ p3))))) := by
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
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h3



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_228900882040017348386556292227 : ((p4 ∨ (p4 ∧ p5)) ∨ ((p2 → (p4 ∨ (False ∨ p4))) ∨ (((p5 → (False → (p2 ∨ p2))) → (False ∧ ((p2 ∨ (p5 → p2)) ∧ p5))) ∨ True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_710371101751791610226249467419 : ((((((True → (True ∧ p4)) ∨ p2) → p3) ∧ ((p4 ∨ ((((p1 ∧ False) → (p1 ∨ ((True ∧ p2) → p4))) ∧ p5) → (p3 ∨ p2))) ∨ True)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_199612587548822479209987496282 : ((((True → (p4 ∧ (p4 ∨ p3))) → False) → p4) → (((p5 ∧ ((p5 ∧ p4) ∧ p2)) ∧ ((True ∧ (p3 ∨ (p1 ∧ p5))) ∧ True)) → (p4 ∨ True))) := by
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
  -- Conjunctions on the left can always be decomposed.
  let h7 := h6.left
  let h8 := h6.right
  -- Conjunctions on the left can always be decomposed.
  let h9 := h7.left
  let h10 := h7.right
  -- Conjunctions on the left can always be decomposed.
  let h11 := h4.left
  let h12 := h4.right
  -- Conjunctions on the left can always be decomposed.
  let h13 := h11.left
  let h14 := h11.right
  -- Disjunctions on the left can always be decomposed.
  cases h14
  case inl h15 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro
  case inr h16 =>
    -- Conjunctions on the left can always be decomposed.
    let h17 := h16.left
    let h18 := h16.right
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_206011721605495763743795637913 : ((p2 ∧ ((p4 ∧ (p5 ∨ p4)) ∧ p1)) ∨ (p3 → (p4 → ((p5 ∧ (((p4 → True) → p2) ∨ (((False → p1) ∧ p5) ∨ (p2 ∨ p1)))) → p4)))) := by
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
      exact h2
    case inr h11 =>
      -- Disjunctions on the left can always be decomposed.
      cases h11
      case inl h12 =>
        -- One of the premise coincides with the conclusion.
        exact h2
      case inr h13 =>
        -- One of the premise coincides with the conclusion.
        exact h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_137828176081932261874963433890 : ((p3 ∨ (((p4 → p3) ∨ ((p1 ∧ ((p1 ∧ False) → (p5 ∧ ((p5 → p1) → (p4 ∧ True))))) → False)) ∧ (True ∨ p2))) ∨ ((p1 ∧ p1) → p1)) := by
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
theorem thm_5_vars_158521410176613193516194034564 : (((p4 ∨ True) → (((p1 → ((p2 ∨ (p3 ∨ False)) ∨ p2)) → ((True ∨ (True → p1)) ∧ p5)) → p5)) ∨ (False → (((p1 → p2) ∨ False) ∧ False))) := by
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
theorem thm_5_vars_55261392237879270196117958191 : ((((p3 → p2) ∨ (p5 → (p4 ∧ False))) ∨ ((((p3 ∨ True) → (p1 → (p3 ∨ ((False ∧ p4) → p2)))) → p1) ∨ (p1 → (p4 ∨ True)))) ∨ p2) := by
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
theorem thm_5_vars_307288879117938811239407086642 : (p1 ∨ (p2 ∨ (p5 ∨ ((p1 → (False ∧ p4)) ∨ ((p1 ∨ ((p1 → p4) ∨ (((p2 ∧ p4) → p3) → (p4 ∨ (False → (p4 → p5)))))) ∨ p4))))) := by
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
  -- Implications on the right can always be decomposed.
  intro h3
  -- False on the left can always be used.
  apply False.elim h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_190268378398911807998373241716 : ((((((p4 ∧ False) ∧ p4) ∨ (p4 ∨ p3)) ∨ True) ∨ p4) ∨ ((((p4 ∧ p1) ∧ ((p3 ∨ p4) → ((p2 ∨ p3) ∨ p5))) ∧ (True → p3)) ∧ p4)) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_47108005948311034437492638696 : ((((True → ((p2 ∨ p5) ∧ ((p3 → False) ∨ (((p1 → True) ∨ ((True ∧ p3) → p4)) ∨ False)))) ∧ ((p4 → True) → p3)) ∨ (True ∨ True)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_2491708037700889395148056715 : (((p2 ∧ (p1 ∨ (True ∧ p1))) → ((p5 ∧ p2) → p2)) → (p5 → (((True ∧ ((p2 → (p5 → False)) ∧ (p1 ∧ p3))) ∨ p2) ∨ p5))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_565875020598860767990394741045 : (((True → ((p5 ∧ (p2 ∨ (p5 ∨ ((p1 ∨ ((p3 → p5) ∨ False)) ∨ (p4 ∧ p1))))) → (((p4 → p2) ∨ (p5 ∨ p2)) ∨ (p5 ∨ p5)))) ∧ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
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
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- One of the premise coincides with the conclusion.
    exact h3
  case inr h6 =>
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
      -- Disjunctions on the left can always be decomposed.
      cases h8
      case inl h9 =>
        -- Disjunctions on the left can always be decomposed.
        cases h9
        case inl h10 =>
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- Show the left disjunct based on <expert-advice>.
          apply Or.inl
          -- One of the premise coincides with the conclusion.
          exact h3
        case inr h11 =>
          -- Disjunctions on the left can always be decomposed.
          cases h11
          case inl h12 =>
            -- Show the right disjunct based on <expert-advice>.
            apply Or.inr
            -- Show the left disjunct based on <expert-advice>.
            apply Or.inl
            -- One of the premise coincides with the conclusion.
            exact h3
          case inr h13 =>
            -- False on the left can always be used.
            apply False.elim h13
      case inr h14 =>
        -- Conjunctions on the left can always be decomposed.
        let h15 := h14.left
        let h16 := h14.right
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- One of the premise coincides with the conclusion.
        exact h3
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_328916822513314781552929092355 : (True → ((((False ∧ (p2 ∨ p3)) ∧ False) ∨ (True ∨ p4)) → ((True → (p3 ∨ (True → ((((p3 ∧ p5) → p3) ∧ p3) ∨ (True ∧ p2))))) ∨ True))) := by
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
    -- Conjunctions on the left can always be decomposed.
    let h6 := h4.left
    let h7 := h4.right
    -- False on the left can always be used.
    apply False.elim h6
  case inr h8 =>
    -- Disjunctions on the left can always be decomposed.
    cases h8
    case inl h9 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- True on the right can always be proven directly.
      apply True.intro
    case inr h10 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- True on the right can always be proven directly.
      apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_118846064612185895715675233641 : ((True → ((((((p1 → p5) ∨ p5) → ((p4 ∨ True) ∧ p1)) ∧ p1) ∨ (p5 ∨ (False → True))) ∨ (p5 ∧ ((p2 ∧ p2) ∧ p1)))) ∨ (p2 ∨ p1)) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h2
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_64007545947810223130928070039 : ((False ∨ ((p3 ∧ (False ∧ (p1 ∧ ((p1 ∨ ((p2 ∨ True) ∧ ((((p4 ∧ False) ∨ p5) ∧ p2) ∧ p4))) ∧ (p1 ∨ p2))))) ∧ (False → p2))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_596480535723383281539561755098 : (((((((p3 → p3) ∨ (p2 ∧ (p5 ∨ p3))) ∨ False) → ((p3 ∧ p3) ∧ ((p1 ∧ p5) → (((p1 → p5) ∧ p5) ∨ (False ∨ p3))))) ∧ True) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_117503020743673834886319202876 : ((p2 ∧ (((((p5 ∨ p4) ∨ ((False ∨ p3) ∧ p1)) ∨ (p1 → p4)) → ((False ∧ ((p3 ∧ (p5 → p1)) ∨ False)) ∧ True)) ∧ p1)) ∨ (p4 → p4)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_48042205970928051576439537547 : ((((p5 ∨ (True ∨ ((p3 → (p4 → (True → p5))) ∨ p2))) ∨ ((True ∨ (False ∨ (p2 ∨ (p5 ∧ (p2 → False))))) ∧ p4)) → (p4 ∧ p1)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_161729510022309366868782352159 : ((p3 ∨ (((((False → p3) ∧ (p2 ∨ p3)) → True) ∨ p5) ∧ (p1 ∧ (((p1 ∨ p3) → False) ∨ False)))) → (p4 ∨ (p3 ∨ ((p1 ∨ False) → p4)))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h2 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- One of the premise coincides with the conclusion.
    exact h2
  case inr h3 =>
    -- Conjunctions on the left can always be decomposed.
    let h4 := h3.left
    let h5 := h3.right
    -- Disjunctions on the left can always be decomposed.
    cases h4
    case inl h6 =>
      -- Conjunctions on the left can always be decomposed.
      let h7 := h5.left
      let h8 := h5.right
      -- Disjunctions on the left can always be decomposed.
      cases h8
      case inl h9 =>
        -- We want to use the implication h9 based on <expert-advice>. So we show its premise.
        have h10 : (p1 ∨ p3) := by
          -- Show the left disjunct based on <expert-advice>.
          apply Or.inl
          -- One of the premise coincides with the conclusion.
          exact h7
        -- We have shown the premise of h9, we can now drive its conclusion.
        let h11 := h9 h10
        -- False on the left can always be used.
        apply False.elim h11
      case inr h12 =>
        -- False on the left can always be used.
        apply False.elim h12
    case inr h13 =>
      -- Conjunctions on the left can always be decomposed.
      let h14 := h5.left
      let h15 := h5.right
      -- Disjunctions on the left can always be decomposed.
      cases h15
      case inl h16 =>
        -- We want to use the implication h16 based on <expert-advice>. So we show its premise.
        have h17 : (p1 ∨ p3) := by
          -- Show the left disjunct based on <expert-advice>.
          apply Or.inl
          -- One of the premise coincides with the conclusion.
          exact h14
        -- We have shown the premise of h16, we can now drive its conclusion.
        let h18 := h16 h17
        -- False on the left can always be used.
        apply False.elim h18
      case inr h19 =>
        -- False on the left can always be used.
        apply False.elim h19



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_46806800853691298814788548924 : (((((p3 → ((p4 → (True ∧ ((p1 ∨ False) → ((p5 ∨ p5) → p2)))) → ((p2 ∨ (p5 → p3)) → False))) ∧ p5) ∧ True) ∨ (p2 ∧ True)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_337037883830949710216763442700 : (p1 → (((((((p2 → True) ∨ p3) → (p5 ∨ p5)) ∨ (((False → (p4 → True)) ∨ False) → p1)) ∧ (True ∨ (p1 ∧ p2))) ∧ True) ∨ (p2 ∨ p2))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
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
    -- False on the left can always be used.
    apply False.elim h4
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_150288128501584330959878405467 : ((p4 → ((((((p1 ∧ ((p2 ∨ ((p5 ∨ p4) → False)) ∧ p2)) ∧ p3) ∧ (p1 → p1)) → p4) ∧ p4) → False)) ∨ ((p3 → p2) → (p1 ∨ True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_172062075272632561581101471939 : (((((((p2 ∧ (p5 ∨ (True → p4))) ∧ True) ∨ False) ∨ p5) → p4) → (p1 ∧ p5)) ∨ (False → (p3 ∧ (((p4 ∨ p1) ∧ p4) ∧ (False → p3))))) := by
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
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- False on the left can always be used.
  apply False.elim h1
  -- False on the left can always be used.
  apply False.elim h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- False on the left can always be used.
  apply False.elim h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_164441653165167570327038366198 : ((((((p5 → (p1 ∧ (p2 ∨ False))) ∧ ((p5 → p3) ∧ (p3 → p3))) ∧ False) ∧ p5) ∧ p2) ∨ ((p4 ∨ ((p3 ∧ p1) ∧ p3)) ∨ (False → False))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_119253993488280018433375693591 : ((p2 → (p3 ∨ (((False ∧ p3) → (p2 ∧ True)) ∧ ((p5 ∨ ((p3 ∨ (p5 ∧ (((p4 ∧ p5) → p3) → False))) → False)) → p3)))) ∨ (p4 → p4)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_210209573338215074866482504026 : ((((p5 → True) ∨ False) ∨ p4) ∧ ((p1 ∨ ((((((((p5 ∨ ((p2 ∧ True) ∨ False)) ∨ p2) ∧ False) ∧ p3) ∧ p5) ∧ p1) ∨ p4) ∨ True)) ∧ True)) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro
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
theorem thm_5_vars_51961946655758698735292437661 : ((((p4 ∧ ((p2 ∧ p1) → p2)) → (p1 ∨ (p5 → ((p5 → (p5 ∨ p4)) → p3)))) ∨ (((True ∧ p1) ∧ (p2 ∧ (p1 → p1))) ∨ True)) ∨ p3) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_137634558021613952974864452508 : ((False ∨ (((True ∧ False) ∧ (p3 ∨ (((True → p3) ∨ ((p2 ∧ p4) ∧ (False ∨ p1))) ∨ p1))) ∧ (p5 ∧ (False ∧ p1)))) ∨ ((p4 ∧ p3) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_42605905457723841935533796076 : (((p3 ∨ ((((p3 ∨ (True → p3)) ∨ False) ∨ (False ∧ ((p4 ∧ p1) → ((((True ∧ (p5 ∨ p2)) ∧ p1) → p3) ∨ p1)))) ∧ p5)) ∨ p1) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_49944778597379320895475373117 : (((((p1 ∧ (p1 ∨ ((((p4 ∧ p3) → (True ∨ (p2 ∧ True))) ∨ True) ∨ p2))) ∧ p3) ∨ (p2 ∨ p4)) ∧ (((p4 → False) → p1) ∧ p4)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_52650884159554192581562848026 : (((False ∧ (((p2 ∧ p4) ∧ (True → True)) ∨ (True ∧ (p1 → (p4 → p5))))) ∨ ((p3 ∨ ((p3 → False) ∨ (p5 ∧ (True ∧ p5)))) ∨ p3)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_679358793906883867083375690594 : ((((p3 → (((True ∨ p5) ∧ False) ∨ ((p2 → (False ∧ (False ∨ (p3 ∨ p1)))) → ((p1 ∨ True) → p5)))) ∨ ((p1 ∧ p1) → (True ∨ p3))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_199022837130811190372548574629 : ((((True ∨ (p2 ∧ (p1 ∨ p2))) ∧ p5) ∧ p2) → (((((p3 ∧ ((p4 ∧ True) ∧ False)) ∧ (False ∧ True)) ∧ p4) ∨ (True ∨ (p2 ∧ p2))) ∨ True)) := by
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
      -- True on the right can always be proven directly.
      apply True.intro
    case inr h11 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- True on the right can always be proven directly.
      apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_47402935964934920828187432236 : (((True ∧ (True ∧ ((p3 ∧ p4) ∧ (((p2 → p5) ∨ (((p2 ∨ p1) ∧ (False → p5)) ∧ ((p4 ∨ p5) ∧ p4))) ∨ p5)))) ∨ (True ∨ False)) ∨ p1) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_304005013853947274525579655313 : (p1 ∨ (((p1 ∨ False) → ((p3 ∨ True) → (((p1 ∧ (((p2 ∨ (p2 ∨ p1)) ∨ True) ∨ (False ∧ (p5 ∧ (True ∨ p3))))) ∨ p1) ∧ p1))) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_57083551064942237927791715666 : ((((p1 ∧ p2) ∧ p2) ∨ ((((p5 ∧ p5) ∧ ((p1 ∧ (False ∧ p3)) → ((p3 ∨ ((p4 ∧ p2) ∧ True)) ∧ (False ∧ p5)))) ∨ p1) ∧ p3)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_319202784858129485409887801108 : (p4 ∨ (((p1 ∨ (p4 ∧ (((p5 ∧ p3) ∧ p4) → (((p5 → p4) ∨ p5) → False)))) ∧ (p5 → p3)) → (((p2 ∧ p5) ∧ (p1 ∧ p1)) ∨ True))) := by
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
    -- True on the right can always be proven directly.
    apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_112248569119895109424161844660 : (((p3 ∨ (p4 ∨ (((((p3 → (p1 ∨ True)) → ((False ∨ True) ∨ p3)) → p1) ∧ ((True ∨ p3) → p3)) → (p4 ∨ p1)))) ∨ p1) ∨ (p5 ∧ True)) := by
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
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
  have h4 : ((p3 → (p1 ∨ True)) → ((False ∨ True) ∨ p3)) := by
    -- Implications on the right can always be decomposed.
    intro h5
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h2, we can now drive its conclusion.
  let h6 := h2 h4
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h6



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_136635634248265955723219656298 : ((((p1 → True) ∨ False) → ((p1 ∧ True) → (p3 ∨ (((p5 ∧ p5) → p4) → ((p3 ∨ ((True ∨ p4) ∧ p5)) ∨ False))))) ∨ (True ∨ (True ∧ p3))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_766861578490472614416311904370 : (((p4 ∧ (p4 ∨ (p3 → (((((((p2 ∧ p3) → True) ∨ (p3 ∧ (p1 ∨ ((p5 ∧ False) → p5)))) ∨ True) ∧ p5) → (p2 ∧ p3)) → p4)))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_168563691455635580157117019554 : ((p1 ∧ (p1 → ((p3 ∨ (False → (p4 ∨ (p5 → (p3 ∧ False))))) → (p2 ∧ (False ∧ p5))))) → (p3 ∧ (((p5 ∨ (p4 ∨ p3)) ∨ p5) → p3))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- We want to use the implication h3 based on <expert-advice>. So we show its premise.
  have h4 : p1 := by
    -- One of the premise coincides with the conclusion.
    exact h2
  -- We have shown the premise of h3, we can now drive its conclusion.
  let h5 := h3 h4
  -- We want to use the implication h5 based on <expert-advice>. So we show its premise.
  have h6 : (p3 ∨ (False → (p4 ∨ (p5 → (p3 ∧ False))))) := by
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h7
    -- False on the left can always be used.
    apply False.elim h7
  -- We have shown the premise of h5, we can now drive its conclusion.
  let h8 := h5 h6
  -- We need to get the right conjuct of h8 based on <expert-advice>.
  let h9 := h8.right
  -- We need to get the left conjuct of h9 based on <expert-advice>.
  let h10 := h9.left
  -- False on the left can always be used.
  apply False.elim h10
  -- Implications on the right can always be decomposed.
  intro h11
  -- Disjunctions on the left can always be decomposed.
  cases h11
  case inl h12 =>
    -- Disjunctions on the left can always be decomposed.
    cases h12
    case inl h13 =>
      -- Conjunctions on the left can always be decomposed.
      let h14 := h1.left
      let h15 := h1.right
      -- We want to use the implication h15 based on <expert-advice>. So we show its premise.
      have h16 : p1 := by
        -- One of the premise coincides with the conclusion.
        exact h14
      -- We have shown the premise of h15, we can now drive its conclusion.
      let h17 := h15 h16
      -- We want to use the implication h17 based on <expert-advice>. So we show its premise.
      have h18 : (p3 ∨ (False → (p4 ∨ (p5 → (p3 ∧ False))))) := by
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- Implications on the right can always be decomposed.
        intro h19
        -- False on the left can always be used.
        apply False.elim h19
      -- We have shown the premise of h17, we can now drive its conclusion.
      let h20 := h17 h18
      -- We need to get the right conjuct of h20 based on <expert-advice>.
      let h21 := h20.right
      -- We need to get the left conjuct of h21 based on <expert-advice>.
      let h22 := h21.left
      -- False on the left can always be used.
      apply False.elim h22
    case inr h23 =>
      -- Disjunctions on the left can always be decomposed.
      cases h23
      case inl h24 =>
        -- Conjunctions on the left can always be decomposed.
        let h25 := h1.left
        let h26 := h1.right
        -- We want to use the implication h26 based on <expert-advice>. So we show its premise.
        have h27 : p1 := by
          -- One of the premise coincides with the conclusion.
          exact h25
        -- We have shown the premise of h26, we can now drive its conclusion.
        let h28 := h26 h27
        -- We want to use the implication h28 based on <expert-advice>. So we show its premise.
        have h29 : (p3 ∨ (False → (p4 ∨ (p5 → (p3 ∧ False))))) := by
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- Implications on the right can always be decomposed.
          intro h30
          -- False on the left can always be used.
          apply False.elim h30
        -- We have shown the premise of h28, we can now drive its conclusion.
        let h31 := h28 h29
        -- We need to get the right conjuct of h31 based on <expert-advice>.
        let h32 := h31.right
        -- We need to get the left conjuct of h32 based on <expert-advice>.
        let h33 := h32.left
        -- False on the left can always be used.
        apply False.elim h33
      case inr h34 =>
        -- Conjunctions on the left can always be decomposed.
        let h35 := h1.left
        let h36 := h1.right
        -- One of the premise coincides with the conclusion.
        exact h34
  case inr h37 =>
    -- Conjunctions on the left can always be decomposed.
    let h38 := h1.left
    let h39 := h1.right
    -- We want to use the implication h39 based on <expert-advice>. So we show its premise.
    have h40 : p1 := by
      -- One of the premise coincides with the conclusion.
      exact h38
    -- We have shown the premise of h39, we can now drive its conclusion.
    let h41 := h39 h40
    -- We want to use the implication h41 based on <expert-advice>. So we show its premise.
    have h42 : (p3 ∨ (False → (p4 ∨ (p5 → (p3 ∧ False))))) := by
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Implications on the right can always be decomposed.
      intro h43
      -- False on the left can always be used.
      apply False.elim h43
    -- We have shown the premise of h41, we can now drive its conclusion.
    let h44 := h41 h42
    -- We need to get the right conjuct of h44 based on <expert-advice>.
    let h45 := h44.right
    -- We need to get the left conjuct of h45 based on <expert-advice>.
    let h46 := h45.left
    -- False on the left can always be used.
    apply False.elim h46



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_670183736344368080980357428118 : ((((((p5 ∨ (p5 → False)) ∨ True) ∧ ((p3 ∧ ((True → (((p2 → p3) ∨ p3) ∨ p2)) ∧ (p1 ∧ p2))) ∨ p3)) ∨ (p5 → (p2 → p2))) ∨ False) ∧ True) := by
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
  -- One of the premise coincides with the conclusion.
  exact h2
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_64450842410840616518886899808 : ((p1 ∨ (((p3 ∨ (((False → p3) ∨ True) ∨ (((p4 ∨ p1) ∨ (p4 ∨ p5)) → False))) ∨ (False ∧ ((True ∨ p4) ∨ p2))) → (p4 → p3))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_807843020080077242666945837556 : (((p4 → ((p2 → True) ∧ ((((True → (False → p1)) ∨ (p4 ∧ (True ∨ ((((p1 ∨ p2) → p1) ∧ True) → p3)))) → (p1 ∨ p1)) → p2))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_41733447716782300752183254003 : (((((p2 → p1) → (p1 ∧ p2)) ∧ ((p2 ∧ ((p1 ∨ (True ∨ p2)) ∧ (False ∨ (p1 → (p2 ∧ (p1 ∨ (False → p5))))))) → p4)) ∨ True) ∨ p1) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_164696934289984528282430685974 : ((((((False ∨ (p1 → ((True ∨ False) ∨ (p5 ∧ p4)))) → False) ∧ (p5 ∨ p5)) ∨ True) ∨ p1) ∨ (p2 → ((False ∧ p3) → (False ∨ (p1 ∨ False))))) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_259627156169485164468741324761 : ((p1 → False) → ((((((False ∧ True) → (True → p4)) ∧ (((p3 → p5) ∨ p4) ∨ ((False → (p1 → p2)) ∧ p3))) ∨ p5) → p4) → (p5 ∨ True))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_112842657380178472627925816600 : (((((p4 ∨ p3) ∧ p1) ∧ ((False → p2) → ((((False ∨ p5) → (p1 ∧ (True ∨ (p1 ∧ (p2 ∧ p5))))) ∨ False) ∨ p4))) → False) ∨ (True ∨ p2)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_804026010921095024328780174087 : (((p3 → ((p2 ∨ ((((True ∧ p2) ∧ (p5 ∨ p2)) ∨ (False ∨ p3)) → ((p2 ∨ (p3 ∧ p1)) → (p1 ∧ False)))) ∨ ((p2 ∧ False) → False))) ∨ p2) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h2
  -- Conjunctions on the left can always be decomposed.
  let h3 := h2.left
  let h4 := h2.right
  -- False on the left can always be used.
  apply False.elim h4
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_44761446171712817464033263386 : (((((p5 → (p5 ∨ p4)) ∨ p5) → (((True → (p3 ∨ (p5 ∨ p1))) ∨ p5) ∧ ((p1 → (p2 ∧ (p1 → False))) ∧ (False ∧ p2)))) → p4) ∨ False) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h2 : ((p5 → (p5 ∨ p4)) ∨ p5) := by
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Implications on the right can always be decomposed.
    intro h3
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- One of the premise coincides with the conclusion.
    exact h3
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h4 := h1 h2
  -- We need to get the right conjuct of h4 based on <expert-advice>.
  let h5 := h4.right
  -- We need to get the right conjuct of h5 based on <expert-advice>.
  let h6 := h5.right
  -- We need to get the left conjuct of h6 based on <expert-advice>.
  let h7 := h6.left
  -- False on the left can always be used.
  apply False.elim h7



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_162883876951556716728051110335 : (((p1 ∧ (p1 → (p4 ∨ (((p4 ∧ p2) ∧ (p3 ∧ (p4 ∧ p2))) ∧ p1)))) ∨ (p1 → True)) ∧ ((False ∧ False) → ((p2 ∨ (p3 ∨ p3)) ∧ True))) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro
  -- Implications on the right can always be decomposed.
  intro h2
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Conjunctions on the left can always be decomposed.
  let h3 := h2.left
  let h4 := h2.right
  -- False on the left can always be used.
  apply False.elim h3
  -- True on the right can always be proven directly.
  apply True.intro



