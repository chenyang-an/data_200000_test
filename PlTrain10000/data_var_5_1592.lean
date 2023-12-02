variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_736647197985834651789244469743 : ((((p1 → p5) ∧ (p2 → (p2 ∧ (True ∧ (((True ∨ ((p4 ∨ False) ∨ (p2 → p1))) → (p1 ∨ ((False → p2) ∧ p1))) ∨ (p1 ∧ False)))))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_648652782160142870669505184952 : (((((((p1 ∧ False) ∨ p5) → (p5 → ((True → ((True → ((p4 → True) ∧ (p2 ∧ (False ∨ p4)))) ∨ p3)) ∨ p2))) ∨ True) ∧ (p1 ∧ p4)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_701215951066580310553826419961 : (((((p1 → (p5 → ((p2 ∨ p3) ∧ p2))) ∧ (True ∧ p1)) ∧ (((p1 ∨ p2) → ((True ∧ True) → (p2 ∨ ((p1 ∨ p1) ∨ p1)))) ∨ True)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_192694954590641906473246495168 : ((((True → ((p1 ∨ p3) ∨ p1)) ∨ (p2 ∧ p3)) → False) → (p1 → (p4 ∧ (False ∧ (((p3 ∧ (((p5 ∧ p2) ∧ p4) → p2)) ∨ p3) ∨ p2))))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h3 : ((True → ((p1 ∨ p3) ∨ p1)) ∨ (p2 ∧ p3)) := by
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Implications on the right can always be decomposed.
    intro h4
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h2
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h5 := h1 h3
  -- False on the left can always be used.
  apply False.elim h5
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h6 : ((True → ((p1 ∨ p3) ∨ p1)) ∨ (p2 ∧ p3)) := by
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Implications on the right can always be decomposed.
    intro h7
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h2
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h8 := h1 h6
  -- False on the left can always be used.
  apply False.elim h8
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h9 : ((True → ((p1 ∨ p3) ∨ p1)) ∨ (p2 ∧ p3)) := by
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Implications on the right can always be decomposed.
    intro h10
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h2
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h11 := h1 h9
  -- False on the left can always be used.
  apply False.elim h11



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_623807784308350969891277777980 : ((((p1 ∨ (((p4 ∨ False) ∧ p5) ∨ (((p5 ∧ ((p5 → (p2 → (p3 ∧ True))) ∨ p3)) → p4) → (p4 ∨ (False → (False → True)))))) ∨ False) ∨ p1) ∧ True) := by
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
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h2
  -- Implications on the right can always be decomposed.
  intro h3
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_214679123231120639595004463986 : (((p5 → False) ∧ (p2 ∨ p3)) ∨ ((p3 ∨ (p5 ∨ True)) ∨ (p4 ∨ (False ∧ (p4 ∧ ((True → (((p1 ∧ (p3 → False)) ∨ p5) ∨ p5)) → p1)))))) := by
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
theorem thm_5_vars_193138835563434974767652812324 : ((((False → p5) ∨ (False ∧ p5)) ∨ ((p1 ∨ p4) ∨ False)) → (p1 → ((((False ∧ ((p2 ∨ (True ∧ (p4 → p4))) → False)) ∧ p5) ∨ True) ∨ p1))) := by
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
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- One of the premise coincides with the conclusion.
      exact h2
    case inr h5 =>
      -- Conjunctions on the left can always be decomposed.
      let h6 := h5.left
      let h7 := h5.right
      -- False on the left can always be used.
      apply False.elim h6
  case inr h8 =>
    -- Disjunctions on the left can always be decomposed.
    cases h8
    case inl h9 =>
      -- Disjunctions on the left can always be decomposed.
      cases h9
      case inl h10 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- One of the premise coincides with the conclusion.
        exact h10
      case inr h11 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- One of the premise coincides with the conclusion.
        exact h2
    case inr h12 =>
      -- False on the left can always be used.
      apply False.elim h12



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_308625813131343252971948048434 : (p2 ∨ (((p3 ∧ p5) → (True ∧ (((((p1 → p3) ∧ p1) ∧ (((p2 ∧ p1) ∨ p4) → (p3 ∧ p3))) → (p4 ∧ p2)) ∨ (True ∧ p3)))) ∨ p4)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- One of the premise coincides with the conclusion.
  exact h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_907975656560444500027514482576 : ((((p4 ∨ (((p5 ∨ (p3 ∧ ((((True → (False ∨ p5)) ∨ p3) ∨ (p3 ∨ p2)) ∨ p5))) ∨ p5) ∨ True)) → (((True ∨ True) ∨ False) ∧ False)) → p5) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h1
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h2 : (p4 ∨ (((p5 ∨ (p3 ∧ ((((True → (False ∨ p5)) ∨ p3) ∨ (p3 ∨ p2)) ∨ p5))) ∨ p5) ∨ True)) := by
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
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
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_61167802332137637138033229982 : ((False ∧ (((p2 ∧ p1) ∨ p4) ∨ ((p4 ∨ ((p2 ∧ p5) ∧ (True ∨ p1))) → (((p1 → p5) ∨ ((p5 ∨ (p3 → p1)) ∧ p2)) ∧ p4)))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_114570103751147828569745684250 : ((((((p3 ∨ False) → (((p1 → p2) → (p5 → p4)) ∧ p1)) → p1) → (p3 → p2)) ∧ ((p4 ∧ ((p5 ∧ p1) → p3)) ∨ p3)) ∨ (True ∨ False)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_316924518283825985967100479193 : (p3 ∨ (p2 → (((p3 ∧ (p5 ∧ (p2 ∧ ((True → p2) ∨ p1)))) ∧ (p3 ∨ ((((p5 ∨ p1) ∨ False) → True) → (p1 → p5)))) ∨ (p2 ∧ p2)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- One of the premise coincides with the conclusion.
  exact h1
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_619695660372714476128487861553 : (((((p5 ∧ True) ∧ (((p4 → False) ∨ p2) ∧ (((((True → (p3 ∧ ((p5 ∨ p3) ∧ p5))) ∨ True) ∨ p2) → (p2 ∧ True)) → p2))) ∨ p1) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_50133474030941106599518425057 : (((p5 ∨ ((p1 ∨ (((False ∧ (p5 → ((False → (p2 ∨ False)) ∧ p5))) → p2) ∧ (p2 → p1))) ∧ p2)) ∧ (((p5 → p5) → p2) ∧ True)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_115765103529013170975675555521 : (((p4 ∨ ((p3 → (True ∧ p1)) → p5)) → ((((p4 → p1) → p2) ∨ ((p3 → (p3 ∨ (p2 ∨ p4))) ∧ p4)) ∨ (p2 → p2))) ∨ (p5 ∨ p2)) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h2 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h3
    -- One of the premise coincides with the conclusion.
    exact h3
  case inr h4 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h5
    -- One of the premise coincides with the conclusion.
    exact h5



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_60689218312740229620719042949 : ((True ∧ ((p5 ∨ ((p3 ∨ p1) ∨ (p1 ∧ (p3 ∧ ((p1 → p1) → False))))) ∨ ((p5 ∧ (p2 ∨ p1)) ∧ (p4 ∨ ((p3 ∨ p1) ∨ p3))))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_177697065628727287393526826501 : ((((((p5 ∨ (p2 ∨ p4)) ∧ p2) → (False ∨ p5)) ∨ (True → p4)) ∧ p3) ∨ ((True → p3) ∨ (p4 → (p4 ∨ ((p3 ∧ (p4 ∧ p2)) ∨ p2))))) := by
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
theorem thm_5_vars_146951800763847293821521518254 : (((((True ∨ p2) ∧ (((((p1 ∧ p4) ∨ p1) ∧ False) → (((p4 → p5) ∨ True) → True)) → p4)) ∨ p4) ∧ p3) ∨ ((p1 ∨ p2) ∨ (True ∧ True))) := by
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
theorem thm_5_vars_218400163304912760122226427004 : (((True ∧ p4) → (p3 → True)) → (p3 ∨ (((((False → False) ∨ (True ∧ p3)) ∧ (((True ∧ p5) ∧ (p5 ∧ p1)) → p5)) → p5) ∨ (True ∨ p5)))) := by
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
theorem thm_5_vars_260270963338468555525155786284 : ((p2 → p3) → (p1 → ((p4 ∧ ((p1 ∧ ((p4 ∨ p4) ∨ (((p3 ∨ (p5 ∨ ((p5 → p1) ∨ (p4 ∧ p1)))) → p5) ∧ p3))) ∧ p4)) ∨ True))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_752999758193121180301688530836 : (((False ∧ (((p5 ∧ ((True ∨ (p1 → p5)) ∨ p4)) ∧ (p5 ∨ (p5 ∨ (p1 ∧ (p2 ∨ ((False ∨ (p3 → (p4 ∨ p5))) ∧ p3)))))) → p3)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_155527959680804483193889102943 : (((True → (p3 ∨ p3)) ∨ ((((False ∧ False) ∨ (((p2 ∨ p4) ∨ p1) ∨ (p4 ∧ p2))) ∧ p2) → p2)) ∧ ((p1 ∨ (p2 → (False ∨ p4))) ∨ True)) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
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
    let h5 := h4.left
    let h6 := h4.right
    -- False on the left can always be used.
    apply False.elim h5
  case inr h7 =>
    -- Disjunctions on the left can always be decomposed.
    cases h7
    case inl h8 =>
      -- Disjunctions on the left can always be decomposed.
      cases h8
      case inl h9 =>
        -- Disjunctions on the left can always be decomposed.
        cases h9
        case inl h10 =>
          -- One of the premise coincides with the conclusion.
          exact h3
        case inr h11 =>
          -- One of the premise coincides with the conclusion.
          exact h3
      case inr h12 =>
        -- One of the premise coincides with the conclusion.
        exact h3
    case inr h13 =>
      -- Conjunctions on the left can always be decomposed.
      let h14 := h13.left
      let h15 := h13.right
      -- One of the premise coincides with the conclusion.
      exact h3
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_119552610298799337116130672846 : ((p5 → ((True → (((False → (False → (p3 ∨ p1))) ∧ ((p1 → False) ∨ p4)) ∧ (p3 ∧ (p5 ∨ p2)))) → ((False ∨ p3) ∧ True))) ∨ (True ∨ False)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_257899275744756428554113880391 : ((p4 ∨ True) → (p4 ∨ (((p2 ∧ ((p4 ∧ False) ∨ p5)) ∧ ((p3 ∨ (((p4 ∧ ((True → True) ∧ False)) ∧ p2) ∨ (p2 ∧ True))) → p3)) ∨ True))) := by
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
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_329677668963493309312576389475 : (True → ((p1 ∨ p2) → (p5 ∨ ((p4 ∨ ((p4 → (((p5 ∨ p4) ∨ False) ∧ (p4 ∧ p4))) → p1)) ∨ ((p2 ∨ p5) ∨ (p4 → (p4 ∧ p3))))))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Disjunctions on the left can always be decomposed.
  cases h2
  case inl h3 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h4
    -- One of the premise coincides with the conclusion.
    exact h3
  case inr h5 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- One of the premise coincides with the conclusion.
    exact h5



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_157371567175205944695635059675 : (((p4 → ((p5 ∨ p1) ∨ (p2 ∨ ((p1 → p4) ∧ (True → (p4 ∧ (p2 ∨ (p5 ∨ p1)))))))) → p2) ∨ (True ∧ (False → ((True ∧ p4) → p3)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Conjunctions on the left can always be decomposed.
  let h3 := h2.left
  let h4 := h2.right
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_310769692105843849680782393382 : (p2 ∨ (((p4 ∨ False) ∧ True) ∨ (((p3 ∨ p3) ∨ False) ∨ ((p2 ∨ (p5 → (((p3 → True) ∧ ((p3 → p3) → (p4 ∧ p5))) → p4))) ∨ p3)))) := by
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
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Conjunctions on the left can always be decomposed.
  let h3 := h2.left
  let h4 := h2.right
  -- We want to use the implication h4 based on <expert-advice>. So we show its premise.
  have h5 : (p3 → p3) := by
    -- Implications on the right can always be decomposed.
    intro h6
    -- One of the premise coincides with the conclusion.
    exact h6
  -- We have shown the premise of h4, we can now drive its conclusion.
  let h7 := h4 h5
  -- We need to get the left conjuct of h7 based on <expert-advice>.
  let h8 := h7.left
  -- One of the premise coincides with the conclusion.
  exact h8



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_215129490910869019394767209253 : (((p4 → True) → (p3 ∨ p2)) ∨ (p5 → ((p5 → p2) ∨ ((p1 → (p5 ∨ True)) ∧ (((p3 → (p1 ∨ False)) → p5) ∧ ((False → True) ∨ p5)))))) := by
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
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- One of the premise coincides with the conclusion.
  exact h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h3
  -- One of the premise coincides with the conclusion.
  exact h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_725928048210738748221063492681 : (((((p2 → False) ∧ p4) ∨ ((((p1 ∨ ((p3 ∧ True) → p3)) → p5) ∧ p3) ∨ (((True ∨ ((p3 ∨ (p4 → p1)) → p3)) → p1) → p4))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_684732775415398301442102552307 : (((((p5 ∨ False) ∧ (True → ((p5 ∧ (p4 → p2)) ∧ ((True ∨ (p4 → (False → p3))) → p1)))) ∨ (True ∨ (p5 ∨ (p2 ∨ (False ∧ True))))) ∨ p1) ∧ True) := by
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
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_221740154126073850125542527000 : (((False ∧ p5) → p2) ∧ (((False ∧ ((p2 ∨ p3) ∧ ((p3 ∨ p1) ∧ True))) ∨ (False ∨ p5)) ∨ (False ∨ ((p2 ∨ (p1 ∧ p2)) → (True ∧ p2))))) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- False on the left can always be used.
  apply False.elim h2
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h4
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- Disjunctions on the left can always be decomposed.
  cases h4
  case inl h5 =>
    -- One of the premise coincides with the conclusion.
    exact h5
  case inr h6 =>
    -- Conjunctions on the left can always be decomposed.
    let h7 := h6.left
    let h8 := h6.right
    -- One of the premise coincides with the conclusion.
    exact h8



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_961273344805031613640477797353 : ((((p2 ∨ True) ∧ ((False ∨ (True → p3)) ∧ ((((p2 ∨ ((True → p4) ∨ p3)) ∧ (p3 → (p5 ∧ p4))) ∧ ((p4 ∨ p5) ∨ p3)) → p4))) → p3) ∧ True) := by
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
    -- Conjunctions on the left can always be decomposed.
    let h5 := h3.left
    let h6 := h3.right
    -- Disjunctions on the left can always be decomposed.
    cases h5
    case inl h7 =>
      -- False on the left can always be used.
      apply False.elim h7
    case inr h8 =>
      -- We want to use the implication h8 based on <expert-advice>. So we show its premise.
      have h9 : True := by
        -- True on the right can always be proven directly.
        apply True.intro
      -- We have shown the premise of h8, we can now drive its conclusion.
      let h10 := h8 h9
      -- One of the premise coincides with the conclusion.
      exact h10
  case inr h11 =>
    -- Conjunctions on the left can always be decomposed.
    let h12 := h3.left
    let h13 := h3.right
    -- Disjunctions on the left can always be decomposed.
    cases h12
    case inl h14 =>
      -- False on the left can always be used.
      apply False.elim h14
    case inr h15 =>
      -- We want to use the implication h15 based on <expert-advice>. So we show its premise.
      have h16 : True := by
        -- True on the right can always be proven directly.
        apply True.intro
      -- We have shown the premise of h15, we can now drive its conclusion.
      let h17 := h15 h16
      -- One of the premise coincides with the conclusion.
      exact h17
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_113986885199275102225130054152 : (((p5 ∨ ((p3 ∨ ((p3 ∨ (p4 → p2)) ∨ ((p4 ∨ ((p1 ∧ p1) → p1)) ∨ (p2 ∧ p1)))) ∨ p2)) ∧ (p5 ∧ (p5 ∨ p3))) ∨ (False → p2)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_95546542222297635496237717036 : ((p5 ∧ (((((False ∨ p2) ∨ p5) → p4) ∧ (((((False → (p4 ∨ (p5 ∨ False))) → p3) → p5) ∨ p4) ∧ True)) ∧ ((p3 → p3) ∧ p2))) → p4) := by
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
  -- Conjunctions on the left can always be decomposed.
  let h8 := h7.left
  let h9 := h7.right
  -- Disjunctions on the left can always be decomposed.
  cases h8
  case inl h10 =>
    -- Conjunctions on the left can always be decomposed.
    let h11 := h5.left
    let h12 := h5.right
    -- We want to use the implication h6 based on <expert-advice>. So we show its premise.
    have h13 : ((False ∨ p2) ∨ p5) := by
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- One of the premise coincides with the conclusion.
      exact h2
    -- We have shown the premise of h6, we can now drive its conclusion.
    let h14 := h6 h13
    -- One of the premise coincides with the conclusion.
    exact h14
  case inr h15 =>
    -- Conjunctions on the left can always be decomposed.
    let h16 := h5.left
    let h17 := h5.right
    -- One of the premise coincides with the conclusion.
    exact h15



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_951063072005377825521461516005 : ((((False ∨ (True → False)) ∧ (False ∨ ((False ∨ ((p3 ∨ ((True → (False ∨ (p3 ∧ (p2 → (p5 ∨ p2))))) ∧ (False ∧ p2))) ∧ True)) → False))) → p3) ∧ True) := by
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
    -- False on the left can always be used.
    apply False.elim h4
  case inr h5 =>
    -- Disjunctions on the left can always be decomposed.
    cases h3
    case inl h6 =>
      -- False on the left can always be used.
      apply False.elim h6
    case inr h7 =>
      -- We want to use the implication h5 based on <expert-advice>. So we show its premise.
      have h8 : True := by
        -- True on the right can always be proven directly.
        apply True.intro
      -- We have shown the premise of h5, we can now drive its conclusion.
      let h9 := h5 h8
      -- False on the left can always be used.
      apply False.elim h9
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_722409812267510913110947573737 : (((((p5 ∧ p2) ∧ True) ∧ (p3 ∨ (((p5 ∧ ((p1 ∧ (p2 ∧ ((p5 → ((p1 ∨ (p2 → True)) → p5)) ∨ p2))) ∨ p3)) ∨ p5) ∧ p4))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_113404541712344581907576881756 : (((p5 → ((True → (((p4 ∨ ((False ∨ p1) → True)) → False) ∨ (((p4 ∨ p4) ∧ (p2 ∨ True)) ∧ p4))) ∨ True)) ∧ (p2 → True)) ∨ (p4 → p4)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_158518315322413277746299640094 : (((p3 ∨ False) → (((p2 ∨ (p3 ∨ (p4 → ((p5 → p2) ∧ p4)))) ∨ ((p2 → True) ∨ p2)) → p5)) ∨ (p5 → (((True ∨ p4) ∧ True) ∨ False))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
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



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_116073411125050473696525314487 : ((((p1 → False) ∧ p5) ∧ (((((p1 → (((p1 ∨ True) ∨ False) ∧ p3)) ∨ (True ∨ True)) ∨ p1) → (p1 ∨ True)) ∧ (False → True))) ∨ (False → p4)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_124152448741592410111094150056 : (((((p1 ∨ ((p3 ∨ p2) ∨ p5)) ∨ (p1 → p2)) ∧ p2) ∨ (((p5 ∧ False) → p4) ∧ (p3 ∨ (((p4 ∧ p3) ∨ True) → p4)))) → (p1 ∨ True)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h2 =>
    -- Conjunctions on the left can always be decomposed.
    let h3 := h2.left
    let h4 := h2.right
    -- Disjunctions on the left can always be decomposed.
    cases h3
    case inl h5 =>
      -- Disjunctions on the left can always be decomposed.
      cases h5
      case inl h6 =>
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- One of the premise coincides with the conclusion.
        exact h6
      case inr h7 =>
        -- Disjunctions on the left can always be decomposed.
        cases h7
        case inl h8 =>
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
    -- Conjunctions on the left can always be decomposed.
    let h14 := h13.left
    let h15 := h13.right
    -- Disjunctions on the left can always be decomposed.
    cases h15
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



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_340978400525369080825205754291 : (p2 → (((p1 ∨ p1) ∨ (((((True → (((p4 → (p1 ∧ p5)) ∨ (True ∨ p3)) ∧ (p2 → p2))) ∧ p4) ∧ (p3 → p5)) ∨ p4) ∨ p2)) ∨ True)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_198189748849074338808184443563 : (((False → p1) → (p3 ∧ ((True ∧ False) → p3))) ∨ (p5 → (p4 ∨ (p1 → (p5 ∧ ((((((p4 → p3) ∨ p3) ∨ True) ∧ p3) ∨ p2) ∨ p5)))))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h2
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- One of the premise coincides with the conclusion.
  exact h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_166579300903366012092802693233 : ((True → ((p3 ∧ ((p1 → (p3 → (p1 ∨ (False ∨ (False ∨ p4))))) → False)) ∨ (p3 ∨ p3))) ∨ (p3 → ((p1 ∨ p3) → (True → (False → p1))))) := by
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
  apply False.elim h4



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_733438064890442302429043610976 : ((((p4 ∧ p1) ∧ (((((p1 ∨ True) ∧ p2) ∨ (p2 ∨ (p1 ∧ ((p3 ∧ p3) ∨ (p2 ∨ p5))))) ∨ p5) → (((p4 ∧ p4) ∨ p3) → False))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_350574633439884434820166680280 : (p4 → (((p5 ∧ ((((False ∧ p2) ∧ p3) → p4) → (False ∧ p1))) ∧ ((((True → False) ∧ (False ∨ (p1 ∧ (False ∨ p4)))) ∨ False) → p3)) → p2)) := by
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
  -- We want to use the implication h6 based on <expert-advice>. So we show its premise.
  have h7 : (((False ∧ p2) ∧ p3) → p4) := by
    -- Implications on the right can always be decomposed.
    intro h8
    -- Conjunctions on the left can always be decomposed.
    let h9 := h8.left
    let h10 := h8.right
    -- Conjunctions on the left can always be decomposed.
    let h11 := h9.left
    let h12 := h9.right
    -- False on the left can always be used.
    apply False.elim h11
  -- We have shown the premise of h6, we can now drive its conclusion.
  let h13 := h6 h7
  -- We need to get the left conjuct of h13 based on <expert-advice>.
  let h14 := h13.left
  -- False on the left can always be used.
  apply False.elim h14



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_112081087292328300084557735283 : ((((p5 ∧ p4) ∨ (p2 ∨ ((((True ∨ (True ∧ (p5 → p3))) ∨ p1) ∧ ((p5 ∨ (p1 ∧ p2)) ∨ (p4 ∨ p2))) ∧ p5))) ∨ True) ∨ (p4 ∧ p5)) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_641674573166061520821491314454 : (((((False ∨ p4) → (((p4 ∨ p4) ∨ ((((p1 ∧ False) → p5) ∨ (((False ∨ ((p1 ∧ p2) ∧ p4)) → p1) ∧ p5)) → False)) → p3)) → p4) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_196724938879320761959880417118 : (((((p3 ∨ False) → (p3 ∨ p4)) → p4) ∧ p4) ∨ ((((p2 ∨ p4) → (False ∧ True)) ∧ ((p2 → p2) ∨ (p1 → p2))) ∨ ((p5 ∧ p4) ∨ True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_855385289256075895715304623038 : (((((p5 → (((True → (p3 ∧ (p2 ∧ ((True ∨ p2) ∧ (((p2 ∧ True) ∧ p2) ∧ (p1 ∧ p5)))))) → p1) ∧ (False → p2))) ∧ True) → False) → p4) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h1
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h2 : ((p5 → (((True → (p3 ∧ (p2 ∧ ((True ∨ p2) ∧ (((p2 ∧ True) ∧ p2) ∧ (p1 ∧ p5)))))) → p1) ∧ (False → p2))) ∧ True) := by
    -- Conjunctions on the right can always be decomposed.
    apply And.intro
    -- Implications on the right can always be decomposed.
    intro h3
    -- Conjunctions on the right can always be decomposed.
    apply And.intro
    -- Implications on the right can always be decomposed.
    intro h4
    -- We want to use the implication h4 based on <expert-advice>. So we show its premise.
    have h5 : True := by
      -- True on the right can always be proven directly.
      apply True.intro
    -- We have shown the premise of h4, we can now drive its conclusion.
    let h6 := h4 h5
    -- We need to get the right conjuct of h6 based on <expert-advice>.
    let h7 := h6.right
    -- We need to get the right conjuct of h7 based on <expert-advice>.
    let h8 := h7.right
    -- We need to get the right conjuct of h8 based on <expert-advice>.
    let h9 := h8.right
    -- We need to get the right conjuct of h9 based on <expert-advice>.
    let h10 := h9.right
    -- We need to get the left conjuct of h10 based on <expert-advice>.
    let h11 := h10.left
    -- One of the premise coincides with the conclusion.
    exact h11
    -- Implications on the right can always be decomposed.
    intro h12
    -- False on the left can always be used.
    apply False.elim h12
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h13 := h1 h2
  -- False on the left can always be used.
  apply False.elim h13
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_783612037406063200622632523227 : (((p3 ∨ (((p1 ∨ (((False → p3) → p3) ∧ p2)) ∨ p1) ∧ ((True → ((((p4 ∧ p1) ∨ ((p2 ∧ p3) → p4)) ∨ p4) ∧ True)) → False))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_178863564815278896119278602247 : (((False → (p5 ∧ p2)) → (False ∨ (((p3 → p2) → True) ∧ (True → False)))) ∨ ((p1 ∨ (True ∨ ((p3 ∧ p5) ∧ (p2 → p5)))) ∧ (True ∧ True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_309796035623299722776336375493 : (p2 ∨ ((((p5 ∨ p2) → ((((p1 ∨ False) ∨ (True → p3)) → (p4 → p2)) ∧ p3)) → ((False ∨ p4) ∨ p5)) ∨ ((p1 → (p5 → True)) ∨ True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_931684633009349493612182378436 : ((((((((p5 ∧ p1) ∧ True) ∨ True) → False) ∧ p1) ∧ (p1 ∧ (True → ((p2 → p5) → (((p4 ∨ (True ∨ (p2 → p1))) ∨ False) ∨ False))))) → p4) ∧ True) := by
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
  let h6 := h3.left
  let h7 := h3.right
  -- We want to use the implication h4 based on <expert-advice>. So we show its premise.
  have h8 : (((p5 ∧ p1) ∧ True) ∨ True) := by
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h4, we can now drive its conclusion.
  let h9 := h4 h8
  -- False on the left can always be used.
  apply False.elim h9
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_340698270627944658315265296487 : (p2 → (((((p1 ∨ p2) ∧ (((True ∧ (p4 ∧ False)) ∧ (p3 → ((p5 ∧ ((p4 ∨ True) → False)) ∨ p4))) → (p4 ∧ p5))) → False) ∧ True) ∨ p2)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_708101100264285987817545911602 : ((((p5 ∨ (((p5 → p5) ∨ False) → (False ∧ False))) ∨ (((p4 → (p4 ∧ ((p3 ∨ (p5 → ((p1 ∧ p4) → True))) ∧ True))) ∨ True) ∨ p1)) ∨ p2) ∧ True) := by
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
theorem thm_5_vars_125558141081982108152802032753 : (((p1 → p2) ∧ ((True ∨ ((p4 ∨ True) ∧ (p5 → False))) ∧ ((((p1 ∨ p3) → (False ∨ True)) ∧ (p5 ∨ p3)) ∧ (p1 ∧ p1)))) → (False ∨ p1)) := by
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
    -- Conjunctions on the left can always be decomposed.
    let h7 := h5.left
    let h8 := h5.right
    -- Conjunctions on the left can always be decomposed.
    let h9 := h7.left
    let h10 := h7.right
    -- Disjunctions on the left can always be decomposed.
    cases h10
    case inl h11 =>
      -- Conjunctions on the left can always be decomposed.
      let h12 := h8.left
      let h13 := h8.right
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- One of the premise coincides with the conclusion.
      exact h13
    case inr h14 =>
      -- Conjunctions on the left can always be decomposed.
      let h15 := h8.left
      let h16 := h8.right
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- One of the premise coincides with the conclusion.
      exact h16
  case inr h17 =>
    -- Conjunctions on the left can always be decomposed.
    let h18 := h17.left
    let h19 := h17.right
    -- Disjunctions on the left can always be decomposed.
    cases h18
    case inl h20 =>
      -- Conjunctions on the left can always be decomposed.
      let h21 := h5.left
      let h22 := h5.right
      -- Conjunctions on the left can always be decomposed.
      let h23 := h21.left
      let h24 := h21.right
      -- Disjunctions on the left can always be decomposed.
      cases h24
      case inl h25 =>
        -- Conjunctions on the left can always be decomposed.
        let h26 := h22.left
        let h27 := h22.right
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- One of the premise coincides with the conclusion.
        exact h27
      case inr h28 =>
        -- Conjunctions on the left can always be decomposed.
        let h29 := h22.left
        let h30 := h22.right
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- One of the premise coincides with the conclusion.
        exact h30
    case inr h31 =>
      -- Conjunctions on the left can always be decomposed.
      let h32 := h5.left
      let h33 := h5.right
      -- Conjunctions on the left can always be decomposed.
      let h34 := h32.left
      let h35 := h32.right
      -- Disjunctions on the left can always be decomposed.
      cases h35
      case inl h36 =>
        -- Conjunctions on the left can always be decomposed.
        let h37 := h33.left
        let h38 := h33.right
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- One of the premise coincides with the conclusion.
        exact h38
      case inr h39 =>
        -- Conjunctions on the left can always be decomposed.
        let h40 := h33.left
        let h41 := h33.right
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- One of the premise coincides with the conclusion.
        exact h41



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_147423849811605591474890382599 : ((((p5 → (p5 → p1)) ∧ (p2 ∧ (p3 ∨ ((((p3 ∧ ((p1 ∧ p2) ∨ True)) ∨ p5) ∨ True) → p5)))) ∨ True) ∨ ((p2 → (p4 ∨ False)) ∧ p2)) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_315456077030425391165884636088 : (p3 ∨ (((p5 ∧ p4) ∧ p5) → ((((((p3 ∧ (p4 ∨ (p3 ∧ True))) ∧ True) ∨ (p3 ∨ (p2 ∧ (True ∧ (True ∧ p2))))) ∨ False) ∨ p2) ∨ True))) := by
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
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_125579945882803298659469062574 : (((p3 → p2) ∧ ((((p2 → p1) ∨ (p1 → (((True → p4) ∧ p5) → (p1 ∨ (p3 ∨ p4))))) → p4) ∨ (False ∧ (p5 ∧ True)))) → (p4 ∧ p4)) := by
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
    -- We want to use the implication h4 based on <expert-advice>. So we show its premise.
    have h5 : ((p2 → p1) ∨ (p1 → (((True → p4) ∧ p5) → (p1 ∨ (p3 ∨ p4))))) := by
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Implications on the right can always be decomposed.
      intro h6
      -- Implications on the right can always be decomposed.
      intro h7
      -- Conjunctions on the left can always be decomposed.
      let h8 := h7.left
      let h9 := h7.right
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- One of the premise coincides with the conclusion.
      exact h6
    -- We have shown the premise of h4, we can now drive its conclusion.
    let h10 := h4 h5
    -- One of the premise coincides with the conclusion.
    exact h10
  case inr h11 =>
    -- Conjunctions on the left can always be decomposed.
    let h12 := h11.left
    let h13 := h11.right
    -- False on the left can always be used.
    apply False.elim h12
  -- Conjunctions on the left can always be decomposed.
  let h14 := h1.left
  let h15 := h1.right
  -- Disjunctions on the left can always be decomposed.
  cases h15
  case inl h16 =>
    -- We want to use the implication h16 based on <expert-advice>. So we show its premise.
    have h17 : ((p2 → p1) ∨ (p1 → (((True → p4) ∧ p5) → (p1 ∨ (p3 ∨ p4))))) := by
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Implications on the right can always be decomposed.
      intro h18
      -- Implications on the right can always be decomposed.
      intro h19
      -- Conjunctions on the left can always be decomposed.
      let h20 := h19.left
      let h21 := h19.right
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- One of the premise coincides with the conclusion.
      exact h18
    -- We have shown the premise of h16, we can now drive its conclusion.
    let h22 := h16 h17
    -- One of the premise coincides with the conclusion.
    exact h22
  case inr h23 =>
    -- Conjunctions on the left can always be decomposed.
    let h24 := h23.left
    let h25 := h23.right
    -- False on the left can always be used.
    apply False.elim h24



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_190988337327077520360832697479 : ((((p1 ∨ (p5 → False)) → p3) ∨ (True → (p4 ∧ p1))) ∨ ((p4 → (p4 ∧ ((False ∧ (p1 ∧ p2)) ∨ (((True ∨ p1) → p5) ∨ p4)))) ∨ False)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- One of the premise coincides with the conclusion.
  exact h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_783213546375226804904113558532 : (((p3 ∨ (((p4 ∧ (True ∧ ((((((p3 ∨ p2) → True) ∧ p2) ∨ True) ∨ (p1 ∧ p3)) ∧ (p5 ∧ p2)))) → p1) → (p4 ∧ (p3 ∧ p2)))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_624935705998051146088759441219 : ((((p5 ∨ ((p1 ∨ p3) → (False ∨ (p1 ∧ ((p2 ∨ ((p2 ∧ p3) → False)) ∨ (False ∧ (p5 ∨ (((p4 ∨ p4) ∧ p4) ∨ p2)))))))) ∨ True) ∨ p4) ∧ True) := by
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
theorem thm_5_vars_233395844035157217100773305793 : ((False ∨ (True ∨ p1)) → ((p5 → ((((p5 ∨ p5) ∨ (p2 ∨ False)) → (((False ∨ (False → p4)) ∨ p5) ∨ (False ∧ p3))) ∧ (p2 ∨ False))) ∨ True)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h2 =>
    -- False on the left can always be used.
    apply False.elim h2
  case inr h3 =>
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
theorem thm_5_vars_148439063149420904472630427332 : (((p4 ∨ ((p2 → ((False ∨ (p3 ∨ p3)) ∧ (False → p5))) → (p5 ∧ p3))) → ((p2 ∨ (p4 ∨ p4)) → p4)) ∨ (((p3 → p4) ∧ p2) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_48025581767070326007290866927 : (((((((p5 ∧ ((p3 → p5) → p2)) ∧ p2) ∧ p3) ∨ (p5 ∨ False)) → (((p5 ∧ False) ∧ (p1 ∨ (True ∨ True))) ∨ p4)) → (p2 ∨ p1)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_694355831201366607930451320008 : (((((False ∧ p2) ∧ (p2 ∨ ((p3 ∧ p1) ∨ (p5 → ((p4 ∨ p4) ∨ p2))))) ∨ ((False ∧ p3) → (p5 → ((p5 ∧ p3) ∧ (p5 → p5))))) ∨ p4) ∧ True) := by
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
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Conjunctions on the left can always be decomposed.
  let h3 := h1.left
  let h4 := h1.right
  -- False on the left can always be used.
  apply False.elim h3
  -- Conjunctions on the left can always be decomposed.
  let h5 := h1.left
  let h6 := h1.right
  -- False on the left can always be used.
  apply False.elim h5
  -- Implications on the right can always be decomposed.
  intro h7
  -- Conjunctions on the left can always be decomposed.
  let h8 := h1.left
  let h9 := h1.right
  -- False on the left can always be used.
  apply False.elim h8
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_328102618826644328088550559903 : (True → (((((p1 ∨ ((((True ∨ p3) ∨ (p3 ∧ (p2 ∧ False))) ∨ ((p5 → p2) ∧ p2)) ∧ p4)) → False) ∧ True) → p2) ∨ ((True ∨ p5) ∨ p2))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_171623615192203294845437476839 : (((((p1 → True) → p1) ∨ (((False ∨ p3) ∧ (p5 → p1)) → (p2 ∨ p5))) ∨ True) ∨ ((((p5 ∨ True) ∧ ((p3 → p2) ∧ p5)) ∨ True) ∨ p4)) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_180417334189824327695933639799 : ((((False ∧ (True ∨ (False → ((False → False) → False)))) ∧ p1) → (True ∧ p2)) → ((((((True → p2) ∧ (p1 ∧ True)) → p1) ∨ p2) → False) ∨ True)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_342021710967228079981148503392 : (p2 → ((p2 → ((((p4 ∨ ((p4 → (((p5 ∧ p1) → p2) ∧ p5)) → False)) ∧ (p3 ∧ (True ∨ p5))) ∧ p5) ∧ False)) ∨ (True ∨ (p5 ∧ p4)))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_303116036327783632242739783139 : (False ∨ (p3 → (((p2 ∨ (((p3 ∨ p4) ∧ (((p3 → True) → p2) → False)) ∧ p5)) ∨ (p1 → ((False ∧ (p2 ∨ p1)) → p3))) ∨ (p4 ∧ p1)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h2
  -- Implications on the right can always be decomposed.
  intro h3
  -- Conjunctions on the left can always be decomposed.
  let h4 := h3.left
  let h5 := h3.right
  -- False on the left can always be used.
  apply False.elim h4



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_133943962444263745672450606735 : (((p1 → ((p1 ∧ (((((((p1 → True) ∧ p3) → False) ∧ (p3 ∨ p5)) → p1) ∧ p2) ∨ p3)) → (p3 ∨ p4))) ∧ True) ∨ (p5 → (p1 → p1))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- One of the premise coincides with the conclusion.
  exact h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_621239722430325106292269133580 : ((((True ∧ ((((p1 ∧ True) ∨ (((p1 ∨ True) → ((True ∧ True) ∧ False)) ∨ p1)) → ((True → (p5 ∨ False)) ∨ p5)) ∧ (p5 ∧ p2))) ∨ p4) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_42001234735828726627855037910 : ((((p1 → p4) ∧ (p1 ∨ (p3 ∧ ((((((p2 ∧ False) → p5) → p4) ∧ (True ∨ (p1 → ((p5 ∧ p1) → False)))) → p2) ∧ p4)))) ∨ True) ∨ p2) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_626003443409475282320922936785 : ((((p2 → ((p1 ∧ (p5 ∨ (p3 ∨ p5))) ∨ ((((p5 ∨ False) ∧ (p2 ∧ p3)) ∨ (True ∨ (p4 ∧ p4))) ∨ (p1 ∧ (p3 → False))))) ∨ True) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_184897976558412323021800187159 : ((((p4 ∧ p3) ∧ p5) ∨ (((False ∨ p4) ∨ (p1 ∨ p3)) ∨ p3)) ∨ (p3 → (((p3 ∨ (p1 → ((False ∧ True) → False))) → True) ∨ (p1 ∧ p4)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h2
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_309363476879709558733743459830 : (p2 ∨ (((((p2 ∧ p2) ∨ p1) ∨ p3) ∨ (((((p4 ∨ (((p5 ∧ True) ∨ p1) → p1)) ∨ (p5 → p4)) → p1) ∧ p1) → p1)) ∨ (p5 ∧ False))) := by
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
  -- One of the premise coincides with the conclusion.
  exact h3



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_614562808181590738431066131404 : (((((((p3 ∨ True) ∧ p1) ∧ ((p5 ∧ (True → p5)) ∨ (((p1 ∧ p1) → True) → (True → p4)))) ∧ ((p5 ∧ p5) ∧ (p5 ∨ p1))) ∨ p2) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_204561812694784177775956282104 : ((((p1 ∧ p1) ∧ (p1 ∧ False)) ∨ p4) ∨ ((True ∨ (((p3 ∨ ((p1 ∧ (p4 ∨ ((p5 ∧ (p3 ∧ p4)) ∨ True))) ∨ p2)) ∧ False) ∨ p3)) ∨ p5)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_38734730613304305563200446236 : ((((p2 ∨ (((True → p3) → False) ∨ p3)) → ((p1 ∧ p3) ∨ (((False ∨ ((p3 ∨ p4) → False)) ∧ p4) ∨ (p4 ∨ (p5 ∨ True))))) ∧ p5) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_353727151158674070137174483569 : (p4 → (True → ((p4 ∧ (((((p5 → p1) → ((p3 → p5) ∧ ((True ∨ p1) ∨ p3))) ∧ (p4 → p1)) → p2) ∧ (True → False))) ∨ (p4 → p4)))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h3
  -- One of the premise coincides with the conclusion.
  exact h3



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_678944147256179513458520904973 : ((((p4 ∧ ((p5 ∨ (False → ((p2 → ((p3 ∧ p5) ∧ (True ∨ True))) → (p3 ∨ (p5 ∧ False))))) → False)) ∨ (((p4 → False) → p2) → p3)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_350049034213005969503433498354 : (p4 → (((p5 ∨ (p4 → ((p5 ∨ ((((p2 ∧ p3) → p2) ∨ (True ∨ (p3 ∨ (True ∧ (False ∨ p2))))) ∧ p2)) → (p5 → p3)))) → p2) ∨ p4)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_46082431057910442753776541295 : (((((((p2 ∧ (False ∧ True)) ∧ p2) ∨ ((p4 ∧ (False ∧ (False → p2))) ∨ p2)) ∧ (p3 ∧ (p1 → (p5 ∧ p1)))) ∨ p4) ∧ (True ∨ p4)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_61113129962240417852132232205 : ((False ∧ (((((p1 ∧ False) ∨ p3) ∨ False) ∨ ((p1 → (p3 → True)) ∧ p3)) ∨ (p3 ∧ ((p1 ∨ p5) ∧ (p3 → ((False ∨ True) ∨ p3)))))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_305771795446754097406225272594 : (p1 ∨ ((((False ∧ p2) ∨ False) ∧ (p1 ∨ (p5 → p5))) ∨ (p1 → (((False → (p4 ∧ (p5 ∨ (False ∧ ((p3 ∨ p1) → p3))))) → True) ∧ True)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h2
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_165232146849547002088401088664 : ((((p3 ∧ p3) ∨ (p2 → (p2 → ((p5 ∧ p5) ∨ (p2 ∧ (False ∧ False)))))) ∨ (p5 ∧ p3)) ∨ (((p1 ∨ True) ∧ p1) → ((p4 → p1) ∨ False))) := by
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
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Implications on the right can always be decomposed.
    intro h5
    -- One of the premise coincides with the conclusion.
    exact h3
  case inr h6 =>
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Implications on the right can always be decomposed.
    intro h7
    -- One of the premise coincides with the conclusion.
    exact h3



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_16626138661349090787622601417 : (((((True ∨ p4) ∧ ((p2 ∧ (p4 → p5)) → ((p2 → (p5 ∧ (p5 → (False ∧ (p4 ∧ True))))) ∧ False))) ∨ p2) ∨ ((False ∧ p1) → False)) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- False on the left can always be used.
  apply False.elim h2
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_758929956676772917714262205782 : (((p2 ∧ (((((p4 ∧ p2) ∨ ((p4 ∧ p3) → ((p1 → p4) → p4))) ∨ p1) ∧ (p5 → (p2 → (p2 ∧ ((p1 → True) ∨ p2))))) → p5)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_316559614117889891452045362027 : (p3 ∨ (p3 ∨ (((False ∨ ((p1 ∨ ((p2 ∧ p1) ∧ True)) → ((p4 ∧ (p3 → (p2 → p2))) → (p5 ∨ (p4 ∨ p3))))) ∨ p4) ∨ (p1 ∧ True)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
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
  -- Implications on the right can always be decomposed.
  intro h2
  -- Conjunctions on the left can always be decomposed.
  let h3 := h2.left
  let h4 := h2.right
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h5 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- One of the premise coincides with the conclusion.
    exact h3
  case inr h6 =>
    -- Conjunctions on the left can always be decomposed.
    let h7 := h6.left
    let h8 := h6.right
    -- Conjunctions on the left can always be decomposed.
    let h9 := h7.left
    let h10 := h7.right
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- One of the premise coincides with the conclusion.
    exact h3



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_37241556053117300355970490194 : (((((p5 ∨ True) → ((((False ∨ (((p2 → p1) → p1) ∧ (p3 → p4))) ∧ p4) → (p4 ∧ p3)) ∨ ((p3 → p4) → p4))) ∧ p3) ∧ p3) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_712946186600264606426331854330 : ((((False ∧ (p1 ∨ (p4 ∨ (p4 ∨ True)))) ∨ ((((True ∨ p3) → (p3 ∨ ((p1 ∨ (p3 ∨ p3)) ∧ p3))) ∨ p1) ∨ (p4 ∨ (p5 → True)))) ∨ p1) ∧ True) := by
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
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_200896852249677248291357980572 : ((False ∨ (p5 ∧ (p4 ∨ ((True ∧ True) ∨ p1)))) → (((p2 ∨ (p1 ∧ (((True ∧ False) ∨ p2) ∧ p4))) → (((p2 ∧ p3) ∧ p5) ∨ p5)) ∨ False)) := by
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
    -- Disjunctions on the left can always be decomposed.
    cases h5
    case inl h6 =>
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- Implications on the right can always be decomposed.
      intro h7
      -- Disjunctions on the left can always be decomposed.
      cases h7
      case inl h8 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- One of the premise coincides with the conclusion.
        exact h4
      case inr h9 =>
        -- Conjunctions on the left can always be decomposed.
        let h10 := h9.left
        let h11 := h9.right
        -- Conjunctions on the left can always be decomposed.
        let h12 := h11.left
        let h13 := h11.right
        -- Disjunctions on the left can always be decomposed.
        cases h12
        case inl h14 =>
          -- Conjunctions on the left can always be decomposed.
          let h15 := h14.left
          let h16 := h14.right
          -- False on the left can always be used.
          apply False.elim h16
        case inr h17 =>
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- One of the premise coincides with the conclusion.
          exact h4
    case inr h18 =>
      -- Disjunctions on the left can always be decomposed.
      cases h18
      case inl h19 =>
        -- Conjunctions on the left can always be decomposed.
        let h20 := h19.left
        let h21 := h19.right
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- Implications on the right can always be decomposed.
        intro h22
        -- Disjunctions on the left can always be decomposed.
        cases h22
        case inl h23 =>
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- One of the premise coincides with the conclusion.
          exact h4
        case inr h24 =>
          -- Conjunctions on the left can always be decomposed.
          let h25 := h24.left
          let h26 := h24.right
          -- Conjunctions on the left can always be decomposed.
          let h27 := h26.left
          let h28 := h26.right
          -- Disjunctions on the left can always be decomposed.
          cases h27
          case inl h29 =>
            -- Conjunctions on the left can always be decomposed.
            let h30 := h29.left
            let h31 := h29.right
            -- False on the left can always be used.
            apply False.elim h31
          case inr h32 =>
            -- Show the right disjunct based on <expert-advice>.
            apply Or.inr
            -- One of the premise coincides with the conclusion.
            exact h4
      case inr h33 =>
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- Implications on the right can always be decomposed.
        intro h34
        -- Disjunctions on the left can always be decomposed.
        cases h34
        case inl h35 =>
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- One of the premise coincides with the conclusion.
          exact h4
        case inr h36 =>
          -- Conjunctions on the left can always be decomposed.
          let h37 := h36.left
          let h38 := h36.right
          -- Conjunctions on the left can always be decomposed.
          let h39 := h38.left
          let h40 := h38.right
          -- Disjunctions on the left can always be decomposed.
          cases h39
          case inl h41 =>
            -- Conjunctions on the left can always be decomposed.
            let h42 := h41.left
            let h43 := h41.right
            -- False on the left can always be used.
            apply False.elim h43
          case inr h44 =>
            -- Show the right disjunct based on <expert-advice>.
            apply Or.inr
            -- One of the premise coincides with the conclusion.
            exact h4



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_610290372606199320478394541912 : ((((((p2 ∧ ((p4 → ((p1 ∨ p2) ∧ (p5 ∨ p5))) ∧ ((p2 ∧ p5) ∧ ((p4 → (True → (p4 → p1))) → p2)))) ∨ False) → p1) ∨ True) ∨ p1) ∧ True) := by
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
theorem thm_5_vars_63088231862955008074260867937 : ((p5 ∧ (((False → (((p4 ∧ ((p1 ∨ ((p3 ∧ p1) ∨ p5)) ∧ p1)) → p1) ∧ p5)) → ((p2 ∧ ((p5 ∨ p1) → True)) ∧ p2)) ∨ p2)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_199582084410883614214473277174 : ((((False → (p1 ∨ (p3 ∧ True))) ∨ p3) → False) → (p1 ∨ (p5 ∨ ((((True ∨ p1) → p5) ∨ False) → (((p3 ∨ p5) ∨ (p5 → p5)) → False))))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h2 : ((False → (p1 ∨ (p3 ∧ True))) ∨ p3) := by
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Implications on the right can always be decomposed.
    intro h3
    -- False on the left can always be used.
    apply False.elim h3
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h4 := h1 h2
  -- False on the left can always be used.
  apply False.elim h4



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_123774054119306493216890148256 : ((((((p1 ∨ (p3 → p4)) ∨ True) ∨ (((True ∨ False) ∧ p3) → p3)) ∨ False) ∨ (((p4 ∧ (p3 ∨ (p4 → p5))) → True) ∨ p1)) → (p4 → p4)) := by
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
      -- Disjunctions on the left can always be decomposed.
      cases h4
      case inl h5 =>
        -- Disjunctions on the left can always be decomposed.
        cases h5
        case inl h6 =>
          -- Disjunctions on the left can always be decomposed.
          cases h6
          case inl h7 =>
            -- One of the premise coincides with the conclusion.
            exact h2
          case inr h8 =>
            -- One of the premise coincides with the conclusion.
            exact h2
        case inr h9 =>
          -- One of the premise coincides with the conclusion.
          exact h2
      case inr h10 =>
        -- One of the premise coincides with the conclusion.
        exact h2
    case inr h11 =>
      -- False on the left can always be used.
      apply False.elim h11
  case inr h12 =>
    -- Disjunctions on the left can always be decomposed.
    cases h12
    case inl h13 =>
      -- One of the premise coincides with the conclusion.
      exact h2
    case inr h14 =>
      -- One of the premise coincides with the conclusion.
      exact h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_114155497562524723021527915065 : ((((True → (p1 → ((((((p3 ∧ True) ∧ True) ∨ p3) ∧ True) ∧ p4) ∨ ((p3 ∨ p1) ∨ p4)))) ∨ p2) → ((p2 → False) ∧ p2)) ∨ (True ∨ p2)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_57023357679657377692720882657 : (((p1 → (True ∨ p4)) ∧ ((p3 ∧ (p2 ∨ ((p1 ∨ p5) ∧ (((p5 ∧ p5) ∧ (True → (True ∨ (p4 ∨ p4)))) → (True ∨ False))))) ∨ False)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_46904046465926226448892616679 : ((((((p4 ∧ (p1 ∨ (p4 ∨ p5))) ∨ (p4 → (((p1 → p1) ∧ p4) ∨ (p4 → (True → p2))))) → (p5 ∨ p3)) ∨ True) ∨ (p2 ∧ p2)) ∨ p5) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



