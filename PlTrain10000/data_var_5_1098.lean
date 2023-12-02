variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_56718367384584672198711662789 : ((((False ∨ True) ∨ p3) ∧ ((p3 ∨ (((((p3 ∧ p4) → p3) → (p3 ∨ p1)) ∨ (p2 ∨ ((False ∨ (p5 ∨ True)) ∨ False))) → p5)) → p4)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_780274085943583151016885305139 : (((p2 ∨ (((((((p3 ∨ p5) → (p3 → True)) → (p1 ∧ p4)) ∨ p4) → ((p5 ∧ p5) ∨ False)) ∨ p2) ∧ (((p1 → p4) → p1) → p2))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_134661296108643689968977989509 : (((((True ∧ (p4 → p5)) → (((False → p4) ∧ p5) ∨ False)) ∨ (((False → (True ∧ p1)) → (p3 ∨ p5)) ∧ p1)) → p2) ∨ (False → (p3 ∧ p4))) := by
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
theorem thm_5_vars_226603201266724045817172578742 : (((p5 → p2) ∨ p1) ∨ (((((p3 → p2) ∨ p2) ∧ (p3 ∧ ((p1 ∨ (p5 ∨ p5)) → p3))) ∨ ((True ∨ p2) ∨ (True → p4))) ∧ (p2 → p2))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro
  -- Implications on the right can always be decomposed.
  intro h1
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_338723917089992845170712062203 : (p1 → ((p1 → True) ∧ (((p3 ∨ (p1 → (((p3 → p2) ∧ ((((p4 ∨ p5) ∧ p1) ∨ p4) ∧ (p4 ∨ False))) → (False ∨ p3)))) → p4) ∨ p1))) := by
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
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_263180868406234585976723939155 : (True ∧ ((p4 → (((p5 ∧ (p4 ∧ p4)) ∧ p3) ∨ (((False → ((False ∧ (p3 ∨ (p3 ∨ True))) ∧ (p2 ∨ p2))) → p3) ∨ True))) ∨ (False ∨ False))) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- True on the right can always be proven directly.
  apply True.intro
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
theorem thm_5_vars_613823362437361112897219837191 : (((((p5 → ((False ∨ (p3 ∨ ((p2 ∧ (p2 ∨ (p1 → p3))) → (p4 → ((p5 → p3) ∨ False))))) ∨ p4)) ∧ (p4 ∨ (True ∨ p1))) ∨ True) ∨ p2) ∧ True) := by
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
theorem thm_5_vars_44091334663011200901362223687 : ((((True ∨ (p1 → ((False → p3) ∧ ((p2 ∨ ((p4 ∨ p5) ∧ (p2 → p1))) ∧ ((p3 ∧ p2) ∧ p4))))) ∧ (p1 ∧ (p1 → p2))) → False) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_23202104310106862245422128896 : (((p4 ∧ (p3 → (p1 ∨ (p5 ∨ False)))) → ((((False ∨ p2) ∨ (p1 ∧ (p4 ∧ (p4 ∧ (p4 ∧ (p3 ∧ (p4 ∨ p1))))))) → False) ∨ True)) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
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
theorem thm_5_vars_151308403059412235137521876855 : (((p2 ∨ (True ∨ (p3 ∧ ((p4 ∧ p4) → (((p4 → True) ∧ True) ∧ (p2 → ((True → True) → p5))))))) → False) → (((p2 ∧ p4) ∧ p2) ∧ p5)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h2 : (p2 ∨ (True ∨ (p3 ∧ ((p4 ∧ p4) → (((p4 → True) ∧ True) ∧ (p2 → ((True → True) → p5))))))) := by
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h3 := h1 h2
  -- False on the left can always be used.
  apply False.elim h3
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h4 : (p2 ∨ (True ∨ (p3 ∧ ((p4 ∧ p4) → (((p4 → True) ∧ True) ∧ (p2 → ((True → True) → p5))))))) := by
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h5 := h1 h4
  -- False on the left can always be used.
  apply False.elim h5
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h6 : (p2 ∨ (True ∨ (p3 ∧ ((p4 ∧ p4) → (((p4 → True) ∧ True) ∧ (p2 → ((True → True) → p5))))))) := by
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h7 := h1 h6
  -- False on the left can always be used.
  apply False.elim h7
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h8 : (p2 ∨ (True ∨ (p3 ∧ ((p4 ∧ p4) → (((p4 → True) ∧ True) ∧ (p2 → ((True → True) → p5))))))) := by
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h9 := h1 h8
  -- False on the left can always be used.
  apply False.elim h9



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_785496066380589480418670744660 : (((p4 ∨ (((p4 ∨ False) ∨ ((((p2 ∧ False) → True) ∨ (p2 → ((p4 → p1) → p4))) → (p2 → (p1 → ((p4 → p3) ∨ p1))))) ∨ p2)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_314733115846179786423430477626 : (p3 ∨ (((((p3 ∧ (False → (((p5 ∧ p2) ∨ p3) ∧ p2))) ∧ p2) ∨ p5) ∧ p1) ∨ (p3 ∨ ((p4 ∨ p4) → (((True → p1) ∨ p1) → p1))))) := by
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
  -- Disjunctions on the left can always be decomposed.
  cases h2
  case inl h3 =>
    -- Disjunctions on the left can always be decomposed.
    cases h1
    case inl h4 =>
      -- We want to use the implication h3 based on <expert-advice>. So we show its premise.
      have h5 : True := by
        -- True on the right can always be proven directly.
        apply True.intro
      -- We have shown the premise of h3, we can now drive its conclusion.
      let h6 := h3 h5
      -- One of the premise coincides with the conclusion.
      exact h6
    case inr h7 =>
      -- We want to use the implication h3 based on <expert-advice>. So we show its premise.
      have h8 : True := by
        -- True on the right can always be proven directly.
        apply True.intro
      -- We have shown the premise of h3, we can now drive its conclusion.
      let h9 := h3 h8
      -- One of the premise coincides with the conclusion.
      exact h9
  case inr h10 =>
    -- Disjunctions on the left can always be decomposed.
    cases h1
    case inl h11 =>
      -- One of the premise coincides with the conclusion.
      exact h10
    case inr h12 =>
      -- One of the premise coincides with the conclusion.
      exact h10



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_157960116961863369484456666579 : ((((p5 ∨ (p5 → ((p2 ∨ p1) → p2))) → p4) ∨ (((True ∨ (True ∨ p4)) → p2) ∧ (p5 ∧ p4))) ∨ ((True ∨ (False → (p1 ∧ p3))) ∨ p2)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_354756307351985658793184179077 : (p5 → ((((((p3 → (False → p5)) → p3) ∧ p5) ∧ ((p2 → p1) ∨ (p2 ∧ False))) ∨ ((p4 ∨ ((p5 ∨ p5) ∨ (True ∨ p3))) ∨ p5)) ∨ p2)) := by
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
theorem thm_5_vars_246564909342374538970401231096 : ((p5 ∧ p2) ∨ (((p2 → p1) ∧ ((p1 ∧ (((((((False ∧ (p4 ∨ p2)) ∧ (p4 → p5)) → True) ∨ False) → p1) → p5) ∨ p1)) ∧ True)) → p1)) := by
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
  -- Conjunctions on the left can always be decomposed.
  let h6 := h4.left
  let h7 := h4.right
  -- Disjunctions on the left can always be decomposed.
  cases h7
  case inl h8 =>
    -- One of the premise coincides with the conclusion.
    exact h6
  case inr h9 =>
    -- One of the premise coincides with the conclusion.
    exact h9



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_257585617966724224996426998367 : ((p3 ∨ p1) → ((p2 → p3) → (((((((p3 ∨ p3) ∨ (p3 → (p2 ∨ False))) ∨ p3) ∧ p3) ∧ False) ∨ p1) ∨ (((p1 ∨ False) ∨ True) ∨ p4)))) := by
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
    -- True on the right can always be proven directly.
    apply True.intro
  case inr h4 =>
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h4



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_22055088126638706945854779416 : (((((((p5 → p2) ∨ p3) ∧ False) ∧ p2) ∨ p4) ∨ ((p2 → p5) ∨ ((True → p3) ∨ (((((p2 ∨ True) ∨ True) ∨ False) ∧ p2) → p2)))) ∧ True) := by
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
        -- One of the premise coincides with the conclusion.
        exact h3
      case inr h7 =>
        -- One of the premise coincides with the conclusion.
        exact h3
    case inr h8 =>
      -- One of the premise coincides with the conclusion.
      exact h3
  case inr h9 =>
    -- False on the left can always be used.
    apply False.elim h9
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_32568702852712461948733778936 : ((p2 ∨ (((True ∧ (p5 ∧ p2)) ∧ (p2 ∨ (p3 ∨ ((p3 ∨ p5) → (p3 ∨ p2))))) ∨ (p2 ∨ (p5 → (p1 → ((p1 → p1) ∨ False)))))) ∧ True) := by
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
  -- Implications on the right can always be decomposed.
  intro h2
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h3
  -- One of the premise coincides with the conclusion.
  exact h3
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_58136261273574254295960421182 : (((p2 ∧ p2) ∧ ((((p4 → (((((((p4 → (p4 ∨ True)) ∨ False) ∨ (False ∧ p2)) ∧ True) → p1) ∧ p2) ∨ p2)) → True) ∨ p5) → p4)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_190767767912175390700839949137 : (((((p3 → p4) ∨ (p5 ∨ True)) ∧ p1) ∨ (p1 ∧ p5)) ∨ (p3 → ((((((p5 → False) → False) → True) ∧ (p3 ∧ p4)) ∨ p2) ∨ (False → p4)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h2
  -- False on the left can always be used.
  apply False.elim h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_206506599975563313177017055413 : ((p5 ∨ (p3 ∧ ((p3 ∧ p2) ∧ p3))) ∨ (p1 → (False → ((p1 ∧ ((p2 ∧ p4) ∨ ((p4 ∨ ((p1 ∧ p5) ∧ (p3 ∨ p5))) ∧ p3))) → False)))) := by
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
    -- Conjunctions on the left can always be decomposed.
    let h7 := h6.left
    let h8 := h6.right
    -- False on the left can always be used.
    apply False.elim h2
  case inr h9 =>
    -- Conjunctions on the left can always be decomposed.
    let h10 := h9.left
    let h11 := h9.right
    -- Disjunctions on the left can always be decomposed.
    cases h10
    case inl h12 =>
      -- False on the left can always be used.
      apply False.elim h2
    case inr h13 =>
      -- Conjunctions on the left can always be decomposed.
      let h14 := h13.left
      let h15 := h13.right
      -- Conjunctions on the left can always be decomposed.
      let h16 := h14.left
      let h17 := h14.right
      -- Disjunctions on the left can always be decomposed.
      cases h15
      case inl h18 =>
        -- False on the left can always be used.
        apply False.elim h2
      case inr h19 =>
        -- False on the left can always be used.
        apply False.elim h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_197664557098461916747733775358 : ((((True → False) ∨ (p5 → True)) → (p1 ∨ p2)) ∨ (p3 ∨ (p3 → (((p3 ∧ (((False → p5) → ((p2 ∧ p4) → p3)) → p3)) ∧ p3) ∨ p3)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_699318203735089070435152713311 : ((((((p5 → ((p4 ∧ (p2 → p2)) ∧ False)) ∧ (False ∨ p3)) ∧ p5) → ((p1 ∧ (p4 → p5)) ∧ (((p4 ∧ (p3 → p3)) ∧ p5) ∧ False))) ∨ p4) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- Conjunctions on the left can always be decomposed.
  let h4 := h2.left
  let h5 := h2.right
  -- Disjunctions on the left can always be decomposed.
  cases h5
  case inl h6 =>
    -- False on the left can always be used.
    apply False.elim h6
  case inr h7 =>
    -- We want to use the implication h4 based on <expert-advice>. So we show its premise.
    have h8 : p5 := by
      -- One of the premise coincides with the conclusion.
      exact h3
    -- We have shown the premise of h4, we can now drive its conclusion.
    let h9 := h4 h8
    -- We need to get the right conjuct of h9 based on <expert-advice>.
    let h10 := h9.right
    -- False on the left can always be used.
    apply False.elim h10
  -- Implications on the right can always be decomposed.
  intro h11
  -- Conjunctions on the left can always be decomposed.
  let h12 := h1.left
  let h13 := h1.right
  -- Conjunctions on the left can always be decomposed.
  let h14 := h12.left
  let h15 := h12.right
  -- Disjunctions on the left can always be decomposed.
  cases h15
  case inl h16 =>
    -- False on the left can always be used.
    apply False.elim h16
  case inr h17 =>
    -- One of the premise coincides with the conclusion.
    exact h13
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Conjunctions on the left can always be decomposed.
  let h18 := h1.left
  let h19 := h1.right
  -- Conjunctions on the left can always be decomposed.
  let h20 := h18.left
  let h21 := h18.right
  -- Disjunctions on the left can always be decomposed.
  cases h21
  case inl h22 =>
    -- False on the left can always be used.
    apply False.elim h22
  case inr h23 =>
    -- We want to use the implication h20 based on <expert-advice>. So we show its premise.
    have h24 : p5 := by
      -- One of the premise coincides with the conclusion.
      exact h19
    -- We have shown the premise of h20, we can now drive its conclusion.
    let h25 := h20 h24
    -- We need to get the left conjuct of h25 based on <expert-advice>.
    let h26 := h25.left
    -- We need to get the left conjuct of h26 based on <expert-advice>.
    let h27 := h26.left
    -- One of the premise coincides with the conclusion.
    exact h27
  -- Implications on the right can always be decomposed.
  intro h28
  -- Conjunctions on the left can always be decomposed.
  let h29 := h1.left
  let h30 := h1.right
  -- Conjunctions on the left can always be decomposed.
  let h31 := h29.left
  let h32 := h29.right
  -- Disjunctions on the left can always be decomposed.
  cases h32
  case inl h33 =>
    -- False on the left can always be used.
    apply False.elim h33
  case inr h34 =>
    -- One of the premise coincides with the conclusion.
    exact h34
  -- Conjunctions on the left can always be decomposed.
  let h35 := h1.left
  let h36 := h1.right
  -- Conjunctions on the left can always be decomposed.
  let h37 := h35.left
  let h38 := h35.right
  -- Disjunctions on the left can always be decomposed.
  cases h38
  case inl h39 =>
    -- False on the left can always be used.
    apply False.elim h39
  case inr h40 =>
    -- One of the premise coincides with the conclusion.
    exact h36
  -- Conjunctions on the left can always be decomposed.
  let h41 := h1.left
  let h42 := h1.right
  -- Conjunctions on the left can always be decomposed.
  let h43 := h41.left
  let h44 := h41.right
  -- Disjunctions on the left can always be decomposed.
  cases h44
  case inl h45 =>
    -- False on the left can always be used.
    apply False.elim h45
  case inr h46 =>
    -- We want to use the implication h43 based on <expert-advice>. So we show its premise.
    have h47 : p5 := by
      -- One of the premise coincides with the conclusion.
      exact h42
    -- We have shown the premise of h43, we can now drive its conclusion.
    let h48 := h43 h47
    -- We need to get the right conjuct of h48 based on <expert-advice>.
    let h49 := h48.right
    -- False on the left can always be used.
    apply False.elim h49
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_799766747109757399013988475620 : (((p1 → (p2 → ((p3 ∨ (((p3 ∨ (((p4 → (True → p4)) ∨ False) ∧ p5)) ∨ p3) ∧ (True → (p1 ∧ (False ∨ p3))))) ∨ (p3 ∨ p1)))) ∨ p3) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_320490207655777838475973868140 : (p4 ∨ ((p4 → p5) → (p4 ∨ (True ∧ ((((p5 → (p1 ∧ p3)) ∧ p1) ∧ ((p5 ∨ (p1 ∨ (p4 ∧ (p5 ∨ True)))) → False)) → (False ∨ False)))))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- Implications on the right can always be decomposed.
  intro h2
  -- Conjunctions on the left can always be decomposed.
  let h3 := h2.left
  let h4 := h2.right
  -- Conjunctions on the left can always be decomposed.
  let h5 := h3.left
  let h6 := h3.right
  -- We want to use the implication h4 based on <expert-advice>. So we show its premise.
  have h7 : (p5 ∨ (p1 ∨ (p4 ∧ (p5 ∨ True)))) := by
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- One of the premise coincides with the conclusion.
    exact h6
  -- We have shown the premise of h4, we can now drive its conclusion.
  let h8 := h4 h7
  -- False on the left can always be used.
  apply False.elim h8



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_52786367955631209854873707289 : ((((((p5 → (p4 ∧ p1)) ∨ (p3 ∧ (True ∧ p3))) ∨ True) → (p3 ∨ p4)) → ((p1 → p3) ∨ ((p4 → (p4 ∧ p4)) ∨ (p1 ∧ p3)))) ∨ p3) := by
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
  -- One of the premise coincides with the conclusion.
  exact h2
  -- One of the premise coincides with the conclusion.
  exact h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_312411980531182337704575300486 : (p2 ∨ (p4 → ((((p2 → ((True → p5) ∨ ((True ∨ False) ∨ (p4 ∧ p4)))) → p2) ∨ (p3 → (((p3 → (p5 ∧ p3)) ∨ p1) → True))) ∨ p1))) := by
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
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_742478806205968084997276659147 : ((((p2 → False) ∨ (((p4 → (p1 ∨ (((p4 ∨ (((p4 ∨ False) → p5) → p4)) ∨ (p3 → p4)) ∧ ((True → p3) ∨ p5)))) ∨ p3) ∨ p1)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_355217437749935393718954373724 : (p5 → (((p5 → (((p5 ∧ p5) ∨ p1) ∧ p1)) ∧ ((p1 ∨ p1) → ((((p1 ∧ p1) ∨ p2) ∨ (p4 ∨ p3)) ∨ ((p2 ∨ p1) ∨ p4)))) → p1)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Conjunctions on the left can always be decomposed.
  let h3 := h2.left
  let h4 := h2.right
  -- We want to use the implication h3 based on <expert-advice>. So we show its premise.
  have h5 : p5 := by
    -- One of the premise coincides with the conclusion.
    exact h1
  -- We have shown the premise of h3, we can now drive its conclusion.
  let h6 := h3 h5
  -- We need to get the right conjuct of h6 based on <expert-advice>.
  let h7 := h6.right
  -- One of the premise coincides with the conclusion.
  exact h7



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_115971974887406653788613107049 : ((((False ∨ (p5 → p5)) ∧ p4) → (p5 ∨ ((p1 → (((p5 → (p4 ∧ ((p3 ∧ p4) ∧ False))) ∧ p1) → p5)) ∨ (p1 → p1)))) ∨ (p2 ∧ p5)) := by
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
    -- False on the left can always be used.
    apply False.elim h4
  case inr h5 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h6
    -- One of the premise coincides with the conclusion.
    exact h6



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_683601259908153879546135206129 : (((((((p3 → True) → ((p1 ∨ ((p3 ∨ (p3 ∧ (p4 ∧ p2))) ∨ p4)) ∧ p3)) → p3) ∧ p1) ∨ (p5 → (((False ∨ p4) ∨ p5) ∧ p5))) ∨ p5) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h1
  -- One of the premise coincides with the conclusion.
  exact h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_337594671330503655133518619121 : (p1 → (((p5 ∨ True) → (((p2 ∧ ((False → p4) → (p1 ∧ p4))) → ((p1 ∨ (p5 ∧ False)) → p3)) ∧ False)) → (p2 ∧ ((p3 → p5) → p3)))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
  have h3 : (p5 ∨ True) := by
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h2, we can now drive its conclusion.
  let h4 := h2 h3
  -- We need to get the right conjuct of h4 based on <expert-advice>.
  let h5 := h4.right
  -- False on the left can always be used.
  apply False.elim h5
  -- Implications on the right can always be decomposed.
  intro h6
  -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
  have h7 : (p5 ∨ True) := by
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h2, we can now drive its conclusion.
  let h8 := h2 h7
  -- We need to get the right conjuct of h8 based on <expert-advice>.
  let h9 := h8.right
  -- False on the left can always be used.
  apply False.elim h9



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_112566379399037974239437010081 : ((((True ∨ (((((p4 ∨ (p3 ∧ p1)) ∧ (p1 → p2)) ∨ p4) → ((p4 ∨ p1) → True)) → ((True → p4) → p3))) → p2) → False) ∨ (False ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_9447049222262431100823449843 : ((((p5 → (True ∨ (p1 → p2))) → ((p4 ∧ ((p1 ∧ p5) ∨ ((p1 → ((p5 ∨ (p4 → p1)) ∨ False)) → (p3 ∧ False)))) ∨ p4)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_677796740810340167258869952213 : (((((p5 → ((p3 ∧ ((((p3 → p1) ∧ (p5 ∨ p1)) ∧ p3) → True)) ∧ (True ∨ (p4 → p1)))) → p1) ∨ ((p2 ∨ True) ∨ (True → p1))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_303003899674577849479927195780 : (False ∨ (p1 → ((True ∧ (p3 → (((p4 → False) → (p3 ∧ p2)) → (p5 ∧ (False ∧ p1))))) ∨ ((False ∧ p5) → ((p3 ∧ (p2 ∧ p5)) → p2))))) := by
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
  -- Conjunctions on the left can always be decomposed.
  let h4 := h3.left
  let h5 := h3.right
  -- Conjunctions on the left can always be decomposed.
  let h6 := h5.left
  let h7 := h5.right
  -- Conjunctions on the left can always be decomposed.
  let h8 := h2.left
  let h9 := h2.right
  -- False on the left can always be used.
  apply False.elim h8



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_227300571805827772630577381983 : (((p2 → False) → p1) ∨ (((((p1 ∨ p5) → p4) ∨ (p2 ∧ False)) ∨ (p3 ∨ ((p4 ∨ p2) ∨ (True ∨ p1)))) ∨ (p4 ∨ ((p5 → p3) ∨ p2)))) := by
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
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_140353702556094071899175591988 : (((((False → (((p1 ∨ p2) ∨ (p4 → p4)) ∧ (p5 → p3))) ∨ p5) ∧ ((p2 ∧ p1) ∧ p2)) ∨ (p2 ∨ (True ∧ p5))) → (p3 → (p5 ∨ p3))) := by
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
    -- Disjunctions on the left can always be decomposed.
    cases h4
    case inl h6 =>
      -- Conjunctions on the left can always be decomposed.
      let h7 := h5.left
      let h8 := h5.right
      -- Conjunctions on the left can always be decomposed.
      let h9 := h7.left
      let h10 := h7.right
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- One of the premise coincides with the conclusion.
      exact h2
    case inr h11 =>
      -- Conjunctions on the left can always be decomposed.
      let h12 := h5.left
      let h13 := h5.right
      -- Conjunctions on the left can always be decomposed.
      let h14 := h12.left
      let h15 := h12.right
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- One of the premise coincides with the conclusion.
      exact h11
  case inr h16 =>
    -- Disjunctions on the left can always be decomposed.
    cases h16
    case inl h17 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- One of the premise coincides with the conclusion.
      exact h2
    case inr h18 =>
      -- Conjunctions on the left can always be decomposed.
      let h19 := h18.left
      let h20 := h18.right
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- One of the premise coincides with the conclusion.
      exact h20



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_129111835697365831328161697652 : (((((False ∧ (True ∧ (((((((True ∨ p2) ∨ True) ∨ p1) ∨ True) → (p1 ∨ p4)) ∧ False) ∨ p2))) → p1) → p5) ∨ True) ∧ (p1 → (p3 ∨ True))) := by
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
theorem thm_5_vars_177869043460212129191113878707 : ((((p5 ∨ (False ∧ ((p3 ∧ False) ∨ ((p4 ∨ True) ∧ p2)))) ∨ p1) ∨ True) ∨ (False ∧ (((p2 → (((p2 → p4) ∧ p3) ∧ p2)) ∧ p1) ∨ True))) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_783280909721242457769227698673 : (((p3 ∨ ((((p1 ∧ (((p2 ∧ p2) → p1) ∧ ((p3 ∨ p2) ∧ p3))) ∧ (p2 → (False ∧ p2))) ∨ p5) ∨ ((p5 ∨ False) → (p4 ∨ True)))) ∨ False) ∧ True) := by
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
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h2 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro
  case inr h3 =>
    -- False on the left can always be used.
    apply False.elim h3
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_452701410584792442716866044129 : ((((True → ((((p4 → (False → p2)) ∨ p2) ∧ (p2 ∧ p3)) ∨ ((p2 ∨ (p2 → p2)) → (p1 ∨ p1)))) ∨ (p2 → ((p1 ∧ False) → p4))) ∧ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
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
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_147917977672969123615937983433 : (((((p4 ∨ p1) ∧ (True → (((False ∧ (True ∨ p5)) → True) ∧ p5))) ∧ ((True → p2) → p4)) ∧ (p1 ∨ p3)) ∨ (False → ((True ∨ p5) → True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_59283438976585785248175038688 : (((p3 ∨ p3) ∨ ((((((p3 ∧ (False → p1)) → False) ∧ p1) ∨ ((True → (True ∨ p3)) ∧ (p2 ∨ (p3 → (p1 → p3))))) → False) → p4)) ∨ p5) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h2 : ((((p3 ∧ (False → p1)) → False) ∧ p1) ∨ ((True → (True ∨ p3)) ∧ (p2 ∨ (p3 → (p1 → p3))))) := by
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Conjunctions on the right can always be decomposed.
    apply And.intro
    -- Implications on the right can always be decomposed.
    intro h3
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- True on the right can always be proven directly.
    apply True.intro
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h4
    -- Implications on the right can always be decomposed.
    intro h5
    -- One of the premise coincides with the conclusion.
    exact h4
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h6 := h1 h2
  -- False on the left can always be used.
  apply False.elim h6



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_51936182766497615884037599502 : (((((p5 → p3) ∨ ((p3 ∨ (p1 ∨ p2)) ∧ True)) ∧ (p1 → (True ∨ (p3 ∧ p4)))) ∨ ((((False → True) ∨ False) → p1) ∨ (p2 ∨ True))) ∨ p5) := by
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
theorem thm_5_vars_658186281983220750168414261361 : ((((p4 ∧ (p1 → (((p3 → p5) ∧ ((p1 ∧ False) ∧ p1)) ∨ ((p2 ∧ (p4 ∨ (p1 → ((p5 ∨ False) ∧ p4)))) ∧ p3)))) ∨ (False → False)) ∨ p4) ∧ True) := by
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
theorem thm_5_vars_775332946845416621695511361240 : (((False ∨ (False ∧ (((True ∨ (((((True → True) ∧ True) ∨ True) ∨ False) ∧ p1)) ∧ (((True ∧ p3) ∧ p3) → False)) ∨ ((p1 ∧ True) ∧ p2)))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_722229866381411784731280780380 : ((((p5 → (True ∨ (True ∨ p1))) → ((p1 → ((p1 → (p3 ∧ p5)) ∨ ((p1 → p5) ∨ p2))) ∧ ((((p4 ∧ p2) → p4) ∧ p1) ∧ False))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_114100840650203924726087417434 : (((p2 ∧ ((p2 → p3) → ((p5 → (False → (((p2 ∧ ((p3 ∨ p4) ∨ False)) ∧ p1) ∨ p4))) → p1))) ∨ (p5 ∧ (False ∧ p1))) ∨ (p4 ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_117172046834268963917599372470 : ((True ∧ ((((p3 ∨ p4) ∧ p4) ∨ (((p4 ∨ p4) → p4) → (((((p2 ∧ p3) ∧ p5) → p1) ∨ (p3 ∨ p5)) → p4))) → p3)) ∨ (False → p1)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_116312484953451769326441369390 : (((p4 → (p2 ∧ p4)) ∨ (((p4 → True) ∨ (p5 ∧ (p2 ∧ ((p4 ∧ (False ∧ p3)) → True)))) → (p2 → (p2 ∨ (False ∨ p1))))) ∨ (False ∨ p5)) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h3 =>
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- One of the premise coincides with the conclusion.
    exact h2
  case inr h4 =>
    -- Conjunctions on the left can always be decomposed.
    let h5 := h4.left
    let h6 := h4.right
    -- Conjunctions on the left can always be decomposed.
    let h7 := h6.left
    let h8 := h6.right
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- One of the premise coincides with the conclusion.
    exact h7



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_190100514209120159285076580198 : (((((p2 → (p1 ∧ p2)) ∧ p5) → (p5 ∧ p2)) ∧ p1) ∨ (p5 → (((p3 ∨ (p1 ∧ ((False → False) ∧ p4))) → ((p2 ∨ p5) ∨ p2)) ∨ p4))) := by
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
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h1
  case inr h4 =>
    -- Conjunctions on the left can always be decomposed.
    let h5 := h4.left
    let h6 := h4.right
    -- Conjunctions on the left can always be decomposed.
    let h7 := h6.left
    let h8 := h6.right
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_218829432547586631445162512041 : ((p2 ∧ ((p1 → p2) ∧ p3)) → (((True ∨ (p4 ∧ ((p2 ∧ (p3 ∧ p1)) ∧ True))) ∨ ((p2 ∨ p2) → (p1 ∧ p5))) → (False ∨ (p5 ∨ p2)))) := by
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
      -- Conjunctions on the left can always be decomposed.
      let h7 := h6.left
      let h8 := h6.right
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- One of the premise coincides with the conclusion.
      exact h5
    case inr h9 =>
      -- Conjunctions on the left can always be decomposed.
      let h10 := h9.left
      let h11 := h9.right
      -- Conjunctions on the left can always be decomposed.
      let h12 := h11.left
      let h13 := h11.right
      -- Conjunctions on the left can always be decomposed.
      let h14 := h12.left
      let h15 := h12.right
      -- Conjunctions on the left can always be decomposed.
      let h16 := h15.left
      let h17 := h15.right
      -- Conjunctions on the left can always be decomposed.
      let h18 := h1.left
      let h19 := h1.right
      -- Conjunctions on the left can always be decomposed.
      let h20 := h19.left
      let h21 := h19.right
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- One of the premise coincides with the conclusion.
      exact h18
  case inr h22 =>
    -- Conjunctions on the left can always be decomposed.
    let h23 := h1.left
    let h24 := h1.right
    -- Conjunctions on the left can always be decomposed.
    let h25 := h24.left
    let h26 := h24.right
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h23



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_53232532396916432612104121199 : ((((p5 → (p1 ∨ (p2 ∧ p2))) → ((p2 → p5) ∨ (p3 ∧ False))) ∨ (True ∨ ((p4 ∧ ((p1 → p5) ∨ ((p4 ∨ True) ∨ p2))) → p3))) ∨ p3) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_215101493292931917365705555306 : (((p1 → p2) → (p1 → False)) ∨ ((((True → (((p5 → ((p4 ∨ True) → p4)) → p2) → ((p4 ∨ p5) ∧ (p4 ∨ True)))) ∨ p3) ∨ True) ∧ True)) := by
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
theorem thm_5_vars_218582719286323829345836657457 : (((p2 → p1) → (p2 → True)) → ((((p3 → ((False → False) ∨ False)) → ((((p4 → False) → True) ∨ False) ∨ (p3 ∧ p1))) → (p5 → p1)) ∨ True)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_687352101994844904672711498639 : (((((p3 ∨ (((p4 ∨ p2) → ((p4 → False) ∨ p1)) ∨ (p5 → (p4 ∧ p1)))) ∧ p3) ∧ ((True → ((p3 ∨ (p5 ∨ True)) → False)) ∨ p5)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_191582111458157103846198604815 : ((p2 ∧ ((p2 ∨ p5) ∧ (((p5 → p5) → p5) ∨ p1))) ∨ (True ∨ (True ∨ ((((False ∨ (p5 ∧ (p2 ∧ p5))) ∨ (True → True)) ∧ False) ∨ p1)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_158995760931843574261864355101 : ((p3 ∨ (False ∨ ((p4 → ((((p2 ∧ True) ∧ False) ∧ (p2 ∨ (p4 → True))) → True)) → (p4 ∨ p5)))) ∨ (p2 → (p2 → ((True → p3) ∨ p2)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_325707093207399672522065528546 : (p5 ∨ (p1 ∨ ((p3 ∨ p1) ∨ ((False ∨ (((p3 ∨ (p1 ∨ True)) ∨ (True ∨ (p1 ∧ (p5 → p4)))) ∨ (True ∨ (p5 ∨ (p1 ∧ p3))))) ∨ False)))) := by
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
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_749240785557938958123653425024 : ((((p5 → p3) → (p5 ∨ ((p2 → (p3 ∨ (p1 ∨ p1))) ∨ ((((p4 → (((p4 → p1) ∧ (p1 ∧ p4)) ∧ p4)) ∧ True) ∧ p5) ∧ p5)))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_799875595385798980628476548890 : (((p1 → (p5 → (((((((True ∧ p4) → True) → p5) → ((p3 ∨ (((False ∨ p5) ∧ (p3 → p4)) → True)) → p3)) ∨ p3) ∧ p5) ∨ True))) ∨ p5) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_319067248315944705691911067055 : (p4 ∨ ((p2 → ((((p2 ∧ p4) ∧ (p4 ∨ ((p1 → (False ∨ p1)) → p2))) ∨ (p4 ∨ True)) ∧ (p4 ∧ p1))) ∨ (True ∨ ((True ∨ p4) ∧ False)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_233875289736809130830427008309 : ((p4 ∨ (False ∨ p3)) → ((((((p1 ∧ ((((p3 ∨ p5) ∨ p2) ∧ (p5 → (True ∧ p4))) ∧ p1)) → False) ∨ p5) ∧ True) ∨ (p4 ∨ p3)) ∧ True)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
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
    -- Disjunctions on the left can always be decomposed.
    cases h3
    case inl h4 =>
      -- False on the left can always be used.
      apply False.elim h4
    case inr h5 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- One of the premise coincides with the conclusion.
      exact h5
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_353667753363440778795885995561 : (p4 → (p5 ∨ (((False → (p5 ∧ p2)) → (p4 ∧ ((p3 ∨ ((p3 ∧ (((p5 ∧ (p3 ∧ p2)) ∧ p3) ∧ False)) → True)) ∧ p3))) → (p3 ∨ p1)))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h2
  -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
  have h3 : (False → (p5 ∧ p2)) := by
    -- Implications on the right can always be decomposed.
    intro h4
    -- Conjunctions on the right can always be decomposed.
    apply And.intro
    -- False on the left can always be used.
    apply False.elim h4
    -- False on the left can always be used.
    apply False.elim h4
  -- We have shown the premise of h2, we can now drive its conclusion.
  let h5 := h2 h3
  -- We need to get the right conjuct of h5 based on <expert-advice>.
  let h6 := h5.right
  -- We need to get the right conjuct of h6 based on <expert-advice>.
  let h7 := h6.right
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- One of the premise coincides with the conclusion.
  exact h7



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_117883694974374072059135994359 : ((p5 ∧ ((p4 ∨ (False → (True → (((p4 ∨ ((p3 → True) ∧ ((False ∨ p1) ∧ (False ∧ p4)))) → (True → p2)) ∨ p4)))) → p4)) ∨ (True ∨ p2)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_54390941163690312676238096066 : (((p5 → (p4 → ((p3 ∨ (p3 ∨ True)) → p5))) ∧ ((((p1 ∧ ((False → ((p1 → False) ∨ p5)) ∨ p1)) → (p4 ∧ p1)) ∨ p4) ∨ p3)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_61542388834444226715538335531 : ((p1 ∧ ((p4 ∨ ((p4 ∨ p1) ∧ (p2 ∧ (((True → False) ∨ p2) → p4)))) → (((p2 → False) ∧ (((p2 → p2) → p2) ∨ True)) ∧ p5))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_303222840969241379208396248021 : (False ∨ (p5 → ((p5 ∧ ((((p3 → p5) → p4) ∧ (p2 ∧ ((p1 → (p1 ∧ (((p1 ∧ p1) ∧ p2) → True))) ∨ (p2 → True)))) → p4)) ∧ True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- One of the premise coincides with the conclusion.
  exact h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Conjunctions on the left can always be decomposed.
  let h3 := h2.left
  let h4 := h2.right
  -- Conjunctions on the left can always be decomposed.
  let h5 := h4.left
  let h6 := h4.right
  -- Disjunctions on the left can always be decomposed.
  cases h6
  case inl h7 =>
    -- We want to use the implication h3 based on <expert-advice>. So we show its premise.
    have h8 : (p3 → p5) := by
      -- Implications on the right can always be decomposed.
      intro h9
      -- One of the premise coincides with the conclusion.
      exact h1
    -- We have shown the premise of h3, we can now drive its conclusion.
    let h10 := h3 h8
    -- One of the premise coincides with the conclusion.
    exact h10
  case inr h11 =>
    -- We want to use the implication h3 based on <expert-advice>. So we show its premise.
    have h12 : (p3 → p5) := by
      -- Implications on the right can always be decomposed.
      intro h13
      -- One of the premise coincides with the conclusion.
      exact h1
    -- We have shown the premise of h3, we can now drive its conclusion.
    let h14 := h3 h12
    -- One of the premise coincides with the conclusion.
    exact h14
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_747785123772441196568096877200 : ((((False → p1) → (True → (p3 → ((((p1 → ((p4 ∧ p2) → (False ∧ p4))) ∨ (True → ((p4 ∨ p4) ∨ (True ∨ p3)))) ∨ p1) ∨ p5)))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_174364805157835308668202682252 : (((p4 ∨ ((False ∧ (((False ∧ True) ∨ p2) ∧ p4)) ∨ True)) → (p5 ∧ (True ∧ p2))) → ((p5 ∨ ((p3 ∨ (p4 → p5)) ∨ p1)) ∨ (False ∧ p1))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h2 : (p4 ∨ ((False ∧ (((False ∧ True) ∨ p2) ∧ p4)) ∨ True)) := by
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h3 := h1 h2
  -- We need to get the left conjuct of h3 based on <expert-advice>.
  let h4 := h3.left
  -- One of the premise coincides with the conclusion.
  exact h4



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_41298010454201367743391643175 : ((((True ∨ ((p1 → ((p3 ∨ (p1 → (((p1 → p2) → False) ∧ (p2 ∨ True)))) ∨ p1)) ∧ p5)) → (p1 ∨ (p4 ∧ (p5 ∧ p4)))) ∨ True) ∨ p4) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_259283576838017648510092000425 : ((False → p1) → ((p4 ∧ p3) ∨ ((True ∧ (True ∨ p4)) ∧ ((((p3 ∨ ((((p5 → False) ∧ p1) → p5) ∨ p4)) → p1) ∧ False) ∨ (True → True))))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h2
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_340786767310942563215657295204 : (p2 → ((((p1 → ((p1 ∧ (((p3 ∨ p1) → True) ∨ True)) ∧ p2)) ∧ ((True ∧ ((True → p1) → (p5 → p3))) → (p4 → p5))) → p3) ∨ p2)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_430238934560990576287641342891 : ((((((((p4 ∨ True) ∨ True) ∨ p1) ∧ True) → ((((p5 → p1) ∨ ((p4 → p1) ∨ (p2 → p3))) ∧ p5) ∨ (p1 → p4))) ∨ (p3 ∨ True)) ∧ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
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
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_727385536482336413841945677745 : ((((p2 ∧ (p5 ∨ p2)) ∨ (((p3 ∧ p2) ∧ p2) ∨ ((((p2 ∧ ((p4 ∨ (True ∨ p1)) → p5)) ∧ p3) ∨ ((True → False) ∨ p3)) → False))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_172106462166341436714231987568 : (((False → ((False ∨ p4) → (((p1 ∨ p3) ∧ p3) → (p2 ∨ p2)))) → (p5 ∧ p1)) ∨ ((p4 ∧ (p4 → p5)) ∨ (False ∨ ((False → p2) → True)))) := by
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
theorem thm_5_vars_166336832854898905339108733361 : ((p5 ∧ (p4 ∨ ((((((p5 ∨ False) → (True → p4)) → p2) ∨ (p2 → False)) → p3) ∨ p4))) ∨ ((True ∧ ((p2 ∧ False) ∨ p3)) → (False → p1))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- False on the left can always be used.
  apply False.elim h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_612454477096044418905458885545 : ((((((((p3 ∧ p3) → (p5 → ((False ∧ p4) → (False ∧ ((p4 → ((p5 ∧ False) → p1)) ∧ p4))))) → p4) ∧ p4) ∨ (p1 ∧ True)) ∨ True) ∨ p3) ∧ True) := by
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
theorem thm_5_vars_318643875988785375045976570485 : (p4 ∨ ((p2 ∨ (p2 → (False ∧ ((p1 → (((p4 → (p5 ∨ p5)) → ((p1 ∧ False) → p5)) ∧ (p5 → p3))) → (p3 ∨ False))))) ∨ (p5 → p5))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_147590305216220143359563747031 : ((((((p3 → (((p2 ∧ p4) ∨ (p2 → (p5 ∨ True))) → p1)) ∧ ((True → p2) ∨ True)) ∨ p5) ∨ p5) → False) ∨ (((True ∨ True) ∧ False) → p2)) := by
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
    -- False on the left can always be used.
    apply False.elim h3
  case inr h5 =>
    -- False on the left can always be used.
    apply False.elim h3



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_173642700363616213004490966211 : (((p5 → ((p4 → (((p2 → p2) ∧ (p3 ∨ p5)) ∧ p3)) ∨ (False ∨ p2))) ∧ p3) → (((((False ∧ (p5 → p1)) → False) → False) ∧ p2) → p5)) := by
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
  -- We want to use the implication h3 based on <expert-advice>. So we show its premise.
  have h7 : ((False ∧ (p5 → p1)) → False) := by
    -- Implications on the right can always be decomposed.
    intro h8
    -- Conjunctions on the left can always be decomposed.
    let h9 := h8.left
    let h10 := h8.right
    -- False on the left can always be used.
    apply False.elim h9
  -- We have shown the premise of h3, we can now drive its conclusion.
  let h11 := h3 h7
  -- False on the left can always be used.
  apply False.elim h11



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_174212115155093858231704679063 : ((((((p2 ∧ ((p2 ∨ p2) → True)) ∧ p3) ∧ p4) ∨ (False ∨ True)) → (p2 ∧ p5)) → (p5 ∧ ((p4 → (p4 → p2)) → ((p1 → p5) ∧ True)))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h2 : ((((p2 ∧ ((p2 ∨ p2) → True)) ∧ p3) ∧ p4) ∨ (False ∨ True)) := by
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
  -- One of the premise coincides with the conclusion.
  exact h4
  -- Implications on the right can always be decomposed.
  intro h5
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h6
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h7 : ((((p2 ∧ ((p2 ∨ p2) → True)) ∧ p3) ∧ p4) ∨ (False ∨ True)) := by
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h8 := h1 h7
  -- We need to get the right conjuct of h8 based on <expert-advice>.
  let h9 := h8.right
  -- One of the premise coincides with the conclusion.
  exact h9
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_592712750453622465551030816131 : ((((((p1 ∧ ((True → ((p2 → p5) ∧ ((False → (p3 ∨ True)) ∧ (p2 ∧ (p4 ∨ p4))))) ∧ p3)) ∧ p5) ∧ (False ∧ (False ∨ p4))) ∧ p1) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_148814041574337108005773069529 : ((((p1 → p3) ∧ (p2 ∧ (p1 → p1))) → (((p4 ∧ p4) ∨ False) ∨ ((True → p1) ∨ (p3 ∨ (p1 → p4))))) ∨ ((p4 ∨ (False → False)) → True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_98916628086956098253966585672 : ((True → ((((p2 ∧ ((p5 ∨ (True → p2)) ∧ p1)) ∧ p4) → ((p3 ∧ (p5 ∨ (p3 → ((p3 ∧ p4) → p1)))) → False)) ∧ (p4 ∧ False))) → False) := by
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
  -- False on the left can always be used.
  apply False.elim h5



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_762509989633834542566514109866 : (((p3 ∧ (((((False → False) → (p3 → p3)) ∧ (p1 ∧ ((False ∧ (p3 ∨ p4)) ∧ p2))) ∧ True) ∧ ((p1 → (p2 ∧ (p2 ∨ True))) ∧ p3))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_137774279498003353268677398858 : ((p2 ∨ ((((p4 ∨ p1) → ((False → p1) → p1)) → (p5 ∨ p2)) ∨ (p4 → (p4 ∨ ((p3 ∧ (p2 ∨ p3)) ∨ p2))))) ∨ (False → (p2 → p2))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_352102502570353184424027298907 : (p4 → (((True → (p4 ∧ (p1 ∧ p1))) → False) ∨ (((((True ∧ (p1 ∨ (p3 ∨ False))) ∧ p1) ∧ p1) → (((p5 ∨ p3) ∧ False) ∨ True)) ∨ False))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h2
  -- Conjunctions on the left can always be decomposed.
  let h3 := h2.left
  let h4 := h2.right
  -- Conjunctions on the left can always be decomposed.
  let h5 := h3.left
  let h6 := h3.right
  -- Conjunctions on the left can always be decomposed.
  let h7 := h5.left
  let h8 := h5.right
  -- Disjunctions on the left can always be decomposed.
  cases h8
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
      -- False on the left can always be used.
      apply False.elim h12



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_338582795357304349271975987011 : (p1 → (((True ∨ p4) ∨ True) → ((((((p3 ∧ False) → (p2 → ((p5 → True) ∧ False))) ∧ (False ∧ p4)) ∨ p1) ∧ ((True ∧ False) ∨ p1)) ∨ p5))) := by
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
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
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
    case inr h5 =>
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
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
  case inr h6 =>
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
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
theorem thm_5_vars_119362704521672566914803558029 : ((p3 → (p4 ∧ (((p2 → p3) ∧ p2) ∨ (((p2 ∨ (p3 ∧ ((True → p1) ∨ p1))) → ((p1 ∧ p3) ∨ (p5 ∨ False))) → p5)))) ∨ (p4 ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_37787948902919921994020968935 : (((((p5 → p2) ∨ (p3 ∨ (p3 ∨ (p2 ∧ (((((True ∨ p4) → ((p2 → p4) ∧ p5)) → p5) ∨ p4) ∧ (p5 ∨ False)))))) → p5) ∧ p5) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_114312724805949594288094043383 : (((((p4 ∨ (p2 ∨ False)) ∨ p5) ∧ (((True ∧ True) → (p1 → p1)) ∨ ((p2 ∧ p2) → p2))) ∧ ((p2 ∨ (p3 ∧ p1)) ∧ p2)) ∨ (p4 ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_35972140791336408692691590275 : ((p3 → ((((((False → p3) ∧ ((True → False) ∨ p2)) ∧ p2) → p5) → (p4 ∨ p1)) → ((p1 → True) → ((p4 ∨ (p2 → p5)) ∨ p3)))) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
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
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_157406021221390281071361939778 : (((((p4 → ((p5 ∨ p3) ∧ False)) → ((True → p3) ∨ p4)) ∧ (False ∨ (True ∧ p2))) ∧ (False ∧ False)) ∨ ((((p5 → p3) ∨ p2) ∨ True) ∧ True)) := by
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
theorem thm_5_vars_248000659451814607210176664177 : ((p1 ∨ p4) ∨ (p4 ∨ (((p5 → (p4 ∨ (p1 ∨ p5))) ∨ p3) ∨ ((p2 ∨ (p1 ∨ False)) → (((True ∨ (p1 ∧ True)) ∨ (p1 ∨ p5)) → p5))))) := by
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
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_42532501829328505479118424249 : (((p1 ∨ ((((p4 → (p2 → (((p3 → p3) → (p4 ∧ ((p5 ∨ p4) ∨ p4))) → (True → (p1 ∧ p2))))) ∨ False) ∧ p1) → False)) ∨ True) ∨ p3) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_322495000622142361267741335496 : (p5 ∨ (((p4 ∧ True) → ((p1 ∨ (p3 ∨ (((p1 ∨ True) ∨ True) → (p3 → (((p1 → True) ∨ False) → (False ∧ False)))))) ∨ (p3 ∨ True))) ∨ p3)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_45028799563850841056008236000 : ((((p1 ∨ p5) ∨ (((p2 ∨ (p1 ∨ True)) ∧ p5) ∨ ((False ∧ (((False → True) ∧ p3) ∨ (p4 → (p5 ∧ p5)))) → (p3 ∨ p4)))) → p3) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_117709374089096334027509250406 : ((p3 ∧ (p4 ∧ (((False → p3) ∧ (((True → p1) ∨ False) ∨ p1)) → ((p5 → p3) ∧ ((p5 → (p5 ∨ (p4 → p5))) ∧ p2))))) ∨ (p1 ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



