variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_47343961443007755611452886498 : ((((p5 ∨ p5) ∧ ((((p5 ∨ (p5 ∧ p2)) → p1) → ((p5 ∧ p4) ∨ (((p4 ∨ False) → True) ∧ p4))) ∨ (False ∨ p1))) ∨ (False → False)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_144926481922371177557609634320 : (((p2 ∨ ((p1 ∨ ((p2 ∧ p1) ∧ p1)) ∧ (((p1 ∧ p1) ∧ True) ∨ p2))) ∨ (True ∨ (p4 ∨ (p2 ∧ False)))) ∧ (p2 ∨ (True → (p3 → p3)))) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
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
  -- One of the premise coincides with the conclusion.
  exact h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_669259634877965555423864003146 : (((((p5 ∨ ((True → (p3 → True)) ∨ ((True ∧ (p5 ∧ p2)) ∨ (True → ((p1 → p1) → (p1 ∨ p4)))))) → False) ∨ ((True ∨ True) ∨ True)) ∨ p1) ∧ True) := by
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
theorem thm_5_vars_116894004300356747409640045147 : (((p4 → p1) ∨ ((True → True) ∧ ((((False ∨ (p2 ∧ ((True → ((p4 → (p4 ∨ p5)) ∨ True)) ∨ p3))) ∧ True) → p4) ∨ p2))) ∨ (False → p5)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_41531302010946781981346054666 : ((((((((p5 ∨ p5) ∨ p5) ∧ p5) ∧ (p2 ∧ True)) ∧ p5) ∨ (((p2 → (((False → False) ∧ (p2 ∨ p4)) → False)) → p2) ∨ p2)) ∨ True) ∨ p2) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_676507018036851381961482727854 : ((((True ∧ ((p2 → (p2 ∧ (p3 → (p5 → p3)))) → ((p4 → p5) ∧ ((p2 ∧ (p3 ∧ False)) → p2)))) ∧ (((p5 ∧ True) → p4) ∧ p2)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_558059139044843331129677758917 : (((p3 ∨ (p1 ∨ ((p5 → p5) → ((False ∨ ((((p3 → (True ∧ p4)) ∨ True) ∧ p4) ∧ (p4 ∨ p4))) ∨ (((p1 ∧ p2) → True) ∨ True))))) ∧ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
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
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_114681686995398519128247672247 : (((p1 ∨ (((p3 ∨ p4) → (p5 ∨ ((((False ∨ p2) ∧ False) → p5) ∧ p3))) ∨ p4)) ∨ ((False ∨ (p4 ∧ (p4 ∧ True))) → p4)) ∨ (False ∧ p4)) := by
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
    -- Conjunctions on the left can always be decomposed.
    let h6 := h5.left
    let h7 := h5.right
    -- One of the premise coincides with the conclusion.
    exact h6



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_322944028019336073267193449646 : (p5 ∨ ((p1 ∧ (p2 ∧ ((((p2 → (((False → True) ∨ (True → True)) → p5)) ∨ (p1 → (p3 → p3))) → p3) ∧ (p2 ∨ (False ∧ False))))) → p3)) := by
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
  let h6 := h5.left
  let h7 := h5.right
  -- Disjunctions on the left can always be decomposed.
  cases h7
  case inl h8 =>
    -- We want to use the implication h6 based on <expert-advice>. So we show its premise.
    have h9 : ((p2 → (((False → True) ∨ (True → True)) → p5)) ∨ (p1 → (p3 → p3))) := by
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Implications on the right can always be decomposed.
      intro h10
      -- Implications on the right can always be decomposed.
      intro h11
      -- One of the premise coincides with the conclusion.
      exact h11
    -- We have shown the premise of h6, we can now drive its conclusion.
    let h12 := h6 h9
    -- One of the premise coincides with the conclusion.
    exact h12
  case inr h13 =>
    -- Conjunctions on the left can always be decomposed.
    let h14 := h13.left
    let h15 := h13.right
    -- False on the left can always be used.
    apply False.elim h14



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_698855828259406048460918910095 : ((((False ∧ (((False → (True → True)) ∨ p1) ∨ (True ∧ (p1 ∨ p2)))) ∨ (p1 ∧ (((False → False) ∧ (True → (p2 ∧ p4))) → (p2 → p1)))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_757611961652732094381246837476 : (((p1 ∧ (p3 ∧ (p3 ∧ (((((False → ((((False ∨ (p3 ∨ p5)) → (True ∧ (True ∧ True))) ∨ p5) → p2)) ∧ p3) ∧ p4) ∨ False) ∧ p5)))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_206064731700858887077086911071 : ((p3 ∧ ((p5 ∧ (False ∧ False)) ∨ p4)) ∨ (((p4 → (p3 → p4)) → ((p3 → ((False → False) ∨ (p4 ∧ False))) ∧ (True → True))) → (p4 → p4))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- One of the premise coincides with the conclusion.
  exact h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_49161257590462523478152868506 : ((((((p2 ∧ p1) ∧ p3) ∧ (p1 → p1)) ∧ ((((p4 ∨ ((p2 ∧ (p4 ∨ True)) ∧ p1)) ∧ False) → p3) ∧ p3)) ∨ ((p2 ∨ False) ∧ p4)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_215319193165849457638025688793 : ((p1 ∧ (p1 ∧ (True ∧ p4))) ∨ ((p4 ∨ ((((p3 ∧ p4) ∧ (p1 ∧ (p1 → p1))) ∨ True) ∨ False)) ∨ (((p4 → p5) → p1) ∨ (p5 ∨ p1)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
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



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_299103481770615052614767840520 : (False ∨ (((((p5 ∧ p3) ∨ (p4 ∨ p3)) ∧ (p4 ∨ (((False ∨ ((p3 ∨ ((p3 ∧ (p1 ∨ False)) ∧ p5)) ∧ p5)) → False) ∧ False))) ∧ p4) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_64946398101183358375516382832 : ((p2 ∨ ((p1 → ((p5 ∨ (p5 ∧ (p4 ∧ (p3 → False)))) ∧ p1)) ∧ ((p4 ∨ p2) → (((p4 → p2) ∧ (p5 ∧ p3)) ∧ (False ∧ False))))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_638087457450662606412684313872 : (((((p2 ∨ (((p2 ∨ p5) ∧ True) → (p2 ∨ True))) ∨ (((True ∨ p3) ∨ True) ∧ (((False ∨ ((p2 → p1) → p1)) ∧ p1) ∨ p5))) → p2) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_662689316948454664170262516213 : (((((((p2 → p5) → True) → p4) ∨ ((((p3 ∧ (p2 → True)) ∧ (p3 ∧ p2)) → (p4 ∧ p2)) ∨ ((p4 → p1) ∨ p4))) → (p1 → p1)) ∨ p2) ∧ True) := by
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
    -- One of the premise coincides with the conclusion.
    exact h2
  case inr h4 =>
    -- Disjunctions on the left can always be decomposed.
    cases h4
    case inl h5 =>
      -- One of the premise coincides with the conclusion.
      exact h2
    case inr h6 =>
      -- Disjunctions on the left can always be decomposed.
      cases h6
      case inl h7 =>
        -- One of the premise coincides with the conclusion.
        exact h2
      case inr h8 =>
        -- One of the premise coincides with the conclusion.
        exact h2
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_240425272487686491711906602538 : ((p5 ∨ True) ∧ (((p1 ∨ (p1 ∧ p5)) ∧ (p1 → (((False ∨ p2) → p4) ∨ (p2 ∧ ((((True ∨ (p3 ∧ False)) ∧ p2) ∧ p2) ∨ p5))))) ∨ True)) := by
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
theorem thm_5_vars_314406133880067387467046656009 : (p3 ∨ ((((((p2 ∨ p5) ∧ ((p1 → p5) → p5)) ∨ ((p3 ∨ p5) ∨ True)) → (p3 ∨ (p1 → p1))) ∨ p1) ∨ ((p5 → (p2 → p1)) → True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_112087742831776272519933191717 : ((((p5 ∨ False) ∨ (True ∧ ((True → False) → ((((p3 ∧ p1) → p3) ∨ True) ∧ (p4 ∧ ((False ∨ (p3 ∧ p4)) ∨ p2)))))) ∨ p2) ∨ (p5 ∨ p2)) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
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
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
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



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_353502905256555768977185332502 : (p4 → (p2 ∨ (((False → p4) ∧ p1) → ((((p5 ∧ ((p4 ∧ (p4 → (p3 ∨ ((False ∧ p3) ∧ False)))) → p2)) ∨ p4) ∧ True) ∨ (True → False))))) := by
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
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_137137345358671234278908201185 : ((True ∧ (p2 ∨ (((p4 → (p2 ∨ p1)) ∨ (((((p3 ∨ p4) ∧ p1) → p5) → ((True ∧ False) ∨ p4)) → p3)) ∨ True))) ∨ (p2 ∧ (p5 → False))) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_166763374958526623555071437457 : ((p5 → (((False ∧ (((p1 → ((True ∧ p3) → False)) ∨ p5) ∧ (p5 ∨ p2))) ∨ p4) ∧ p2)) ∨ ((p3 ∧ (p1 → p5)) ∨ (p2 → (p2 ∨ p1)))) := by
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
theorem thm_5_vars_192571776085434612375481826926 : (((p4 ∨ ((p2 ∨ p2) ∧ (True ∧ (p4 ∧ p1)))) ∨ p3) → (((((p1 → (p3 ∨ p5)) ∧ ((p4 ∨ False) ∧ p1)) ∨ p4) ∧ True) ∨ (p1 → p1))) := by
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
      -- Conjunctions on the right can always be decomposed.
      apply And.intro
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- One of the premise coincides with the conclusion.
      exact h3
      -- True on the right can always be proven directly.
      apply True.intro
    case inr h4 =>
      -- Conjunctions on the left can always be decomposed.
      let h5 := h4.left
      let h6 := h4.right
      -- Disjunctions on the left can always be decomposed.
      cases h5
      case inl h7 =>
        -- Conjunctions on the left can always be decomposed.
        let h8 := h6.left
        let h9 := h6.right
        -- Conjunctions on the left can always be decomposed.
        let h10 := h9.left
        let h11 := h9.right
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- Conjunctions on the right can always be decomposed.
        apply And.intro
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- One of the premise coincides with the conclusion.
        exact h10
        -- True on the right can always be proven directly.
        apply True.intro
      case inr h12 =>
        -- Conjunctions on the left can always be decomposed.
        let h13 := h6.left
        let h14 := h6.right
        -- Conjunctions on the left can always be decomposed.
        let h15 := h14.left
        let h16 := h14.right
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- Conjunctions on the right can always be decomposed.
        apply And.intro
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- One of the premise coincides with the conclusion.
        exact h15
        -- True on the right can always be proven directly.
        apply True.intro
  case inr h17 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h18
    -- One of the premise coincides with the conclusion.
    exact h18



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_356997409857246536230680374292 : (p5 → (((p5 ∧ p5) ∧ p1) ∨ (((p1 → ((((p3 → (p5 → (False ∨ p3))) ∨ p2) ∧ True) → p4)) → p2) ∨ (True ∨ ((p1 → True) ∨ p3))))) := by
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
theorem thm_5_vars_655833651561790228214163918582 : (((((((p2 → ((p1 ∧ ((True → ((p2 → (False ∧ True)) ∨ p1)) → False)) ∨ False)) → False) → p1) → (p5 → (p1 ∨ False))) ∨ (p4 ∧ p5)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_173861494576573080191985745974 : ((((((True → False) ∨ ((p2 ∧ (True → True)) → p2)) ∧ (False → p1)) ∧ p2) → p2) → ((p5 ∨ p1) → ((p1 ∧ ((p1 ∨ p3) → p4)) → p4))) := by
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
  cases h2
  case inl h6 =>
    -- We want to use the implication h5 based on <expert-advice>. So we show its premise.
    have h7 : (p1 ∨ p3) := by
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- One of the premise coincides with the conclusion.
      exact h4
    -- We have shown the premise of h5, we can now drive its conclusion.
    let h8 := h5 h7
    -- One of the premise coincides with the conclusion.
    exact h8
  case inr h9 =>
    -- We want to use the implication h5 based on <expert-advice>. So we show its premise.
    have h10 : (p1 ∨ p3) := by
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- One of the premise coincides with the conclusion.
      exact h9
    -- We have shown the premise of h5, we can now drive its conclusion.
    let h11 := h5 h10
    -- One of the premise coincides with the conclusion.
    exact h11



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_249645101221694121369528805591 : ((p5 ∨ p3) ∨ (p3 → (((((p1 ∧ p5) → (((p2 ∨ True) ∨ p5) → (False ∧ p3))) → p5) → p2) ∨ ((p5 → p4) → ((p2 ∧ p5) ∨ True))))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h2
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_247833809981023800398663370639 : ((p1 ∨ p2) ∨ ((((True ∧ (((p3 ∧ True) → p4) ∨ p2)) ∧ False) ∨ (True → (((((p3 ∧ p1) → p2) → (False ∧ p5)) → p2) ∨ True))) ∨ p3)) := by
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
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_122213027385674339153006060287 : ((((((p4 ∧ False) ∨ (p5 ∨ (p1 → (p3 ∨ p5)))) → p2) ∧ (((p4 ∧ ((p2 ∨ True) → p2)) → p1) ∧ p4)) ∧ (p3 ∨ p1)) → (p2 ∨ p4)) := by
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
  -- Disjunctions on the left can always be decomposed.
  cases h3
  case inl h8 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h7
  case inr h9 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h7



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_690557642717362790537124853210 : (((((((((p3 ∧ p3) ∨ (p4 ∧ (p1 → (p5 ∧ p5)))) ∧ True) → p1) ∧ True) ∨ p4) → (p2 ∧ (p3 ∨ ((p4 ∨ (p2 ∨ p4)) → p5)))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_135876049375008251456869767027 : ((((p4 ∨ p5) ∧ (p5 ∨ ((((p2 ∧ p3) → True) ∨ True) → p2))) ∨ ((((p4 ∧ False) ∧ False) ∧ p1) ∧ (p3 ∧ p2))) ∨ (p2 → (p5 → p2))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_227644624709979542012939770317 : ((False ∧ (p5 ∨ p2)) ∨ ((p4 → p5) → (((p2 ∨ (False ∨ True)) → ((p4 → (p2 ∧ p2)) ∧ p5)) → (((p5 ∨ False) ∧ True) ∧ (p3 ∨ True))))) := by
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
  -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
  have h3 : (p2 ∨ (False ∨ True)) := by
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h2, we can now drive its conclusion.
  let h4 := h2 h3
  -- We need to get the right conjuct of h4 based on <expert-advice>.
  let h5 := h4.right
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- One of the premise coincides with the conclusion.
  exact h5
  -- True on the right can always be proven directly.
  apply True.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_676568357294868389537480214837 : ((((p1 ∧ (((p1 ∧ (False ∨ (p5 → True))) → p5) ∧ (True ∨ ((p1 ∧ True) → (p5 → (p3 ∨ p3)))))) ∧ (((p2 ∧ p2) → p5) ∨ p1)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_148050642292410570048051176663 : (((p5 ∧ (p1 ∨ ((p2 → p3) ∧ (((p2 → ((p5 ∨ (p5 ∨ p3)) ∧ False)) ∨ p5) ∨ p2)))) ∨ (p3 ∧ p5)) ∨ (((p2 → p2) ∨ p1) ∨ p5)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_54686958259748318257857588674 : ((((p3 ∧ (False ∧ ((False ∧ p3) → p2))) → p5) → (((((p3 → p5) ∧ p3) ∨ ((False ∧ False) ∧ p5)) ∧ ((p5 → p3) ∨ p2)) ∨ p3)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_198540906201300306120047123139 : ((False ∨ (p3 ∧ (p1 → (False ∧ (False ∧ p3))))) ∨ (True ∨ ((p4 → (p1 → (((p4 ∧ p2) ∨ (False ∧ p5)) ∧ (True ∧ (p4 ∨ p4))))) ∨ p5))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_156657639305173625524552274114 : (((((p1 ∧ p1) ∧ (p1 → (((((p4 ∧ p5) → (False → p1)) ∨ p5) ∨ False) ∧ p1))) → False) ∧ False) ∨ ((False ∧ True) → (p3 ∧ (p5 ∧ p3)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- False on the left can always be used.
  apply False.elim h2
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Conjunctions on the left can always be decomposed.
  let h4 := h1.left
  let h5 := h1.right
  -- False on the left can always be used.
  apply False.elim h4
  -- Conjunctions on the left can always be decomposed.
  let h6 := h1.left
  let h7 := h1.right
  -- False on the left can always be used.
  apply False.elim h6



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_310674673185510402277215949953 : (p2 ∨ (((p1 → False) ∨ (p3 ∨ p3)) → (p2 ∨ (((p5 ∧ (True ∧ (((p1 ∧ (p3 ∧ (p5 → False))) → True) ∧ True))) ∧ True) ∨ (p1 → p3))))) := by
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
    -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
    have h4 : p1 := by
      -- One of the premise coincides with the conclusion.
      exact h3
    -- We have shown the premise of h2, we can now drive its conclusion.
    let h5 := h2 h4
    -- False on the left can always be used.
    apply False.elim h5
  case inr h6 =>
    -- Disjunctions on the left can always be decomposed.
    cases h6
    case inl h7 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Implications on the right can always be decomposed.
      intro h8
      -- One of the premise coincides with the conclusion.
      exact h7
    case inr h9 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Implications on the right can always be decomposed.
      intro h10
      -- One of the premise coincides with the conclusion.
      exact h9



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_135977345413343256031590335833 : ((((False ∧ (p1 ∨ (p3 ∨ ((p5 → p1) ∧ p1)))) ∨ True) ∨ ((((p4 → p5) → p2) ∨ (p1 → (p1 → p4))) ∧ p2)) ∨ (True → (True → p3))) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_43937817276834414636887590634 : (((((((False → p1) → ((p1 ∧ (p1 ∨ p4)) ∧ False)) ∨ False) ∧ (p1 ∧ ((((p4 ∧ False) ∧ True) → True) ∧ p5))) ∨ (p4 ∨ False)) → p4) ∨ p3) := by
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
    -- Disjunctions on the left can always be decomposed.
    cases h3
    case inl h5 =>
      -- Conjunctions on the left can always be decomposed.
      let h6 := h4.left
      let h7 := h4.right
      -- Conjunctions on the left can always be decomposed.
      let h8 := h7.left
      let h9 := h7.right
      -- We want to use the implication h5 based on <expert-advice>. So we show its premise.
      have h10 : (False → p1) := by
        -- Implications on the right can always be decomposed.
        intro h11
        -- False on the left can always be used.
        apply False.elim h11
      -- We have shown the premise of h5, we can now drive its conclusion.
      let h12 := h5 h10
      -- We need to get the right conjuct of h12 based on <expert-advice>.
      let h13 := h12.right
      -- False on the left can always be used.
      apply False.elim h13
    case inr h14 =>
      -- False on the left can always be used.
      apply False.elim h14
  case inr h15 =>
    -- Disjunctions on the left can always be decomposed.
    cases h15
    case inl h16 =>
      -- One of the premise coincides with the conclusion.
      exact h16
    case inr h17 =>
      -- False on the left can always be used.
      apply False.elim h17



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_664904339140485100582803507350 : ((((p3 → ((((p5 ∧ (False ∧ ((((False ∨ (((p4 ∧ False) ∧ True) ∨ p4)) ∧ p2) ∨ p1) → True))) ∧ p5) → p3) ∧ p2)) → (True ∧ p3)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_181074075920072938683442832446 : (((p2 ∨ p2) → ((((True ∧ p4) ∨ (True → p5)) ∧ (p2 → p1)) ∧ p1)) → (((p4 → (p3 ∨ p1)) ∨ p5) ∨ (False ∨ (False → (p3 ∨ p3))))) := by
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
theorem thm_5_vars_111783552101075312614396714361 : (((((True ∧ (((True ∨ (p5 ∧ (p3 ∧ (p1 ∨ p5)))) → (p1 → (p2 ∧ p1))) ∧ p3)) → (p4 → False)) ∨ (p3 → p3)) ∨ p1) ∨ (False ∧ p5)) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_192651105975450836330789750909 : ((((p1 → (p4 → ((p1 ∧ p2) → p1))) ∨ p2) → True) → ((p5 ∧ ((p1 → p2) ∧ p1)) ∨ (((False ∨ p2) → p2) ∨ ((p4 ∧ p2) ∨ p1)))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h2
  -- Disjunctions on the left can always be decomposed.
  cases h2
  case inl h3 =>
    -- False on the left can always be used.
    apply False.elim h3
  case inr h4 =>
    -- One of the premise coincides with the conclusion.
    exact h4



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_134509766990102658312755962862 : (((((False ∨ True) → (((((p5 ∧ True) ∨ (p1 → False)) ∨ p4) → (p1 → (p2 → p3))) ∨ (False → p1))) ∨ True) → p5) ∨ (p3 ∨ (p1 → True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_53629609072802422295265763588 : ((((((p5 ∧ p4) ∧ p1) → p1) ∨ (p2 ∧ (True ∧ True))) ∧ ((False → p2) ∧ ((p1 ∧ True) ∨ (((p4 ∧ p1) → p2) → (p2 ∨ p4))))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_315307589951054197689991545414 : (p3 ∨ ((p5 ∧ (p4 ∨ (True ∨ p1))) → (True ∧ ((p2 ∧ (p1 ∨ p3)) ∨ ((((p5 ∨ p2) ∨ (True → p3)) → (p1 ∧ True)) ∨ (p2 → p2)))))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- Disjunctions on the left can always be decomposed.
  cases h3
  case inl h4 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h5
    -- One of the premise coincides with the conclusion.
    exact h5
  case inr h6 =>
    -- Disjunctions on the left can always be decomposed.
    cases h6
    case inl h7 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Implications on the right can always be decomposed.
      intro h8
      -- One of the premise coincides with the conclusion.
      exact h8
    case inr h9 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Implications on the right can always be decomposed.
      intro h10
      -- One of the premise coincides with the conclusion.
      exact h10



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_244212539848162805167667238381 : ((True ∧ p5) ∨ (((p5 ∧ p4) ∨ ((p3 ∨ ((False → False) ∧ p2)) → p4)) ∨ ((True ∧ (p5 ∨ (((p3 → True) ∨ (p5 → True)) ∨ p3))) ∨ p1))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
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
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_137048395298579357714935720023 : (((False → p4) → ((((True ∨ p2) → (p3 ∧ (p4 ∧ p5))) → p4) → (((p5 ∧ p5) ∨ (p1 ∨ p2)) ∨ (p4 ∨ p5)))) ∨ (p3 → (False → p4))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- False on the left can always be used.
  apply False.elim h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_152887374288195041554559833661 : ((True ∧ (((p1 ∨ ((False ∨ True) ∨ p5)) → False) ∧ ((True → (p3 ∧ p3)) ∨ (False ∧ ((p1 → p5) ∨ p4))))) → ((False ∧ p2) ∨ (p4 → p5))) := by
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
    -- We want to use the implication h4 based on <expert-advice>. So we show its premise.
    have h7 : (p1 ∨ ((False ∨ True) ∨ p5)) := by
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- True on the right can always be proven directly.
      apply True.intro
    -- We have shown the premise of h4, we can now drive its conclusion.
    let h8 := h4 h7
    -- False on the left can always be used.
    apply False.elim h8
  case inr h9 =>
    -- Conjunctions on the left can always be decomposed.
    let h10 := h9.left
    let h11 := h9.right
    -- False on the left can always be used.
    apply False.elim h10



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_302648757595729448154298114680 : (False ∨ (p2 ∨ (((p2 ∨ p4) → p5) ∨ ((((p5 → (p4 ∧ (p3 ∧ False))) ∨ ((False → p5) ∧ (p2 ∨ True))) ∧ ((p4 → p5) → True)) ∨ p3)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
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
  -- Implications on the right can always be decomposed.
  intro h2
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_263378595835335523852330009646 : (True ∧ (((p5 ∧ (p1 ∨ (False → ((p3 ∨ (((False → (p4 ∨ p1)) → p2) ∨ (p3 ∧ (False ∧ p2)))) ∧ True)))) ∨ p5) ∨ ((p2 → p1) ∨ True))) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_37966098174942697594810256556 : ((((((False ∧ (True ∨ (((False → (False → p5)) → False) ∧ (((False → True) ∨ p1) ∧ (p1 ∨ False))))) → p4) → p4) ∨ (p3 → True)) ∧ True) ∨ p1) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_61059649456902523005766958869 : ((False ∧ (((p5 → ((True ∨ p3) ∨ (p2 → p5))) → (((p3 ∧ ((p1 → p5) → (p1 ∨ False))) ∧ p2) ∨ p5)) ∧ ((p2 → False) → True))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_225413586978810133897853558502 : (((p3 ∨ False) ∧ p4) ∨ ((p3 ∨ (p1 ∨ ((False → p4) ∨ (((p1 ∧ ((p5 ∨ (p2 ∧ p4)) ∧ p3)) ∨ p4) ∧ True)))) ∨ (True ∧ (p4 ∧ p5)))) := by
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
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_745835579871485341494958653959 : ((((False ∨ p1) → (((p4 → (((p4 ∨ p5) ∧ (((p5 ∧ p1) ∨ p1) ∨ ((p5 ∧ p1) → p4))) ∨ p1)) ∧ p1) → (p3 ∨ (p3 ∧ p5)))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_317704683045047700117318869180 : (p4 ∨ (((((p4 → (p5 → (((False → p3) ∧ False) ∨ (p2 → (((False ∧ (True ∨ True)) ∧ p5) ∧ p3))))) ∨ p4) → p2) ∨ (False → p1)) ∨ p4)) := by
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
theorem thm_5_vars_591779072785696456044949337220 : ((((((((True → ((p4 → True) ∧ p4)) ∧ (p3 ∨ (p4 ∨ (p3 ∧ ((p3 → p4) → p4))))) ∧ p3) ∨ (p5 ∨ p2)) ∨ (p3 ∨ True)) ∧ True) ∨ p5) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
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
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_942816360298367869498029706252 : (((((p5 → (True ∨ False)) → p3) ∧ (((p2 → p2) ∨ ((p5 → p1) ∨ (((p5 ∧ (p5 ∧ p1)) → p4) → False))) ∧ ((p5 ∧ p4) ∧ p2))) → p3) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
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
    -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
    have h11 : (p5 → (True ∨ False)) := by
      -- Implications on the right can always be decomposed.
      intro h12
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- True on the right can always be proven directly.
      apply True.intro
    -- We have shown the premise of h2, we can now drive its conclusion.
    let h13 := h2 h11
    -- One of the premise coincides with the conclusion.
    exact h13
  case inr h14 =>
    -- Disjunctions on the left can always be decomposed.
    cases h14
    case inl h15 =>
      -- Conjunctions on the left can always be decomposed.
      let h16 := h5.left
      let h17 := h5.right
      -- Conjunctions on the left can always be decomposed.
      let h18 := h16.left
      let h19 := h16.right
      -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
      have h20 : (p5 → (True ∨ False)) := by
        -- Implications on the right can always be decomposed.
        intro h21
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- True on the right can always be proven directly.
        apply True.intro
      -- We have shown the premise of h2, we can now drive its conclusion.
      let h22 := h2 h20
      -- One of the premise coincides with the conclusion.
      exact h22
    case inr h23 =>
      -- Conjunctions on the left can always be decomposed.
      let h24 := h5.left
      let h25 := h5.right
      -- Conjunctions on the left can always be decomposed.
      let h26 := h24.left
      let h27 := h24.right
      -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
      have h28 : (p5 → (True ∨ False)) := by
        -- Implications on the right can always be decomposed.
        intro h29
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- True on the right can always be proven directly.
        apply True.intro
      -- We have shown the premise of h2, we can now drive its conclusion.
      let h30 := h2 h28
      -- One of the premise coincides with the conclusion.
      exact h30
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_47145209016791401049745885733 : (((((((p3 ∨ p1) → ((False ∧ p5) → p3)) ∧ ((p2 → True) → (p3 ∧ p5))) → p5) ∨ ((p5 ∧ p2) ∧ (p1 → p5))) ∨ (False ∧ p1)) ∨ p2) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- We want to use the implication h3 based on <expert-advice>. So we show its premise.
  have h4 : (p2 → True) := by
    -- Implications on the right can always be decomposed.
    intro h5
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h3, we can now drive its conclusion.
  let h6 := h3 h4
  -- We need to get the right conjuct of h6 based on <expert-advice>.
  let h7 := h6.right
  -- One of the premise coincides with the conclusion.
  exact h7



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_949149956814879245182378889785 : (((((True → p3) ∧ p2) ∧ ((((p5 → p2) → True) ∨ True) → ((p2 → True) → ((False ∨ (((True ∨ True) ∧ p4) → p5)) → (p1 ∧ p2))))) → p3) ∧ True) := by
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
  -- We want to use the implication h4 based on <expert-advice>. So we show its premise.
  have h6 : True := by
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h4, we can now drive its conclusion.
  let h7 := h4 h6
  -- One of the premise coincides with the conclusion.
  exact h7
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_135377745294530495377875376043 : (((((True ∧ p3) ∨ (p1 ∧ (False ∨ (((p5 → p2) ∨ (p1 ∨ (p3 ∨ p3))) ∧ False)))) ∨ True) ∨ ((p1 ∨ p4) ∨ p2)) ∨ (p2 → (p1 ∧ p4))) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_134058025291169946899757450324 : ((((p2 → ((((p2 ∧ p5) ∧ False) ∨ p3) ∨ (p3 ∨ ((p3 ∧ ((True ∨ True) ∧ True)) ∨ (True ∨ p5))))) ∨ False) ∨ p4) ∨ ((p1 ∧ True) → p5)) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
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
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_118254395732831886758166161965 : ((p1 ∨ (((((p5 → p5) → (p3 ∨ (p4 ∧ p4))) ∧ p1) ∧ (p3 ∧ ((True ∧ False) → p5))) ∧ (((False ∧ p2) ∧ False) ∧ p3))) ∨ (True ∨ p4)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_620094760140354303006866633816 : (((((True ∧ p3) ∨ (((False ∨ ((((p4 ∨ p5) ∧ p5) → p4) ∨ ((p5 → p5) ∨ p5))) ∨ (p3 ∧ ((p1 ∨ p5) ∨ False))) → p3)) ∨ True) ∨ p4) ∧ True) := by
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
theorem thm_5_vars_3923508073150837637800182696 : (False ∨ (((p1 ∨ (p2 ∨ (p3 → p3))) ∧ (True ∧ (p1 ∧ ((True → p4) ∨ p4)))) ∨ (p5 ∨ (True ∨ ((p5 ∨ (p3 ∨ p4)) ∨ False))))) := by
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
theorem thm_5_vars_351004384777906402352313020363 : (p4 → ((p2 ∨ (((p5 ∨ (((p5 ∨ False) → (((True ∧ False) → p2) → p2)) → False)) ∧ p4) → (((p4 ∧ True) ∧ p2) ∧ p5))) ∨ (True ∨ True))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_37258583529280638997372714303 : ((((p2 ∧ (p4 ∨ ((p2 ∧ (p3 ∨ (p5 ∧ False))) ∨ (p3 → (((True ∧ ((p5 ∧ False) ∧ p1)) ∧ p4) → (False ∧ True)))))) ∧ p3) ∧ p3) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_666631809202117693872414857401 : (((((p1 ∨ (p5 ∧ (((p1 ∨ p1) → p2) → ((p1 → p5) ∧ p5)))) ∨ (((p3 ∨ p1) ∧ (p4 ∧ False)) ∨ True)) ∧ ((False ∨ False) → p4)) ∨ False) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
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
  -- Implications on the right can always be decomposed.
  intro h1
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h2 =>
    -- False on the left can always be used.
    apply False.elim h2
  case inr h3 =>
    -- False on the left can always be used.
    apply False.elim h3
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_121435264683503394972762058904 : ((((((True ∨ False) ∧ ((False → ((True ∧ p5) → False)) ∧ (((p4 → p3) ∧ ((True ∧ p1) ∨ p5)) ∧ True))) ∧ p5) → p1) → p2) → (p2 ∨ True)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_118499609960458268498841418021 : ((p3 ∨ (((True → p2) → ((True → p4) ∨ (((p3 → p5) ∨ p5) ∨ False))) → (((False ∨ ((p5 → p4) ∧ p2)) ∧ p5) ∧ p1))) ∨ (True ∨ p4)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_139323297244910245342985461429 : (((p1 ∨ (((False → ((p4 ∨ True) ∨ (p2 → (p4 → False)))) → (p4 → p2)) ∨ ((p2 → (True ∨ p1)) ∨ False))) ∨ p5) → (False ∨ (p4 ∨ True))) := by
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
        -- Disjunctions on the left can always be decomposed.
        cases h6
        case inl h7 =>
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- True on the right can always be proven directly.
          apply True.intro
        case inr h8 =>
          -- False on the left can always be used.
          apply False.elim h8
  case inr h9 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_316452999004296095669781271571 : (p3 ∨ (p1 ∨ ((((p5 ∧ p2) ∨ (p4 → False)) ∧ p2) ∨ (False → (((((p2 ∧ (False ∧ p5)) ∨ True) ∨ True) ∨ p5) → ((False ∨ p4) ∧ p2)))))) := by
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
  -- Disjunctions on the left can always be decomposed.
  cases h2
  case inl h3 =>
    -- Disjunctions on the left can always be decomposed.
    cases h3
    case inl h4 =>
      -- Disjunctions on the left can always be decomposed.
      cases h4
      case inl h5 =>
        -- Conjunctions on the left can always be decomposed.
        let h6 := h5.left
        let h7 := h5.right
        -- Conjunctions on the left can always be decomposed.
        let h8 := h7.left
        let h9 := h7.right
        -- False on the left can always be used.
        apply False.elim h8
      case inr h10 =>
        -- False on the left can always be used.
        apply False.elim h1
    case inr h11 =>
      -- False on the left can always be used.
      apply False.elim h1
  case inr h12 =>
    -- False on the left can always be used.
    apply False.elim h1
  -- Disjunctions on the left can always be decomposed.
  cases h2
  case inl h13 =>
    -- Disjunctions on the left can always be decomposed.
    cases h13
    case inl h14 =>
      -- Disjunctions on the left can always be decomposed.
      cases h14
      case inl h15 =>
        -- Conjunctions on the left can always be decomposed.
        let h16 := h15.left
        let h17 := h15.right
        -- Conjunctions on the left can always be decomposed.
        let h18 := h17.left
        let h19 := h17.right
        -- False on the left can always be used.
        apply False.elim h18
      case inr h20 =>
        -- False on the left can always be used.
        apply False.elim h1
    case inr h21 =>
      -- False on the left can always be used.
      apply False.elim h1
  case inr h22 =>
    -- False on the left can always be used.
    apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_612920846576990978218542788277 : (((((p4 ∨ ((p2 → p4) ∧ (p2 → ((((p1 ∧ (p2 ∧ (p5 → p1))) ∧ p3) ∧ ((p3 ∨ p3) ∧ p1)) → p5)))) ∨ (p2 → p3)) ∨ p4) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_171977745634317900712158239600 : (((p4 ∨ (p2 ∧ ((p5 ∨ p5) ∧ ((p2 → (p3 → p5)) ∨ True)))) ∧ (p4 ∨ False)) ∨ (False → (p2 ∨ ((p2 ∧ (True → False)) → (p2 ∨ True))))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_682490199938206751331127988709 : ((((((p1 ∧ True) ∧ (p5 ∧ (p1 ∨ ((p2 ∨ (True → False)) ∧ p2)))) → (p5 ∧ (p1 → False))) ∧ ((True ∧ (p4 ∧ p4)) ∧ (p5 ∧ p4))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_165087203752408855405241754494 : (((p2 ∨ (((((p5 ∨ p1) → (p1 ∧ p2)) ∨ (p3 ∨ (False → p3))) ∧ p5) ∧ p1)) → p2) ∨ (p4 ∨ (p5 → (p2 ∨ ((p3 ∨ False) → p3))))) := by
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
  -- Disjunctions on the left can always be decomposed.
  cases h2
  case inl h3 =>
    -- One of the premise coincides with the conclusion.
    exact h3
  case inr h4 =>
    -- False on the left can always be used.
    apply False.elim h4



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_388424517653797822410653467916 : ((((((True ∨ (p2 ∧ (((False ∨ (p3 ∨ (True ∨ (True → p4)))) ∧ p5) ∨ p2))) → (p2 ∨ p3)) → (((True ∨ p4) → False) ∨ True)) ∨ p2) ∧ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_338781399048939379595699494700 : (p1 → ((p4 ∧ False) ∨ ((p5 ∧ p3) ∨ (p4 ∨ (True ∨ ((p1 ∨ ((((False ∧ p1) ∨ p5) → ((p2 ∨ p1) ∨ p1)) ∨ p5)) ∧ (False ∧ p2))))))) := by
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
theorem thm_5_vars_260268568669599521168430035820 : ((p2 → p3) → (p5 ∨ ((p5 → ((p1 ∨ (((p4 ∧ (p4 ∨ p1)) ∨ (((p2 ∧ (p4 ∧ p2)) ∨ (False ∧ True)) → p3)) ∧ True)) ∨ p2)) ∨ True))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_309820434148905687395522491931 : (p2 ∨ ((p1 → ((False ∧ (p5 ∨ (True → ((p3 ∧ (True → p4)) → (((p5 → True) ∧ p3) → False))))) ∨ True)) ∨ ((p1 ∨ p1) ∨ (p5 ∨ True)))) := by
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
theorem thm_5_vars_63427634801108455328520174630 : ((p5 ∧ (p1 → (((((((True ∨ (True ∨ True)) ∨ p1) ∨ p2) ∧ (p3 ∨ (True → (((False ∧ p5) ∧ False) ∧ False)))) ∨ p1) ∧ False) ∧ p1))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_589623702437002870338138931242 : (((((((True ∨ p5) ∨ (((False → p5) ∨ ((((p3 → p2) ∨ True) ∨ True) ∧ p3)) ∧ ((p1 ∨ p5) → (p1 ∨ p4)))) → True) → p2) ∧ p5) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_244118437325332537007874117162 : ((True ∧ p3) ∨ (p3 → ((((p4 → (True ∧ False)) ∧ ((((p2 → (p5 → p5)) ∧ p4) ∧ p2) ∨ (p1 → (p3 ∨ p3)))) ∧ (p2 ∨ p2)) ∨ p3))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_656259528338472566675458562089 : (((((((False → p3) ∨ ((p2 → True) → ((p4 ∨ p5) ∧ p2))) → p5) ∧ (p3 ∨ (p4 ∨ ((False ∨ (p1 → p1)) ∨ False)))) ∨ (p3 ∨ True)) ∨ False) ∧ True) := by
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
theorem thm_5_vars_41504258624867231839222904846 : ((((p2 ∧ (True ∨ ((((p1 ∧ p5) ∨ p2) ∨ p4) ∨ (True ∧ p2)))) → ((True ∧ p2) → ((False ∧ p2) ∨ ((p1 ∨ True) ∨ p3)))) ∨ p1) ∨ False) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
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
  -- Disjunctions on the left can always be decomposed.
  cases h6
  case inl h7 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro
  case inr h8 =>
    -- Disjunctions on the left can always be decomposed.
    cases h8
    case inl h9 =>
      -- Disjunctions on the left can always be decomposed.
      cases h9
      case inl h10 =>
        -- Disjunctions on the left can always be decomposed.
        cases h10
        case inl h11 =>
          -- Conjunctions on the left can always be decomposed.
          let h12 := h11.left
          let h13 := h11.right
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- Show the left disjunct based on <expert-advice>.
          apply Or.inl
          -- Show the left disjunct based on <expert-advice>.
          apply Or.inl
          -- One of the premise coincides with the conclusion.
          exact h12
        case inr h14 =>
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- Show the left disjunct based on <expert-advice>.
          apply Or.inl
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- True on the right can always be proven directly.
          apply True.intro
      case inr h15 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
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
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- True on the right can always be proven directly.
      apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_231287414840615125302543295431 : (((p5 ∨ p2) ∨ p1) → (((p4 ∧ p3) ∧ (((True ∨ (False → (False ∧ p3))) ∨ p3) ∧ p4)) → (p1 → ((False ∨ (p4 ∨ (True → False))) ∨ p4)))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Implications on the right can always be decomposed.
  intro h3
  -- Conjunctions on the left can always be decomposed.
  let h4 := h2.left
  let h5 := h2.right
  -- Conjunctions on the left can always be decomposed.
  let h6 := h4.left
  let h7 := h4.right
  -- Conjunctions on the left can always be decomposed.
  let h8 := h5.left
  let h9 := h5.right
  -- Disjunctions on the left can always be decomposed.
  cases h8
  case inl h10 =>
    -- Disjunctions on the left can always be decomposed.
    cases h10
    case inl h11 =>
      -- Disjunctions on the left can always be decomposed.
      cases h1
      case inl h12 =>
        -- Disjunctions on the left can always be decomposed.
        cases h12
        case inl h13 =>
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- One of the premise coincides with the conclusion.
          exact h9
        case inr h14 =>
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- One of the premise coincides with the conclusion.
          exact h9
      case inr h15 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- One of the premise coincides with the conclusion.
        exact h9
    case inr h16 =>
      -- Disjunctions on the left can always be decomposed.
      cases h1
      case inl h17 =>
        -- Disjunctions on the left can always be decomposed.
        cases h17
        case inl h18 =>
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- One of the premise coincides with the conclusion.
          exact h9
        case inr h19 =>
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- One of the premise coincides with the conclusion.
          exact h9
      case inr h20 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- One of the premise coincides with the conclusion.
        exact h9
  case inr h21 =>
    -- Disjunctions on the left can always be decomposed.
    cases h1
    case inl h22 =>
      -- Disjunctions on the left can always be decomposed.
      cases h22
      case inl h23 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- One of the premise coincides with the conclusion.
        exact h9
      case inr h24 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- One of the premise coincides with the conclusion.
        exact h9
    case inr h25 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- One of the premise coincides with the conclusion.
      exact h9



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_216050575684512545313955747158 : ((p5 ∨ (p3 ∧ (p3 ∨ p4))) ∨ ((p1 ∧ True) ∨ (((((False ∧ (p3 ∨ ((p2 → p4) ∧ (False ∨ p1)))) → (False ∧ p1)) ∨ True) ∧ False) → False))) := by
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
    -- False on the left can always be used.
    apply False.elim h3
  case inr h5 =>
    -- False on the left can always be used.
    apply False.elim h3



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_213538229092058195326589265412 : ((((p1 ∧ True) ∧ p3) ∨ p3) ∨ ((p5 ∧ ((p1 ∧ p3) ∨ (p1 ∨ p4))) ∨ (((p1 ∧ (p1 ∨ (p1 ∨ p4))) ∧ p4) ∨ ((p1 ∧ False) ∨ True)))) := by
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
theorem thm_5_vars_58209374022825506502232050133 : (((p4 ∧ p1) ∧ (((((p5 ∧ (True ∧ p3)) ∨ (p4 ∨ p4)) ∨ ((p1 → ((True ∧ False) → p3)) ∧ ((p4 ∨ p5) ∨ p3))) ∨ p4) → p2)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_204360896585931209252882048018 : (((p2 ∨ ((p1 → p2) ∧ p1)) ∧ p3) ∨ ((((False ∨ True) ∨ p5) ∨ True) ∧ (((False → (((p3 → p2) ∨ (p1 ∨ p3)) ∧ False)) ∨ p4) ∨ p2))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- False on the left can always be used.
  apply False.elim h1
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_262410419466155934058849230635 : (True ∧ ((False ∧ ((p4 → ((((((p4 → False) ∧ (p1 ∨ ((False ∧ p1) → False))) → (p5 ∨ p1)) ∧ p3) ∧ p5) ∧ (p3 ∧ p4))) ∨ False)) ∨ True)) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_171774120380274446314262271557 : ((((p2 → (((p1 ∨ (p1 ∧ (p4 ∨ (p3 ∧ p4)))) ∧ True) ∧ p3)) → False) → p5) ∨ ((False → (False ∧ ((True → (p2 ∨ p1)) → p1))) ∨ p1)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- False on the left can always be used.
  apply False.elim h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_178358271911656486467528709050 : (((True → (((p3 ∨ ((p3 ∧ p4) → p5)) ∨ p2) ∧ False)) ∨ (p4 ∧ p3)) ∨ ((True ∧ (False → ((p2 → (p2 → p3)) ∨ p3))) ∨ (p4 ∧ p2))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- Implications on the right can always be decomposed.
  intro h1
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_250152107767636487815390204664 : ((True → p5) ∨ ((((False ∧ p1) ∨ ((((p2 → True) ∨ p5) ∨ p5) ∧ ((p4 → p5) ∨ p4))) ∨ (p4 ∨ ((True ∧ True) ∧ p1))) ∨ (p5 ∨ True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_41559454309938812621610088204 : ((((((p1 → p4) → (p1 ∧ (p2 → p2))) ∨ (p1 ∧ p2)) → (((False ∨ p5) ∨ ((p2 → (p4 ∧ p4)) ∨ p3)) ∨ (True ∨ p3))) ∨ p1) ∨ p1) := by
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
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- True on the right can always be proven directly.
    apply True.intro
  case inr h3 =>
    -- Conjunctions on the left can always be decomposed.
    let h4 := h3.left
    let h5 := h3.right
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- True on the right can always be proven directly.
    apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_60564409353519097468240312549 : ((True ∧ (((((p4 → (p3 ∨ False)) → (p4 ∨ p5)) → (True ∨ (False ∧ (False ∨ (p3 ∨ (((p3 → p5) → False) → True)))))) ∨ p3) → False)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_52122358626078653537348323103 : ((((True ∧ ((((p5 ∧ p5) ∧ p5) ∧ ((p4 ∨ True) ∧ (True → p1))) → p4)) → p2) → (p4 ∧ ((((True → p5) ∨ p3) ∨ p3) ∧ True))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



