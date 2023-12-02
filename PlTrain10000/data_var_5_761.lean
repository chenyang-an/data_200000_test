variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_665806724362642705516317341817 : (((((((((p1 ∧ (((p1 ∨ False) ∨ False) ∧ p3)) ∨ ((p1 ∧ False) ∧ p4)) ∨ (p3 → p2)) ∨ p1) → p3) → p5) ∧ (False ∨ (p1 ∧ True))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_53912627771267481004395655314 : (((False ∨ (((p4 → p4) ∧ ((p4 ∧ p4) ∧ p3)) ∧ p1)) ∨ ((False ∨ False) ∧ (True ∨ ((p4 → (p5 ∧ ((p3 ∧ p4) ∧ p3))) ∧ p3)))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_114364429119254300676878137766 : ((((p2 → ((False → ((p4 → p1) → (p5 → (p5 → ((p1 ∧ p5) → False))))) → False)) ∧ p2) ∨ (((False ∧ p3) → p2) ∧ True)) ∨ (p2 → p4)) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
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
theorem thm_5_vars_47508457476128942639180558094 : (((p2 ∨ (((p1 ∧ p1) ∨ (((p5 ∧ p1) → (((p3 → False) ∧ (False ∧ False)) ∨ (p1 ∨ False))) ∧ False)) ∧ (False ∧ p4))) ∨ (p5 → p5)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_259128418188436707288755126534 : ((False → True) → ((((p3 ∧ (p3 ∧ p2)) ∨ ((p1 ∧ ((p4 → ((p5 ∨ False) ∧ (False ∧ (False → p5)))) → p4)) → p4)) ∨ (p3 → True)) ∨ False)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h2
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_52990949182771156440773695708 : (((((((p1 ∨ False) → p3) → (p3 ∧ False)) → p5) ∨ (p2 ∨ True)) ∧ (((((p5 ∧ p1) ∨ False) ∨ (p2 ∧ True)) ∨ p5) → (p4 ∨ p5))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_77255199397909096882623398437 : ((((True ∧ (p2 ∨ p4)) → ((((((p5 → (p1 → (True → False))) ∨ p4) ∨ p2) ∧ (p1 ∨ True)) ∨ p5) ∨ (True ∨ (p3 ∨ p4)))) → False) → False) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h2 : ((True ∧ (p2 ∨ p4)) → ((((((p5 → (p1 → (True → False))) ∨ p4) ∨ p2) ∧ (p1 ∨ True)) ∨ p5) ∨ (True ∨ (p3 ∨ p4)))) := by
    -- Implications on the right can always be decomposed.
    intro h3
    -- Conjunctions on the left can always be decomposed.
    let h4 := h3.left
    let h5 := h3.right
    -- Disjunctions on the left can always be decomposed.
    cases h5
    case inl h6 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- True on the right can always be proven directly.
      apply True.intro
    case inr h7 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- True on the right can always be proven directly.
      apply True.intro
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h8 := h1 h2
  -- False on the left can always be used.
  apply False.elim h8



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_666641020563774774118178525136 : ((((((((p5 ∨ p2) ∨ ((p3 → (False ∧ p5)) → True)) → True) ∨ p5) → ((p2 ∧ (False → p1)) ∨ (p2 → p5))) ∧ ((p3 → False) ∨ p3)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_206006627799759546174159013489 : ((p1 ∧ (p4 → (p1 ∨ (p2 ∧ p5)))) ∨ ((p1 → True) ∧ (((True → p4) ∨ p4) ∨ (p2 ∨ ((p2 ∧ (p2 ∨ p2)) → (False ∨ (False → p2))))))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
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
    -- False on the left can always be used.
    apply False.elim h6
  case inr h7 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h8
    -- False on the left can always be used.
    apply False.elim h8



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_649695632450166183605224979429 : (((((p3 → ((p4 ∧ (((p2 ∨ (p5 ∧ p2)) ∧ (p3 → ((True ∧ p2) → p4))) ∨ True)) ∨ (p4 → p4))) ∨ (p5 → p1)) ∧ (True ∨ p1)) ∨ False) ∧ True) := by
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
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h2
  -- One of the premise coincides with the conclusion.
  exact h2
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_346589267611151744145493812991 : (p3 → (((((p1 ∧ ((False → ((True ∨ p1) ∧ False)) → (p5 ∨ False))) ∧ (False ∨ ((p1 → p1) ∧ p4))) ∨ False) ∨ p3) ∨ ((p5 → p3) ∨ p5))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_111214716248622411095028369135 : (((((p1 → True) ∧ p1) → (((False ∨ (((p4 ∨ p4) → p3) ∨ p5)) ∨ ((p3 → (p5 ∧ True)) ∧ (False ∧ False))) → p5)) ∧ p1) ∨ (False → p4)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_156922721553861193246546809355 : ((((p2 ∧ ((p4 ∨ p1) → (p5 → (((True ∧ p1) ∧ (False → (True ∨ p2))) → p4)))) → p5) ∨ p4) ∨ ((p2 ∨ True) ∨ (p4 ∧ (True ∧ True)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_47525050311775514194885239253 : (((p3 ∨ (p5 ∧ ((p3 → (p5 ∨ (p2 ∨ p3))) ∨ ((False → True) ∧ (p1 ∧ (p4 ∧ (False → (False ∧ (True ∧ False))))))))) ∨ (p5 ∧ p2)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_643252335400579174387951068606 : ((((p3 ∧ ((p4 ∨ ((p3 ∧ p2) ∨ p4)) ∨ ((p4 ∧ (p5 → ((((True ∧ True) → ((p1 ∨ p1) → True)) ∧ False) ∨ p5))) → True))) → p1) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_206315638261419861276283136623 : ((p1 ∨ ((p2 → p4) → (True ∧ p1))) ∨ (p3 → (p4 ∨ ((p4 ∧ p2) ∨ (((True ∧ p1) ∧ False) ∨ ((False → (p1 ∧ (p3 ∧ p1))) ∨ p2)))))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
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
  -- Implications on the right can always be decomposed.
  intro h2
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- False on the left can always be used.
  apply False.elim h2
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- False on the left can always be used.
  apply False.elim h2
  -- False on the left can always be used.
  apply False.elim h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_137294660866548865767137799744 : ((p2 ∧ (((p4 ∨ (p3 → (((p5 ∨ (p1 → p2)) ∧ p2) ∨ p3))) ∨ ((((p3 → p2) → True) → False) ∧ p3)) → p3)) ∨ (True ∨ (p5 ∧ p1))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_356662177650663550077777377720 : (p5 → (((p2 ∧ p1) ∨ (p1 ∨ ((p5 ∨ False) ∧ p1))) → ((((p3 → ((((True ∧ p4) ∨ p2) ∧ False) ∨ True)) ∨ p1) ∨ True) ∧ (False → False)))) := by
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
      -- True on the right can always be proven directly.
      apply True.intro
    case inr h8 =>
      -- Conjunctions on the left can always be decomposed.
      let h9 := h8.left
      let h10 := h8.right
      -- Disjunctions on the left can always be decomposed.
      cases h9
      case inl h11 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- True on the right can always be proven directly.
        apply True.intro
      case inr h12 =>
        -- False on the left can always be used.
        apply False.elim h12
  -- Implications on the right can always be decomposed.
  intro h13
  -- False on the left can always be used.
  apply False.elim h13



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_263083400233510950871115423999 : (True ∧ ((((False ∧ p5) ∨ (p4 ∨ ((p3 ∧ ((p4 ∧ (p4 ∨ p1)) ∧ ((p5 ∨ True) ∨ p5))) → (False ∨ (p2 ∧ p5))))) ∨ p5) ∨ (p3 → p3))) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_60881408658115488499514960572 : ((True ∧ (p1 → (p4 ∧ ((((p3 ∧ p3) → p5) ∧ ((p3 → (((p4 ∨ False) ∨ p4) → (False ∨ (False ∨ (p4 → p2))))) ∧ p4)) ∧ p5)))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_138747210719221620176881107744 : ((((p4 ∧ (False → p3)) ∧ (p4 → (p3 ∧ (((p3 ∨ p5) ∧ (True → False)) ∨ ((p4 ∧ (p4 → False)) ∧ p3))))) ∧ True) → (p1 → (False ∨ p2))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Conjunctions on the left can always be decomposed.
  let h3 := h1.left
  let h4 := h1.right
  -- Conjunctions on the left can always be decomposed.
  let h5 := h3.left
  let h6 := h3.right
  -- Conjunctions on the left can always be decomposed.
  let h7 := h5.left
  let h8 := h5.right
  -- We want to use the implication h6 based on <expert-advice>. So we show its premise.
  have h9 : p4 := by
    -- One of the premise coincides with the conclusion.
    exact h7
  -- We have shown the premise of h6, we can now drive its conclusion.
  let h10 := h6 h9
  -- We need to get the right conjuct of h10 based on <expert-advice>.
  let h11 := h10.right
  -- Disjunctions on the left can always be decomposed.
  cases h11
  case inl h12 =>
    -- Conjunctions on the left can always be decomposed.
    let h13 := h12.left
    let h14 := h12.right
    -- Disjunctions on the left can always be decomposed.
    cases h13
    case inl h15 =>
      -- We want to use the implication h14 based on <expert-advice>. So we show its premise.
      have h16 : True := by
        -- True on the right can always be proven directly.
        apply True.intro
      -- We have shown the premise of h14, we can now drive its conclusion.
      let h17 := h14 h16
      -- False on the left can always be used.
      apply False.elim h17
    case inr h18 =>
      -- We want to use the implication h14 based on <expert-advice>. So we show its premise.
      have h19 : True := by
        -- True on the right can always be proven directly.
        apply True.intro
      -- We have shown the premise of h14, we can now drive its conclusion.
      let h20 := h14 h19
      -- False on the left can always be used.
      apply False.elim h20
  case inr h21 =>
    -- Conjunctions on the left can always be decomposed.
    let h22 := h21.left
    let h23 := h21.right
    -- Conjunctions on the left can always be decomposed.
    let h24 := h22.left
    let h25 := h22.right
    -- We want to use the implication h25 based on <expert-advice>. So we show its premise.
    have h26 : p4 := by
      -- One of the premise coincides with the conclusion.
      exact h24
    -- We have shown the premise of h25, we can now drive its conclusion.
    let h27 := h25 h26
    -- False on the left can always be used.
    apply False.elim h27



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_675606449619126640746870756444 : (((((((p4 → (p5 ∨ p5)) → p2) ∨ ((True ∨ (p1 ∧ ((p2 → p4) → p1))) → p1)) ∨ (p3 ∧ p4)) ∧ (p3 ∨ (True ∨ (p2 ∧ p4)))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_207933567432462883212264070109 : (((p4 ∨ (p5 ∧ True)) ∧ (p5 ∨ True)) → ((p5 → p3) → (((p2 ∨ (((p1 → p2) → p4) ∧ True)) → p3) → (((p5 → p2) → p3) ∨ p3)))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Implications on the right can always be decomposed.
  intro h3
  -- Conjunctions on the left can always be decomposed.
  let h4 := h1.left
  let h5 := h1.right
  -- Disjunctions on the left can always be decomposed.
  cases h4
  case inl h6 =>
    -- Disjunctions on the left can always be decomposed.
    cases h5
    case inl h7 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
      have h8 : p5 := by
        -- One of the premise coincides with the conclusion.
        exact h7
      -- We have shown the premise of h2, we can now drive its conclusion.
      let h9 := h2 h8
      -- One of the premise coincides with the conclusion.
      exact h9
    case inr h10 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- We want to use the implication h3 based on <expert-advice>. So we show its premise.
      have h11 : (p2 ∨ (((p1 → p2) → p4) ∧ True)) := by
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- Conjunctions on the right can always be decomposed.
        apply And.intro
        -- Implications on the right can always be decomposed.
        intro h12
        -- One of the premise coincides with the conclusion.
        exact h6
        -- True on the right can always be proven directly.
        apply True.intro
      -- We have shown the premise of h3, we can now drive its conclusion.
      let h13 := h3 h11
      -- One of the premise coincides with the conclusion.
      exact h13
  case inr h14 =>
    -- Conjunctions on the left can always be decomposed.
    let h15 := h14.left
    let h16 := h14.right
    -- Disjunctions on the left can always be decomposed.
    cases h5
    case inl h17 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
      have h18 : p5 := by
        -- One of the premise coincides with the conclusion.
        exact h17
      -- We have shown the premise of h2, we can now drive its conclusion.
      let h19 := h2 h18
      -- One of the premise coincides with the conclusion.
      exact h19
    case inr h20 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
      have h21 : p5 := by
        -- One of the premise coincides with the conclusion.
        exact h15
      -- We have shown the premise of h2, we can now drive its conclusion.
      let h22 := h2 h21
      -- One of the premise coincides with the conclusion.
      exact h22



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_299150452167264474902542362225 : (False ∨ (((p2 ∧ ((((((p1 ∨ p4) → (((p1 → p3) → False) ∨ p3)) ∧ p4) ∨ (False ∨ ((p3 → p5) ∨ p1))) → False) ∨ p3)) ∨ False) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_41372125034252520694450554570 : (((((p1 → False) → ((p1 → (p2 ∨ True)) → ((p3 ∧ False) → (p3 → (p1 ∧ p2))))) → (p3 → (((True → False) ∧ p5) ∨ p4))) ∨ p2) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_191996784419733862633894487156 : ((p1 → (((p3 → (p4 ∨ p1)) ∨ p2) ∧ (p2 ∨ p3))) ∨ (True → (((((p1 ∨ p4) ∧ False) ∨ p4) ∨ (True ∨ True)) ∨ (p4 ∧ (p4 ∧ p1))))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
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
theorem thm_5_vars_178938033477218791824292984077 : (((p1 ∧ True) ∨ (((p2 ∨ False) → ((p4 ∧ (False ∨ p1)) ∨ p5)) ∧ p2)) ∨ (p1 → (p1 → (p2 ∨ ((((False → True) ∧ p3) → p4) → p1))))) := by
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
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_112947801788706017059608260089 : (((True ∧ (((p3 ∧ p4) ∨ ((p5 → (p3 ∧ (p2 ∧ (((p4 → False) ∧ p3) → p2)))) ∧ (p2 ∨ p5))) ∨ (p3 ∨ p3))) → p3) ∨ (True ∧ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_319044124445055456640380821195 : (p4 ∨ ((((((p5 ∨ ((True ∨ p4) → p3)) → p3) ∧ True) ∨ p1) ∧ (p3 → (((False ∨ p3) ∨ p2) → p1))) ∨ (True ∨ ((True ∧ p1) → p1)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_225107322657799695345753488114 : (((p2 ∧ p2) ∧ p1) ∨ (((((p3 → p5) ∨ (p3 ∨ p3)) ∨ ((((p1 ∧ p5) ∧ False) ∧ (p2 ∨ True)) ∨ p1)) → (p4 ∧ (False ∧ p2))) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_224094168482009129236023998692 : ((p5 ∨ (p4 ∨ True)) ∧ (p5 ∨ (((p2 ∧ (((p3 ∨ True) ∧ p3) → (p5 → ((p1 → p1) ∧ (p2 → p1))))) ∨ (False → (False ∨ p1))) ∨ p1))) := by
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
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_58357018011134670991875403510 : (((p1 ∨ True) ∧ (((p4 ∨ ((((p3 → (p3 → False)) ∧ p4) ∨ p3) → (False ∨ p2))) ∨ False) → (((p1 ∨ p1) ∨ p2) → (p4 ∨ p2)))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_156750403971011390277349515156 : ((((p3 → (p1 → p2)) ∨ (p4 ∨ ((p1 ∧ (p1 ∨ p1)) ∧ (p3 ∨ ((p2 ∨ True) → p1))))) ∧ p1) ∨ (False → ((True ∧ (p5 ∧ p3)) ∨ False))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_180082782320576727874097833263 : (((((((p4 → p3) → (p5 ∨ True)) ∨ (True ∧ True)) ∧ True) ∧ p3) → p2) → (((((True → p3) → p1) ∧ True) → p5) ∨ (p5 → (p5 ∨ False)))) := by
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



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_147491375327386537335163370557 : (((p5 ∧ (True ∧ (((False ∧ (p2 ∧ ((p4 → ((p1 ∨ False) ∧ (p4 → False))) → p2))) ∧ True) ∨ p5))) ∨ p1) ∨ ((p4 → p1) ∨ (False → True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_608215362635784432204926624402 : ((((((p2 → ((p2 ∧ ((((p4 ∨ p2) ∧ (p1 ∧ p5)) ∧ (p3 → False)) → False)) → (((p5 ∧ p4) ∨ False) ∨ False))) ∧ p5) ∨ True) ∨ p5) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_321189242759684129359240014615 : (p4 ∨ (p3 ∨ (((False ∧ False) ∧ (True ∧ (p4 ∧ (True ∧ (((True → ((p3 → False) ∧ True)) ∨ p3) → p3))))) ∨ ((True → p2) ∨ (True ∨ p3))))) := by
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



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_42201518074001004881204252795 : (((True ∧ (p3 ∧ ((((p4 ∨ True) → (p3 ∨ p2)) ∨ (p2 ∧ (p4 ∧ (p4 → p3)))) → (((True ∨ False) ∨ (p2 ∧ p1)) ∧ False)))) ∨ True) ∨ p3) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_612257838078832928857501484753 : ((((((p3 → False) ∧ ((p2 → ((p4 → p2) → p5)) → (True → ((p4 ∨ (((p2 → p4) ∨ p2) ∨ p1)) ∧ p3)))) ∧ (p4 ∨ False)) ∨ p2) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_166313109180361819152024531683 : ((p5 ∧ ((((p2 → p5) ∨ (p5 ∨ (p2 ∨ p2))) ∨ ((p4 ∧ False) ∨ (p4 → p4))) ∨ p5)) ∨ (((True ∧ p4) → (p5 ∧ p2)) ∨ (p2 ∨ True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_196837429160331094036877275509 : (((p4 ∧ ((p5 → True) ∧ (p3 ∨ p1))) ∧ p1) ∨ (p2 ∨ ((p5 ∧ (((True ∨ p5) ∨ p2) → (p4 → (True ∧ ((p5 ∨ False) → p5))))) → p5))) := by
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
theorem thm_5_vars_659140917582402371375546111188 : ((((p3 → ((((p5 ∧ p5) ∧ (False ∧ (p5 ∧ (True ∧ ((p4 ∧ ((p1 ∨ False) → p5)) ∧ p2))))) ∨ p4) ∨ (False ∨ p3))) ∨ (p3 ∨ p1)) ∨ p1) ∧ True) := by
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
  -- One of the premise coincides with the conclusion.
  exact h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_218089695906215356822582607156 : (((True → p3) ∧ (True → False)) → ((((p3 ∨ ((True → (p2 ∨ (p3 → p4))) ∧ p3)) ∧ (True ∧ ((p3 ∨ p2) ∧ p1))) ∨ (p3 → p5)) → False)) := by
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
      -- Conjunctions on the left can always be decomposed.
      let h7 := h5.left
      let h8 := h5.right
      -- Conjunctions on the left can always be decomposed.
      let h9 := h8.left
      let h10 := h8.right
      -- Disjunctions on the left can always be decomposed.
      cases h9
      case inl h11 =>
        -- Conjunctions on the left can always be decomposed.
        let h12 := h1.left
        let h13 := h1.right
        -- We want to use the implication h13 based on <expert-advice>. So we show its premise.
        have h14 : True := by
          -- True on the right can always be proven directly.
          apply True.intro
        -- We have shown the premise of h13, we can now drive its conclusion.
        let h15 := h13 h14
        -- False on the left can always be used.
        apply False.elim h15
      case inr h16 =>
        -- Conjunctions on the left can always be decomposed.
        let h17 := h1.left
        let h18 := h1.right
        -- We want to use the implication h18 based on <expert-advice>. So we show its premise.
        have h19 : True := by
          -- True on the right can always be proven directly.
          apply True.intro
        -- We have shown the premise of h18, we can now drive its conclusion.
        let h20 := h18 h19
        -- False on the left can always be used.
        apply False.elim h20
    case inr h21 =>
      -- Conjunctions on the left can always be decomposed.
      let h22 := h21.left
      let h23 := h21.right
      -- Conjunctions on the left can always be decomposed.
      let h24 := h5.left
      let h25 := h5.right
      -- Conjunctions on the left can always be decomposed.
      let h26 := h25.left
      let h27 := h25.right
      -- Disjunctions on the left can always be decomposed.
      cases h26
      case inl h28 =>
        -- Conjunctions on the left can always be decomposed.
        let h29 := h1.left
        let h30 := h1.right
        -- We want to use the implication h30 based on <expert-advice>. So we show its premise.
        have h31 : True := by
          -- True on the right can always be proven directly.
          apply True.intro
        -- We have shown the premise of h30, we can now drive its conclusion.
        let h32 := h30 h31
        -- False on the left can always be used.
        apply False.elim h32
      case inr h33 =>
        -- Conjunctions on the left can always be decomposed.
        let h34 := h1.left
        let h35 := h1.right
        -- We want to use the implication h35 based on <expert-advice>. So we show its premise.
        have h36 : True := by
          -- True on the right can always be proven directly.
          apply True.intro
        -- We have shown the premise of h35, we can now drive its conclusion.
        let h37 := h35 h36
        -- False on the left can always be used.
        apply False.elim h37
  case inr h38 =>
    -- Conjunctions on the left can always be decomposed.
    let h39 := h1.left
    let h40 := h1.right
    -- We want to use the implication h40 based on <expert-advice>. So we show its premise.
    have h41 : True := by
      -- True on the right can always be proven directly.
      apply True.intro
    -- We have shown the premise of h40, we can now drive its conclusion.
    let h42 := h40 h41
    -- False on the left can always be used.
    apply False.elim h42



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_234395495343131328285672702593 : ((p1 → (p2 → True)) → (((True → p2) ∧ False) ∨ (((p3 ∨ False) → p5) ∨ (((p1 → (p2 ∨ (True → p1))) → p4) → ((False ∧ p4) → False))))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
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
theorem thm_5_vars_599629778491056289780339950575 : (((((True → p4) ∨ ((True ∧ p3) ∨ (p2 ∧ (((p2 ∧ (p3 → p3)) ∧ (False → ((False ∧ (False → p5)) ∧ (p2 → p5)))) → p4)))) ∧ p5) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_689398311599315396488044704153 : ((((((p1 → p4) ∧ (True ∧ ((((False ∨ p1) ∨ False) ∧ p5) → p1))) → (p3 ∧ p4)) ∨ (p5 ∨ (False → (p3 → (p2 ∨ (p5 ∧ p3)))))) ∨ p2) ∧ True) := by
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
  -- Implications on the right can always be decomposed.
  intro h2
  -- False on the left can always be used.
  apply False.elim h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_208188603781651859998881754041 : (((p2 ∨ (p2 ∧ p3)) → (p1 ∧ p4)) → ((p4 ∨ (True ∧ (p4 ∧ False))) → ((p5 → (((p1 ∧ p1) ∨ True) → p2)) ∨ ((p1 → p1) ∨ p4)))) := by
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
    -- One of the premise coincides with the conclusion.
    exact h3
  case inr h4 =>
    -- Conjunctions on the left can always be decomposed.
    let h5 := h4.left
    let h6 := h4.right
    -- Conjunctions on the left can always be decomposed.
    let h7 := h6.left
    let h8 := h6.right
    -- False on the left can always be used.
    apply False.elim h8



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_648019023735325104386989660650 : (((((((True → p2) ∧ (True → ((p2 ∨ p5) → ((p1 → p1) → p2)))) ∧ ((p3 ∨ (False ∧ (p2 ∧ True))) ∨ True)) ∧ p4) ∧ (p2 ∧ p4)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_84076870498134965270460807734 : (((((p2 ∧ p3) → ((True → p5) → (False → p4))) → (p4 ∧ (p2 ∧ (p5 ∧ False)))) ∧ ((((p3 ∨ p2) → (p5 → False)) ∨ True) ∨ p5)) → False) := by
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
      -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
      have h6 : ((p2 ∧ p3) → ((True → p5) → (False → p4))) := by
        -- Implications on the right can always be decomposed.
        intro h7
        -- Implications on the right can always be decomposed.
        intro h8
        -- Implications on the right can always be decomposed.
        intro h9
        -- False on the left can always be used.
        apply False.elim h9
      -- We have shown the premise of h2, we can now drive its conclusion.
      let h10 := h2 h6
      -- We need to get the right conjuct of h10 based on <expert-advice>.
      let h11 := h10.right
      -- We need to get the right conjuct of h11 based on <expert-advice>.
      let h12 := h11.right
      -- We need to get the right conjuct of h12 based on <expert-advice>.
      let h13 := h12.right
      -- False on the left can always be used.
      apply False.elim h13
    case inr h14 =>
      -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
      have h15 : ((p2 ∧ p3) → ((True → p5) → (False → p4))) := by
        -- Implications on the right can always be decomposed.
        intro h16
        -- Implications on the right can always be decomposed.
        intro h17
        -- Implications on the right can always be decomposed.
        intro h18
        -- False on the left can always be used.
        apply False.elim h18
      -- We have shown the premise of h2, we can now drive its conclusion.
      let h19 := h2 h15
      -- We need to get the right conjuct of h19 based on <expert-advice>.
      let h20 := h19.right
      -- We need to get the right conjuct of h20 based on <expert-advice>.
      let h21 := h20.right
      -- We need to get the right conjuct of h21 based on <expert-advice>.
      let h22 := h21.right
      -- False on the left can always be used.
      apply False.elim h22
  case inr h23 =>
    -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
    have h24 : ((p2 ∧ p3) → ((True → p5) → (False → p4))) := by
      -- Implications on the right can always be decomposed.
      intro h25
      -- Implications on the right can always be decomposed.
      intro h26
      -- Implications on the right can always be decomposed.
      intro h27
      -- False on the left can always be used.
      apply False.elim h27
    -- We have shown the premise of h2, we can now drive its conclusion.
    let h28 := h2 h24
    -- We need to get the right conjuct of h28 based on <expert-advice>.
    let h29 := h28.right
    -- We need to get the right conjuct of h29 based on <expert-advice>.
    let h30 := h29.right
    -- We need to get the right conjuct of h30 based on <expert-advice>.
    let h31 := h30.right
    -- False on the left can always be used.
    apply False.elim h31



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_181443701952725260966985274826 : ((p3 ∨ (((p2 ∧ p2) ∧ True) ∨ ((p5 ∧ p3) ∧ ((p2 → False) ∧ p4)))) → (((p2 ∧ ((p4 ∧ p5) ∨ p3)) ∨ p5) ∨ ((False ∧ p4) → p2))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h2 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h3
    -- Conjunctions on the left can always be decomposed.
    let h4 := h3.left
    let h5 := h3.right
    -- False on the left can always be used.
    apply False.elim h4
  case inr h6 =>
    -- Disjunctions on the left can always be decomposed.
    cases h6
    case inl h7 =>
      -- Conjunctions on the left can always be decomposed.
      let h8 := h7.left
      let h9 := h7.right
      -- Conjunctions on the left can always be decomposed.
      let h10 := h8.left
      let h11 := h8.right
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Implications on the right can always be decomposed.
      intro h12
      -- Conjunctions on the left can always be decomposed.
      let h13 := h12.left
      let h14 := h12.right
      -- False on the left can always be used.
      apply False.elim h13
    case inr h15 =>
      -- Conjunctions on the left can always be decomposed.
      let h16 := h15.left
      let h17 := h15.right
      -- Conjunctions on the left can always be decomposed.
      let h18 := h16.left
      let h19 := h16.right
      -- Conjunctions on the left can always be decomposed.
      let h20 := h17.left
      let h21 := h17.right
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- One of the premise coincides with the conclusion.
      exact h18



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_257474520646111736807795414252 : ((p3 ∨ True) → (p4 ∨ ((((p2 → False) ∧ p3) ∧ p4) → (p4 ∧ (((False ∨ True) ∧ ((False ∨ (p5 ∧ True)) ∨ (p3 ∨ True))) ∨ (p4 → p2)))))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h2 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h3
    -- Conjunctions on the right can always be decomposed.
    apply And.intro
    -- Conjunctions on the left can always be decomposed.
    let h4 := h3.left
    let h5 := h3.right
    -- Conjunctions on the left can always be decomposed.
    let h6 := h4.left
    let h7 := h4.right
    -- One of the premise coincides with the conclusion.
    exact h5
    -- Conjunctions on the left can always be decomposed.
    let h8 := h3.left
    let h9 := h3.right
    -- Conjunctions on the left can always be decomposed.
    let h10 := h8.left
    let h11 := h8.right
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Conjunctions on the right can always be decomposed.
    apply And.intro
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- One of the premise coincides with the conclusion.
    exact h11
  case inr h12 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h13
    -- Conjunctions on the right can always be decomposed.
    apply And.intro
    -- Conjunctions on the left can always be decomposed.
    let h14 := h13.left
    let h15 := h13.right
    -- Conjunctions on the left can always be decomposed.
    let h16 := h14.left
    let h17 := h14.right
    -- One of the premise coincides with the conclusion.
    exact h15
    -- Conjunctions on the left can always be decomposed.
    let h18 := h13.left
    let h19 := h13.right
    -- Conjunctions on the left can always be decomposed.
    let h20 := h18.left
    let h21 := h18.right
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Conjunctions on the right can always be decomposed.
    apply And.intro
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- One of the premise coincides with the conclusion.
    exact h21



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_703273932734228547397687855391 : ((((p3 ∧ ((True ∨ p1) ∧ (((p4 → p4) → True) ∧ True))) ∨ ((p4 → p3) ∧ (p4 ∧ (p1 → ((p1 ∧ (False → p1)) → (p4 ∧ p4)))))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_56634007706547931825487895601 : ((((p5 ∧ True) ∧ p5) ∧ ((((p4 ∨ ((p4 ∨ p5) → (p3 ∨ (p5 → (p1 ∧ p3))))) ∧ ((True → p3) → (p5 → False))) ∧ False) ∨ p4)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_787705497399359532156485177107 : (((p4 ∨ (p5 ∨ (((((False → (p5 ∧ (((((p1 → p5) ∧ (True ∧ False)) ∨ p4) ∧ True) ∧ False))) ∧ p2) → False) ∨ p4) ∨ (False → p5)))) ∨ p2) ∧ True) := by
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
  -- False on the left can always be used.
  apply False.elim h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_37435159896898485550091447681 : (((((p3 ∧ (((((p4 ∨ (p1 ∨ p4)) → (p4 → False)) ∨ (p3 → True)) ∧ p5) ∨ False)) ∧ ((p4 ∧ p5) → (p2 ∨ p5))) ∨ True) ∧ p5) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_337757923664087556283707446805 : (p1 → ((((p5 → ((p4 → p3) → False)) ∧ (p5 ∨ (p2 ∧ ((p1 → p2) ∧ p5)))) ∨ True) ∨ (True ∧ (p5 ∧ (((p3 → p1) ∧ p5) ∨ p5))))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_187812349156997917426880145892 : ((p4 → ((p1 ∨ (False ∧ (((p4 → p1) → p2) ∨ p4))) → False)) → ((p2 ∨ ((p5 ∨ p3) → (True ∨ (p3 → False)))) ∨ ((p4 ∧ p3) ∧ p5))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
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
theorem thm_5_vars_47327821587888980922934855873 : ((((False → (p4 ∧ p1)) → ((((p3 → p2) ∨ p5) → p3) ∧ (p5 ∧ ((p5 ∧ p1) → ((True ∨ (p1 ∨ False)) ∧ p1))))) ∨ (p3 ∨ False)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_340829929030837177617642390161 : (p2 → (((((((True ∨ False) ∨ ((p2 ∨ ((((False ∧ p2) ∨ (p4 ∧ False)) → p5) ∨ p4)) ∨ p4)) → p3) → p3) ∨ False) → (p1 ∨ False)) ∨ True)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_301389967453572089905547528283 : (False ∨ ((p3 ∧ (p5 ∨ (p5 ∧ True))) ∨ ((False ∨ (((False → (p5 ∨ (True ∨ ((p5 → True) → (p1 ∧ p1))))) ∨ p3) ∨ p5)) → (p3 ∨ True)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
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
    -- Disjunctions on the left can always be decomposed.
    cases h3
    case inl h4 =>
      -- Disjunctions on the left can always be decomposed.
      cases h4
      case inl h5 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- True on the right can always be proven directly.
        apply True.intro
      case inr h6 =>
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- One of the premise coincides with the conclusion.
        exact h6
    case inr h7 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- True on the right can always be proven directly.
      apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_114016400473540138565274536378 : ((((((p3 ∧ (p3 → p2)) → (p1 ∧ ((p5 ∨ ((True ∨ p1) ∧ (p1 ∨ p3))) ∧ p2))) → p4) ∨ p2) ∨ ((p5 ∨ True) ∨ True)) ∨ (p1 → p5)) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_114677499802407619888699588583 : (((p4 ∧ (((p5 → (((True → (p5 → True)) ∧ (p1 → p5)) ∨ p2)) ∨ True) → False)) ∨ ((False ∨ (False → (p5 → False))) ∨ p4)) ∨ (p4 ∧ p1)) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
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
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_50438268968263621254845977074 : (((False ∨ ((False ∨ (p4 ∨ (p2 ∨ (((p4 ∨ False) ∧ ((p4 ∧ (p3 ∨ p1)) ∧ False)) → p3)))) ∧ p5)) ∨ ((p5 → p4) → (p4 ∧ True))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_138806688359359771275801209988 : (((True ∧ (True ∨ ((((p5 → p1) → (p1 → p2)) → ((p2 ∧ ((False → p3) ∧ (True ∨ True))) ∧ False)) ∨ p5))) ∧ p4) → ((True → p3) ∨ p4)) := by
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
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h3
  case inr h7 =>
    -- Disjunctions on the left can always be decomposed.
    cases h7
    case inl h8 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- One of the premise coincides with the conclusion.
      exact h3
    case inr h9 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- One of the premise coincides with the conclusion.
      exact h3



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_320504245670435738314269759889 : (p4 ∨ (True ∧ (((((p5 ∨ p5) ∨ (((p4 ∨ p1) ∧ p4) → (False ∨ p1))) ∧ p4) → ((p5 ∧ p5) ∨ (p2 → ((p5 → False) ∨ True)))) ∨ p2))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- True on the right can always be proven directly.
  apply True.intro
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
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- Conjunctions on the right can always be decomposed.
      apply And.intro
      -- One of the premise coincides with the conclusion.
      exact h5
      -- One of the premise coincides with the conclusion.
      exact h5
    case inr h6 =>
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- Conjunctions on the right can always be decomposed.
      apply And.intro
      -- One of the premise coincides with the conclusion.
      exact h6
      -- One of the premise coincides with the conclusion.
      exact h6
  case inr h7 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h8
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_621399932521088980049070323890 : ((((True ∧ (p3 ∨ ((p1 ∧ ((p5 ∧ p2) → (p3 ∧ (p3 → (True ∧ p1))))) → ((p2 ∨ p4) ∨ ((p5 ∧ True) ∨ (p4 → p5)))))) ∨ True) ∨ p4) ∧ True) := by
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
theorem thm_5_vars_48810097581461817609025267614 : (((p3 ∧ (((((((p5 ∧ p4) ∨ (p3 ∧ p5)) ∨ (p2 ∨ (p5 → True))) ∨ (False → p2)) ∨ False) → p1) ∧ p1)) ∧ ((False ∨ True) ∧ True)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_116987806529149042666997181474 : (((p5 ∧ p5) → ((((True ∧ (True → (p5 ∧ (False → p4)))) ∨ (p2 ∨ p2)) ∧ (True ∨ (p5 ∧ ((p1 ∨ p5) ∧ p5)))) → False)) ∨ (False → p4)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_172210989288122841539751054758 : ((((p1 ∨ (p3 ∧ p5)) → ((False ∧ (p5 → p2)) ∧ True)) → ((p2 ∨ p4) → False)) ∨ (p5 → ((p5 → p1) → (((p2 ∧ p5) ∧ p3) → p5)))) := by
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
  -- Conjunctions on the left can always be decomposed.
  let h6 := h4.left
  let h7 := h4.right
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_213785710024023396159969534255 : (((p1 ∧ (p2 ∧ False)) ∨ p2) ∨ ((p2 → (p4 → ((False ∧ (p1 ∨ p2)) ∨ (p2 ∨ p3)))) ∨ (p2 ∨ (((p2 → p3) ∧ True) ∨ (p2 → p5))))) := by
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
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_119432281954018521967243705783 : ((p4 → (((p2 → p1) ∧ (((p4 ∧ (True ∧ ((p1 ∧ p5) ∨ (p5 ∨ (p5 ∨ p2))))) ∨ False) ∧ p2)) ∨ (p1 → (False → p4)))) ∨ (p1 ∨ p2)) := by
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
  apply False.elim h3



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_167200281917237202893223502372 : (((p4 ∧ (((((False ∨ p1) ∨ True) ∧ True) ∧ False) ∨ (p5 → ((p3 ∧ p5) ∧ True)))) ∨ p4) → (p1 → ((p5 → False) ∨ ((False → p3) → p1)))) := by
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
    cases h5
    case inl h6 =>
      -- Conjunctions on the left can always be decomposed.
      let h7 := h6.left
      let h8 := h6.right
      -- Conjunctions on the left can always be decomposed.
      let h9 := h7.left
      let h10 := h7.right
      -- Disjunctions on the left can always be decomposed.
      cases h9
      case inl h11 =>
        -- Disjunctions on the left can always be decomposed.
        cases h11
        case inl h12 =>
          -- False on the left can always be used.
          apply False.elim h12
        case inr h13 =>
          -- False on the left can always be used.
          apply False.elim h8
      case inr h14 =>
        -- False on the left can always be used.
        apply False.elim h8
    case inr h15 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Implications on the right can always be decomposed.
      intro h16
      -- One of the premise coincides with the conclusion.
      exact h2
  case inr h17 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h18
    -- One of the premise coincides with the conclusion.
    exact h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_228917209138031032715809375391 : ((p4 ∨ (False ∨ p4)) ∨ (True → ((p4 ∨ (p5 → (p4 ∨ (((p4 ∧ p1) → False) → (((False ∧ p2) ∧ p4) → (False → (False → p2))))))) ∨ False))) := by
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
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h3
  -- Implications on the right can always be decomposed.
  intro h4
  -- Implications on the right can always be decomposed.
  intro h5
  -- Implications on the right can always be decomposed.
  intro h6
  -- False on the left can always be used.
  apply False.elim h6



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_712497462940468443542244693354 : ((((((p5 → True) → p4) ∨ (p1 ∧ p3)) ∨ (((p5 ∧ (p3 ∧ p2)) → (((p3 ∨ (p4 ∧ True)) → (True → (p5 ∧ p1))) ∨ True)) ∧ True)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_61209017462486015190006201445 : ((False ∧ ((False → True) → ((True → (p2 ∧ True)) → ((False → True) → (p2 → ((True → ((p4 → ((p5 ∧ p2) ∨ False)) → p2)) → p1)))))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_54438257641327759617557568947 : ((((p5 ∨ ((p4 ∨ (False ∨ p4)) → p2)) ∨ False) ∨ (True → (((p5 ∧ (False → p2)) ∨ False) ∨ (((p4 → p5) ∧ True) ∧ (False ∧ True))))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_52167477349385284960091595045 : ((((p5 ∨ ((True → ((p4 → False) → p2)) ∧ p5)) ∨ (True → (p4 ∨ (False ∨ p4)))) → (p3 ∧ (((True → p3) → False) → (p5 ∨ p3)))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_695842642199797251527553741115 : (((((p1 ∨ False) ∧ (p4 ∨ ((((p3 ∨ (True ∧ p2)) → p5) ∧ p4) → p5))) → ((p2 ∨ (p4 → (p3 → False))) → (p5 ∨ (p2 → p1)))) ∨ p1) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
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
    cases h4
    case inl h6 =>
      -- Disjunctions on the left can always be decomposed.
      cases h5
      case inl h7 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- Implications on the right can always be decomposed.
        intro h8
        -- One of the premise coincides with the conclusion.
        exact h6
      case inr h9 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- Implications on the right can always be decomposed.
        intro h10
        -- One of the premise coincides with the conclusion.
        exact h6
    case inr h11 =>
      -- False on the left can always be used.
      apply False.elim h11
  case inr h12 =>
    -- Conjunctions on the left can always be decomposed.
    let h13 := h1.left
    let h14 := h1.right
    -- Disjunctions on the left can always be decomposed.
    cases h13
    case inl h15 =>
      -- Disjunctions on the left can always be decomposed.
      cases h14
      case inl h16 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- Implications on the right can always be decomposed.
        intro h17
        -- One of the premise coincides with the conclusion.
        exact h15
      case inr h18 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- Implications on the right can always be decomposed.
        intro h19
        -- One of the premise coincides with the conclusion.
        exact h15
    case inr h20 =>
      -- False on the left can always be used.
      apply False.elim h20
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_58904995931470385729043577013 : (((False ∧ p5) ∨ (True → ((p1 ∧ ((((p1 ∧ (p5 ∧ True)) → False) ∨ ((p3 ∨ p2) ∧ True)) ∧ (p2 ∨ (False ∨ (False → p1))))) ∧ p4))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_248258320901072584540494431970 : ((p2 ∨ p2) ∨ (((True → ((p1 → (((p4 ∨ ((p3 ∧ p5) ∨ False)) → p3) ∨ True)) → (p4 ∨ p1))) ∧ ((p5 ∨ (False ∧ p4)) → p1)) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_118463350133876578092893214758 : ((p3 ∨ ((True → ((p4 ∧ (p2 ∨ p3)) ∨ ((p2 ∧ ((p1 → (p4 → (p1 → p4))) → (p5 ∨ (True → False)))) → p5))) ∨ True)) ∨ (p1 → p5)) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_60030667867278790544558466641 : (((p1 ∨ p3) → ((((p5 ∧ ((False ∧ p5) ∨ (((p4 ∨ (p1 ∧ True)) ∨ p2) ∧ (((p3 → p1) → p3) ∧ p2)))) ∧ p5) ∧ False) ∨ True)) ∨ p2) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
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
theorem thm_5_vars_249094246673050239529416611221 : ((p4 ∨ p1) ∨ (p5 ∨ (((p5 → (p5 ∧ ((True ∧ p1) ∨ ((False → (((p5 ∨ p2) ∨ p1) ∨ ((p2 → p5) ∨ p3))) → p2)))) ∨ p2) ∨ True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_138361483009964348288125848557 : ((p4 → ((((((True → False) → True) ∨ True) → ((p1 ∨ (p5 ∨ (p3 ∨ p2))) ∨ p4)) ∨ p4) ∧ ((True ∨ p4) ∨ p2))) ∨ ((p3 ∨ True) → p1)) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h1
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_43687678538623790092277644080 : (((((((p3 → (p1 ∧ True)) ∧ (p2 → (p2 ∧ p4))) ∨ p4) → ((p1 ∧ (False → (True ∧ (False → p3)))) ∨ (p2 → True))) → p1) → p1) ∨ p4) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h2 : ((((p3 → (p1 ∧ True)) ∧ (p2 → (p2 ∧ p4))) ∨ p4) → ((p1 ∧ (False → (True ∧ (False → p3)))) ∨ (p2 → True))) := by
    -- Implications on the right can always be decomposed.
    intro h3
    -- Disjunctions on the left can always be decomposed.
    cases h3
    case inl h4 =>
      -- Conjunctions on the left can always be decomposed.
      let h5 := h4.left
      let h6 := h4.right
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Implications on the right can always be decomposed.
      intro h7
      -- True on the right can always be proven directly.
      apply True.intro
    case inr h8 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Implications on the right can always be decomposed.
      intro h9
      -- True on the right can always be proven directly.
      apply True.intro
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h10 := h1 h2
  -- One of the premise coincides with the conclusion.
  exact h10



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_46694911749130093207407413243 : (((p3 ∨ (((((p1 ∧ p4) ∨ True) → ((p3 → p2) ∨ p1)) → p3) ∨ ((p5 ∧ p2) → (p3 ∨ (p3 ∨ (True → p5)))))) ∧ (p4 → True)) ∨ p2) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
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
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h4
  -- One of the premise coincides with the conclusion.
  exact h2
  -- Implications on the right can always be decomposed.
  intro h5
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_37175485915449925553480273569 : (((((p4 ∧ ((False ∨ (True ∨ (((p4 → p1) → p3) → False))) ∨ p1)) ∧ ((p3 → (((p4 → True) ∧ p5) ∧ p3)) → p4)) ∧ p3) ∧ p3) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_230756442651696183518242061824 : (((p5 → p5) ∧ p5) → ((((p1 ∧ ((p4 ∨ p4) ∨ p3)) ∨ p3) ∧ (p5 ∧ True)) ∨ ((p5 ∧ p5) ∨ (((p1 ∧ False) → p2) ∧ (p5 ∨ p1))))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- One of the premise coincides with the conclusion.
  exact h3
  -- One of the premise coincides with the conclusion.
  exact h3



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_634378104810883114799991398875 : ((((((True → (((((p3 → p4) ∨ (p2 → False)) ∧ p1) ∧ (p4 → (p2 ∨ (False ∧ p3)))) ∧ p3)) ∧ p3) ∧ ((False ∨ p5) ∧ p4)) → p2) ∨ p4) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
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
  cases h6
  case inl h8 =>
    -- False on the left can always be used.
    apply False.elim h8
  case inr h9 =>
    -- We want to use the implication h4 based on <expert-advice>. So we show its premise.
    have h10 : True := by
      -- True on the right can always be proven directly.
      apply True.intro
    -- We have shown the premise of h4, we can now drive its conclusion.
    let h11 := h4 h10
    -- We need to get the left conjuct of h11 based on <expert-advice>.
    let h12 := h11.left
    -- We need to get the right conjuct of h12 based on <expert-advice>.
    let h13 := h12.right
    -- We want to use the implication h13 based on <expert-advice>. So we show its premise.
    have h14 : p4 := by
      -- One of the premise coincides with the conclusion.
      exact h7
    -- We have shown the premise of h13, we can now drive its conclusion.
    let h15 := h13 h14
    -- Disjunctions on the left can always be decomposed.
    cases h15
    case inl h16 =>
      -- One of the premise coincides with the conclusion.
      exact h16
    case inr h17 =>
      -- Conjunctions on the left can always be decomposed.
      let h18 := h17.left
      let h19 := h17.right
      -- False on the left can always be used.
      apply False.elim h18
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_345644209328665027407675213512 : (p3 → ((p3 ∧ ((p4 ∨ (p3 ∧ (p3 ∧ (False ∨ False)))) ∨ (False ∨ ((((p2 → ((True ∧ True) → p4)) ∧ p2) ∧ (False ∧ p4)) ∧ p5)))) ∨ p3)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_151684558689987152693406110680 : (((p1 → ((p1 ∨ (((True → p4) ∨ (((p5 ∨ p4) ∨ True) ∨ p5)) ∨ p4)) → False)) ∧ (True ∨ (False ∨ p4))) → ((p5 ∨ p3) ∨ (p1 ∨ True))) := by
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
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro
  case inr h5 =>
    -- Disjunctions on the left can always be decomposed.
    cases h5
    case inl h6 =>
      -- False on the left can always be used.
      apply False.elim h6
    case inr h7 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- True on the right can always be proven directly.
      apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_158436814045296058291803383384 : (((p1 ∨ p3) ∨ ((((p2 ∨ p4) ∧ (False ∧ p2)) ∧ (((p4 ∧ (p3 → p3)) ∨ True) → False)) ∧ p1)) ∨ (((p2 → (p2 ∨ p3)) → False) → False)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h2 : (p2 → (p2 ∨ p3)) := by
    -- Implications on the right can always be decomposed.
    intro h3
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- One of the premise coincides with the conclusion.
    exact h3
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h4 := h1 h2
  -- False on the left can always be used.
  apply False.elim h4



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_156686452452362212738706100788 : ((((((p2 ∧ p5) ∨ False) → ((((p5 ∨ p2) ∨ p5) ∧ (p2 → p1)) → True)) → (p2 ∧ p5)) ∧ p2) ∨ (p4 ∨ (((False → p4) ∨ p1) ∧ True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- False on the left can always be used.
  apply False.elim h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_165231077827922703105843739594 : ((((True → p4) ∧ (((False → p1) ∧ p4) ∨ ((False → (p5 ∨ p4)) → p2))) ∨ (p2 → p1)) ∨ (((((p3 ∨ p1) ∧ False) ∨ p1) ∨ p4) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_20553008969064432534687474160 : (((p4 → ((p4 → (p1 ∧ ((p5 ∨ (True ∧ False)) ∧ (p1 ∨ p3)))) → False)) → ((p2 ∧ True) → ((((p2 → p4) ∨ p1) ∧ True) ∨ p2))) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Conjunctions on the left can always be decomposed.
  let h3 := h2.left
  let h4 := h2.right
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h3
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_122723056501773046054723369211 : ((((p4 ∨ p1) ∨ (p1 ∧ ((False ∧ (p1 ∧ (((p5 → p3) → (p4 ∧ False)) ∨ p1))) ∨ (p3 ∨ (True ∧ p1))))) → (True ∧ p5)) → (p3 → p3)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- One of the premise coincides with the conclusion.
  exact h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_112274977705205517785146674928 : (((True → ((p3 → (p3 ∧ (((p3 ∨ False) ∧ (((p2 ∧ (True ∧ p5)) → p2) ∧ (True ∧ p5))) ∧ (p3 → True)))) → p3)) ∨ True) ∨ (p4 ∨ p5)) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_657715247101610227308406792465 : (((((p4 → False) → ((p2 ∧ p2) → ((p3 → (p5 ∨ ((((p1 ∨ False) ∧ p4) ∧ ((p4 → True) ∨ p5)) ∧ p5))) ∧ False))) ∨ (False → p5)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_119306284180685977126298715764 : ((p3 → (((((False → p1) ∧ ((p5 ∧ (p1 ∧ (p1 ∨ True))) ∨ (p5 ∧ False))) ∧ p3) → ((p5 → False) ∧ p2)) ∨ (True ∨ p3))) ∨ (True ∧ False)) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_621072798420453197001627517871 : (((((p2 → p3) → ((p2 ∧ (p4 ∧ (p2 ∧ ((p4 → ((True ∨ p3) ∧ False)) ∧ p2)))) ∧ ((p3 → (True ∨ (p5 ∨ False))) ∧ p3))) ∨ True) ∨ p3) ∧ True) := by
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



