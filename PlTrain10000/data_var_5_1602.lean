variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_134297469034351643710051303277 : ((((False ∨ p1) → (p4 ∨ (p5 ∧ (p4 ∧ ((((False ∧ (p4 ∨ p4)) ∨ p1) ∧ (p2 → p2)) ∨ (p5 ∧ False)))))) ∨ p2) ∨ ((True → p1) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_136140608295627072920428142611 : ((((p1 ∨ ((p5 ∨ p4) ∨ (False → p3))) → p1) → (((p1 → p5) → ((False ∧ p1) ∨ (p2 → p1))) ∨ (p3 ∧ True))) ∨ (p1 ∨ (p4 → p1))) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h2
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h3
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h4 : (p1 ∨ ((p5 ∨ p4) ∨ (False → p3))) := by
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h5
    -- False on the left can always be used.
    apply False.elim h5
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h6 := h1 h4
  -- One of the premise coincides with the conclusion.
  exact h6



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_315371209542257694213743198016 : (p3 ∨ ((p3 ∨ (True ∨ p5)) ∧ ((p5 ∧ (((p4 → False) ∧ p5) → (True → (p5 ∧ False)))) ∨ (((p2 ∨ False) ∨ p4) ∨ (False → (p5 ∧ p4)))))) := by
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
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
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
theorem thm_5_vars_116092950656548177228912338214 : ((((True → True) ∨ p3) ∧ (((((True ∧ p4) ∨ p5) ∧ p2) → ((True ∧ False) ∧ p3)) ∨ (p4 ∨ (True ∨ (True ∨ (True → p1)))))) ∨ (p2 → p3)) := by
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
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_45390820507887582479836682374 : (((p5 ∧ (((((p1 ∨ p3) → (True → (((p2 → ((p5 → True) → p1)) ∧ False) ∧ ((p5 ∨ p5) ∧ p4)))) ∧ p5) → p1) → p2)) → p3) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_351531776170594820558630924455 : (p4 → (((False ∧ (p4 ∧ (((p1 → p3) ∧ (False ∨ p5)) ∨ p4))) ∨ (p3 ∨ ((p3 → True) → p1))) ∨ ((False ∨ (p2 → p1)) → (p1 → p4)))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h2
  -- Implications on the right can always be decomposed.
  intro h3
  -- Disjunctions on the left can always be decomposed.
  cases h2
  case inl h4 =>
    -- False on the left can always be used.
    apply False.elim h4
  case inr h5 =>
    -- One of the premise coincides with the conclusion.
    exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_199037720317449432042633999307 : (((((True ∨ (True ∧ False)) ∨ p3) ∨ p3) ∧ p2) → (p5 ∨ (((True → False) ∧ True) ∨ ((((p2 ∧ (p3 ∨ p2)) → False) ∧ p5) ∨ (p3 → p2))))) := by
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
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- Implications on the right can always be decomposed.
        intro h7
        -- One of the premise coincides with the conclusion.
        exact h3
      case inr h8 =>
        -- Conjunctions on the left can always be decomposed.
        let h9 := h8.left
        let h10 := h8.right
        -- False on the left can always be used.
        apply False.elim h10
    case inr h11 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Implications on the right can always be decomposed.
      intro h12
      -- One of the premise coincides with the conclusion.
      exact h3
  case inr h13 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h14
    -- One of the premise coincides with the conclusion.
    exact h3



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_52548167817831057652641119894 : ((((((p2 → (p3 ∨ p1)) ∧ ((True ∧ p1) ∧ p5)) ∧ (p1 ∧ p3)) → p2) ∨ ((p1 ∧ True) ∨ (((p3 ∧ p4) ∧ (p3 ∨ False)) → p4))) ∨ p1) := by
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
  -- Conjunctions on the left can always be decomposed.
  let h4 := h2.left
  let h5 := h2.right
  -- Disjunctions on the left can always be decomposed.
  cases h3
  case inl h6 =>
    -- One of the premise coincides with the conclusion.
    exact h5
  case inr h7 =>
    -- False on the left can always be used.
    apply False.elim h7



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_706788842479618054180413219033 : ((((((p4 → (p3 ∨ p4)) → (p1 ∨ p3)) ∧ p4) ∨ ((((p2 ∨ (p5 → p1)) → False) → False) ∨ (True ∧ ((True ∨ p4) ∨ (p1 ∧ False))))) ∨ p1) ∧ True) := by
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
  -- True on the right can always be proven directly.
  apply True.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_710727773108112948190781896908 : ((((((p3 ∧ p1) ∨ p1) → (p5 ∨ p1)) ∧ (p4 → (((((False ∧ ((p5 ∧ p1) → (p4 ∨ (True ∧ p2)))) ∨ True) ∨ p2) ∨ True) → p1))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_63254322856049978317425597053 : ((p5 ∧ ((True ∧ ((p2 ∨ ((p3 ∧ True) → p3)) ∨ False)) ∧ (((p5 ∨ ((True ∨ (p2 ∨ p2)) → ((False → p4) → p4))) → False) ∨ p1))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_57667651446530496733452523517 : ((((True → p2) ∨ p1) → (((p2 ∨ p5) ∨ p3) → (p4 ∧ ((p4 → (p3 → ((False → ((False → (p5 ∨ p3)) ∨ p4)) ∨ False))) ∧ p1)))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_321292864950296354096095691995 : (p4 ∨ (p5 ∨ (((p2 ∧ (p1 ∨ (p4 ∧ ((False ∧ ((p1 ∨ True) ∨ ((True ∧ False) ∨ p4))) → ((False ∧ p3) ∧ p2))))) ∨ (p1 → True)) ∨ p4))) := by
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
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_647778200495636715687721389277 : ((((((((p2 → (p2 ∨ (((False → False) ∨ True) ∧ False))) → ((p3 ∨ p1) ∨ (p4 ∨ (p4 → p1)))) ∧ p3) ∧ p4) ∧ p1) ∧ (p4 ∧ p3)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_778027610126446162265611371067 : (((p1 ∨ ((False ∧ False) ∧ (p3 → (((True ∨ p5) → (p4 ∧ p2)) ∧ ((p2 → ((p2 ∨ (False ∨ p4)) → p1)) ∧ ((p5 ∨ p1) ∧ p2)))))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_111895798156326832806758289956 : (((((p4 ∨ False) ∧ (p1 ∨ (((p1 → (True ∧ p1)) → (p5 ∧ p5)) ∧ p5))) ∨ (True ∧ (p5 ∧ ((p2 ∧ True) → p4)))) ∨ p4) ∨ (p5 ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_310812233357320518292829832553 : (p2 ∨ ((p2 ∨ (False ∧ p2)) ∨ ((((((p3 ∨ p5) ∧ p5) ∧ p3) ∨ (p1 ∨ (True → False))) ∧ p4) ∨ ((p4 ∧ False) → (True ∨ (p4 ∧ p3)))))) := by
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
  -- False on the left can always be used.
  apply False.elim h3



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_190901119520532575674967799226 : (((p2 ∨ (True ∧ (p4 ∨ (p1 ∧ p2)))) → (p3 ∨ p4)) ∨ (((p3 ∧ ((p5 ∨ True) ∨ ((p1 ∧ p1) ∨ True))) → ((True → p1) ∧ p4)) → True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_346952554489134385185423519743 : (p3 → (((p1 ∨ (p3 ∧ p3)) → ((p2 ∧ p3) ∧ (False ∧ (True ∨ (False ∧ ((p1 ∧ p4) → p1)))))) → (((p5 ∧ (p4 → p1)) ∧ p2) ∨ False))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
  have h3 : (p1 ∨ (p3 ∧ p3)) := by
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Conjunctions on the right can always be decomposed.
    apply And.intro
    -- One of the premise coincides with the conclusion.
    exact h1
    -- One of the premise coincides with the conclusion.
    exact h1
  -- We have shown the premise of h2, we can now drive its conclusion.
  let h4 := h2 h3
  -- We need to get the right conjuct of h4 based on <expert-advice>.
  let h5 := h4.right
  -- We need to get the left conjuct of h5 based on <expert-advice>.
  let h6 := h5.left
  -- False on the left can always be used.
  apply False.elim h6



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_304021947126086763706007248324 : (p1 ∨ ((False ∧ (True → ((((False ∧ True) ∧ p4) ∨ p3) ∧ (p4 ∧ (((p4 ∧ (((p4 ∨ p5) ∧ p1) ∨ p1)) ∨ True) ∧ (p4 → p1)))))) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_152208407711524647679832824119 : ((((True → ((p1 → p2) ∨ p3)) ∨ p5) ∧ ((((p4 ∧ p3) → True) → p2) ∨ (((p5 ∧ True) ∧ False) ∨ p1))) → (((p4 ∧ p1) ∨ True) ∨ False)) := by
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
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- True on the right can always be proven directly.
      apply True.intro
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
        -- False on the left can always be used.
        apply False.elim h9
      case inr h12 =>
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- True on the right can always be proven directly.
        apply True.intro
  case inr h13 =>
    -- Disjunctions on the left can always be decomposed.
    cases h3
    case inl h14 =>
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- True on the right can always be proven directly.
      apply True.intro
    case inr h15 =>
      -- Disjunctions on the left can always be decomposed.
      cases h15
      case inl h16 =>
        -- Conjunctions on the left can always be decomposed.
        let h17 := h16.left
        let h18 := h16.right
        -- Conjunctions on the left can always be decomposed.
        let h19 := h17.left
        let h20 := h17.right
        -- False on the left can always be used.
        apply False.elim h18
      case inr h21 =>
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- True on the right can always be proven directly.
        apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_919108330791302836657820081420 : (((((((p3 ∧ p5) → p1) ∧ ((p4 → p2) ∧ p1)) ∧ (True → (p5 ∧ p3))) ∧ (((p3 ∧ p2) → True) ∨ (p1 ∧ (p1 ∨ (p2 ∧ p3))))) → p5) ∧ True) := by
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
  let h6 := h4.left
  let h7 := h4.right
  -- Conjunctions on the left can always be decomposed.
  let h8 := h7.left
  let h9 := h7.right
  -- Disjunctions on the left can always be decomposed.
  cases h3
  case inl h10 =>
    -- We want to use the implication h5 based on <expert-advice>. So we show its premise.
    have h11 : True := by
      -- True on the right can always be proven directly.
      apply True.intro
    -- We have shown the premise of h5, we can now drive its conclusion.
    let h12 := h5 h11
    -- We need to get the left conjuct of h12 based on <expert-advice>.
    let h13 := h12.left
    -- One of the premise coincides with the conclusion.
    exact h13
  case inr h14 =>
    -- Conjunctions on the left can always be decomposed.
    let h15 := h14.left
    let h16 := h14.right
    -- Disjunctions on the left can always be decomposed.
    cases h16
    case inl h17 =>
      -- We want to use the implication h5 based on <expert-advice>. So we show its premise.
      have h18 : True := by
        -- True on the right can always be proven directly.
        apply True.intro
      -- We have shown the premise of h5, we can now drive its conclusion.
      let h19 := h5 h18
      -- We need to get the left conjuct of h19 based on <expert-advice>.
      let h20 := h19.left
      -- One of the premise coincides with the conclusion.
      exact h20
    case inr h21 =>
      -- Conjunctions on the left can always be decomposed.
      let h22 := h21.left
      let h23 := h21.right
      -- We want to use the implication h5 based on <expert-advice>. So we show its premise.
      have h24 : True := by
        -- True on the right can always be proven directly.
        apply True.intro
      -- We have shown the premise of h5, we can now drive its conclusion.
      let h25 := h5 h24
      -- We need to get the left conjuct of h25 based on <expert-advice>.
      let h26 := h25.left
      -- One of the premise coincides with the conclusion.
      exact h26
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_249169925432465984743558715646 : ((p4 ∨ p3) ∨ ((((p2 ∨ ((False ∧ True) ∨ p1)) → (p5 → True)) → (((p3 ∧ (((p2 → p1) → (True ∨ True)) ∨ p1)) → p2) → p4)) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_66517266271441122803416793455 : ((True → (((True → (p3 ∨ (p1 ∨ ((((p2 ∨ ((p1 ∧ (p3 ∨ p1)) ∧ (p4 → p4))) ∨ p5) ∨ (p3 → p1)) ∧ p3)))) ∨ p1) → p3)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_660236591779754444766503146801 : ((((((p5 ∧ p3) ∧ ((((p3 → (False ∨ True)) ∨ (p4 → ((True ∧ (p1 ∧ True)) → False))) ∨ (False ∧ p2)) → p3)) ∨ True) → (p2 ∧ True)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_139439395313187744237443700144 : ((((((((True ∨ (((p2 → p5) ∨ (True ∧ p5)) ∧ (p2 → (p2 ∧ p1)))) ∧ p2) ∨ p2) ∨ p3) ∧ p4) ∨ True) → False) → (p1 → (p5 ∧ p4))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h3 : ((((((True ∨ (((p2 → p5) ∨ (True ∧ p5)) ∧ (p2 → (p2 ∧ p1)))) ∧ p2) ∨ p2) ∨ p3) ∧ p4) ∨ True) := by
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h4 := h1 h3
  -- False on the left can always be used.
  apply False.elim h4
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h5 : ((((((True ∨ (((p2 → p5) ∨ (True ∧ p5)) ∧ (p2 → (p2 ∧ p1)))) ∧ p2) ∨ p2) ∨ p3) ∧ p4) ∨ True) := by
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h6 := h1 h5
  -- False on the left can always be used.
  apply False.elim h6



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_350291178353730894694810208064 : (p4 → ((False ∨ (p5 ∧ (((False ∨ True) → ((p4 → (p1 ∨ p5)) ∨ p3)) ∨ (((p1 → p4) ∨ ((p1 ∧ (p3 → p1)) ∧ p5)) ∧ p2)))) ∨ True)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_152958403616022692327464372945 : ((p1 ∧ (((True → (((p1 ∨ ((p1 ∧ (p3 → True)) ∧ p5)) → False) → False)) ∨ ((p3 ∨ p3) → p4)) ∧ p3)) → (p4 → ((p2 ∨ p2) → p4))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Implications on the right can always be decomposed.
  intro h3
  -- Disjunctions on the left can always be decomposed.
  cases h3
  case inl h4 =>
    -- Conjunctions on the left can always be decomposed.
    let h5 := h1.left
    let h6 := h1.right
    -- Conjunctions on the left can always be decomposed.
    let h7 := h6.left
    let h8 := h6.right
    -- Disjunctions on the left can always be decomposed.
    cases h7
    case inl h9 =>
      -- One of the premise coincides with the conclusion.
      exact h2
    case inr h10 =>
      -- One of the premise coincides with the conclusion.
      exact h2
  case inr h11 =>
    -- Conjunctions on the left can always be decomposed.
    let h12 := h1.left
    let h13 := h1.right
    -- Conjunctions on the left can always be decomposed.
    let h14 := h13.left
    let h15 := h13.right
    -- Disjunctions on the left can always be decomposed.
    cases h14
    case inl h16 =>
      -- One of the premise coincides with the conclusion.
      exact h2
    case inr h17 =>
      -- One of the premise coincides with the conclusion.
      exact h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_766000139049908125500244632301 : (((p4 ∧ (((p2 ∨ p5) ∨ p5) ∧ ((p2 → ((p4 → p3) → p2)) ∧ ((p2 ∨ (p5 ∧ True)) ∧ ((p2 ∨ (p4 ∧ (True ∨ p3))) → False))))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_338481300403246083594404003523 : (p1 → ((False ∨ (p1 ∧ p1)) ∧ ((((p4 ∨ ((p5 → ((p3 ∨ p1) ∧ p5)) → (p2 ∧ (True ∨ p1)))) ∨ ((p2 ∧ p4) ∧ p4)) ∧ False) ∨ True))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- One of the premise coincides with the conclusion.
  exact h1
  -- One of the premise coincides with the conclusion.
  exact h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_736390184490498543257622438173 : ((((p1 → True) ∧ ((((((p2 ∧ False) ∧ (p1 ∨ (True ∧ p1))) → (p1 ∨ (p4 → p4))) ∨ True) ∨ False) → (((p2 ∨ False) ∧ p5) ∧ p4))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_184513872426152952553583900512 : (((p3 ∧ (((p2 ∨ p1) ∧ (True → p4)) → p2)) ∨ (p5 ∨ p5)) ∨ (p1 → ((False ∧ (p5 ∧ p2)) ∨ (((p3 ∨ p1) ∨ p1) ∨ (p3 → p2))))) := by
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
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_696289123030835484381229805996 : ((((False → (p2 ∧ (p3 ∧ ((((True ∨ p2) ∨ (True ∨ p1)) → p3) → p5)))) → (True ∧ ((((True ∨ p1) ∧ p2) ∨ p5) ∨ (p4 ∨ False)))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_115789095683194799995574412230 : (((((p3 ∧ p2) ∧ p1) ∨ p5) ∧ (p1 → (p1 ∧ ((p3 ∧ p2) ∧ ((p4 ∧ p3) ∧ ((((p2 → p4) ∨ p4) ∧ p4) ∧ p1)))))) ∨ (p3 → p3)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_211281966284612130195910104197 : (((p4 ∧ p5) ∨ (p3 → True)) ∧ (((p1 ∨ (p3 ∨ p2)) ∨ False) ∨ (p2 ∨ (p4 ∨ (((((True ∧ p1) → p3) → (p4 → p1)) ∨ True) ∨ False))))) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro
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
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_184529480665598575297799400962 : (((p4 → ((((p3 ∨ p3) ∨ p5) ∧ True) ∧ False)) ∨ (p3 ∨ p4)) ∨ (((((p2 ∨ p5) → (p5 ∧ (p3 ∨ p3))) ∧ p1) → p3) ∨ (True ∨ p2))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_114290998795193873288410134178 : ((((((p5 ∧ p4) ∧ p1) ∨ ((((p3 ∧ p2) → (p5 ∨ p3)) ∧ p4) ∨ p2)) ∧ (p2 ∧ p2)) ∧ ((p5 → p5) ∧ (p1 → False))) ∨ (True ∧ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_191828484068364824760170802508 : ((p3 ∨ ((((p1 → p2) → p3) ∨ (p5 ∨ p1)) ∨ p5)) ∨ (p3 → (((((p4 → ((True ∨ p4) ∧ False)) → p1) → p1) ∨ (p1 → p1)) ∧ True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h2
  -- One of the premise coincides with the conclusion.
  exact h2
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_700694760491863340011265778062 : ((((p5 → (p4 ∧ (((p4 ∨ False) ∨ (p4 ∧ p1)) ∧ (True ∨ True)))) → (p2 ∧ (((p5 ∧ ((False ∧ p3) ∨ (p2 → p2))) ∨ False) ∨ p3))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_255875643821721412423336517717 : ((True ∨ p1) → (((((p3 ∨ p5) → p5) → p1) ∧ True) → ((((((False → (p5 ∨ ((p2 ∧ p4) → False))) → p4) ∨ p3) ∨ p4) ∧ p4) ∨ True))) := by
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
    -- True on the right can always be proven directly.
    apply True.intro
  case inr h6 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_61583770076593034067633415482 : ((p1 ∧ ((True ∧ (p1 → (False ∨ p4))) → ((p4 ∨ ((p3 ∧ p1) → p3)) → (((True ∧ True) ∧ ((False → p2) ∧ (p5 → False))) ∧ p4)))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_111027197212768298291400637851 : ((((p3 ∧ (((p1 ∨ (p1 ∧ (p5 ∧ (((p4 → (p1 ∨ p2)) ∨ p2) ∧ p2)))) ∨ p2) → p3)) → ((p4 ∧ p5) ∨ p5)) ∧ p2) ∨ (True ∨ False)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_47287885150812377987828736082 : (((((p4 → True) ∨ (p3 ∧ p5)) → (((p1 ∧ (p3 ∧ (((p4 ∧ p2) ∧ (True ∧ (p5 → p3))) ∧ p3))) → p3) → p2)) ∨ (p2 ∨ p1)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_52468296388832468142462585429 : (((p2 ∨ ((p2 ∨ p2) ∨ (False ∧ ((False ∨ ((p1 → p1) ∨ p5)) → p4)))) ∧ (((((p3 ∧ True) ∨ True) → p5) → p2) ∨ (p1 ∨ p1))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_191450147807929046127726758884 : (((p1 → p2) → (False ∧ ((p4 ∧ (p1 → p2)) ∨ True))) ∨ ((p3 ∨ True) ∨ (((((False → True) ∧ p1) ∧ (p1 ∨ p5)) ∧ p3) ∨ (p4 → p4)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_112967353681830643985362885819 : (((p1 ∧ (((p4 ∧ (p2 ∨ ((p1 ∧ (p2 ∨ ((p3 → ((p5 → (True → p5)) ∧ p2)) ∨ p4))) ∨ p5))) ∧ True) ∨ p1)) → p5) ∨ (False → p5)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_138064800160092802623358477471 : ((True → (p4 ∨ ((((p2 ∧ ((p5 ∧ p4) ∧ False)) → (((True ∧ (p2 ∧ (p3 ∨ False))) ∧ p2) ∨ p3)) → False) ∧ False))) ∨ (True ∨ (p2 ∨ p4))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_624423846084890834305484026992 : ((((p3 ∨ (p1 ∨ (((True ∨ p2) ∧ p2) ∨ (((((p4 → ((p3 ∧ False) → p1)) → p3) → p4) ∧ ((p1 ∨ p5) → False)) ∧ False)))) ∨ True) ∨ p5) ∧ True) := by
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
theorem thm_5_vars_321729125982801746353757427257 : (p4 ∨ (p5 → (((((((True ∨ True) → (p4 ∧ (p4 ∨ p1))) ∧ True) ∧ (p3 ∨ ((p3 → p2) → (False → True)))) ∨ False) ∨ True) ∨ (p2 → p1)))) := by
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
theorem thm_5_vars_347035408336385839391677753439 : (p3 → ((((True ∨ ((True ∨ p2) ∨ (((p5 → p5) ∧ (True → p3)) → False))) ∨ True) ∨ False) → ((((p5 ∧ (False → p5)) ∧ p3) ∨ True) ∨ True))) := by
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
      cases h4
      case inl h5 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- True on the right can always be proven directly.
        apply True.intro
      case inr h6 =>
        -- Disjunctions on the left can always be decomposed.
        cases h6
        case inl h7 =>
          -- Disjunctions on the left can always be decomposed.
          cases h7
          case inl h8 =>
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
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- True on the right can always be proven directly.
      apply True.intro
  case inr h12 =>
    -- False on the left can always be used.
    apply False.elim h12



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_171676477126443687116539574538 : (((p1 ∨ ((((True → (True ∨ p2)) → p1) ∨ (True ∨ (True ∨ False))) ∧ p1)) ∨ True) ∨ (((True ∧ False) → (p3 ∨ p3)) ∧ (p5 ∧ (p2 ∨ False)))) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_616592216639805624875147384019 : ((((((False → (((p3 → True) → False) ∨ p4)) → (p4 → False)) ∧ (((p4 ∧ (True → (((False ∧ p2) ∨ True) ∨ p4))) → p2) ∨ p1)) ∨ p2) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_168971020902096355472946327095 : ((False → ((((True ∨ p5) ∨ p4) ∨ (p3 → p1)) ∧ (True ∨ ((p5 → (p3 ∨ p2)) ∨ p4)))) → ((p5 → p2) ∨ (p4 ∨ ((p3 ∧ False) → p1)))) := by
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
  -- False on the left can always be used.
  apply False.elim h4



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_147261417642806475665300752559 : (((((p4 ∧ (p4 ∧ ((p4 ∨ (p1 → (p5 ∨ (p4 ∨ (True → p3))))) ∨ (True ∧ p5)))) ∧ p5) ∨ p1) ∨ True) ∨ ((True ∨ (p5 ∨ p5)) → p2)) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_62821280433916092334864432451 : ((p4 ∧ ((((p4 → False) ∨ (((False ∨ False) ∨ p5) ∨ p2)) ∧ False) ∨ ((p3 ∨ (p5 ∧ p1)) ∨ ((((p5 → False) ∧ p1) ∧ p1) → p5)))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_214131452466569190437403935572 : ((((p1 → p2) ∨ p5) → p5) ∨ ((((True → p1) ∧ p2) ∨ p4) → (((True ∧ (p2 → (p4 → p5))) → ((p1 ∨ p5) → p1)) ∨ (p1 → p1)))) := by
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
    -- Implications on the right can always be decomposed.
    intro h5
    -- One of the premise coincides with the conclusion.
    exact h5
  case inr h6 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h7
    -- One of the premise coincides with the conclusion.
    exact h7



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_54716221890457851213842236549 : (((((p5 → p4) ∧ (p5 ∧ p5)) → (p2 ∧ False)) → (p3 ∧ ((p3 → True) → ((p3 → (p4 → ((False ∧ (p3 → p1)) ∨ False))) → p5)))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_739139796261018399888813390281 : ((((p4 ∧ True) ∨ (((p2 ∨ (p5 ∧ (True → ((p3 → (True ∨ (True ∨ p5))) → ((True → (p4 ∨ p3)) ∨ False))))) ∧ False) ∧ (p2 ∧ False))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_608692993090195505188396958230 : ((((((((p5 ∧ ((p1 ∧ ((p1 ∧ p2) ∨ p3)) ∧ p3)) → (p5 ∨ ((p5 → (p2 ∧ p5)) ∨ p4))) ∨ p2) → (p3 ∧ p1)) ∨ False) ∨ p4) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_117376200855467184666896453429 : ((False ∧ (p3 → (True → (((False ∨ False) → (p1 ∧ p3)) → (((p1 → ((p4 ∨ p3) → (p4 ∨ (p4 ∨ p3)))) → p3) → p5))))) ∨ (False → p3)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_313330118030941024117826064189 : (p3 ∨ ((p4 ∨ (p2 → (((p1 → ((False ∧ p2) ∨ (False ∨ p4))) ∨ p2) → ((p3 ∧ (p4 ∨ (p3 ∧ p5))) ∧ (p5 → (True ∨ p3)))))) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_37200072087052854815119666312 : ((((((False ∨ p1) → ((p4 ∨ True) ∨ p4)) → (p5 → ((p4 ∧ ((p2 → (True ∧ (p1 ∧ (p4 ∨ p3)))) ∧ p2)) ∨ p1))) ∧ p2) ∧ p2) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_158919549345603474524006546794 : ((p1 ∨ (p4 ∧ ((((p5 ∨ p4) ∧ p4) ∨ p3) → (((p3 ∨ (True ∧ True)) → True) → (p5 ∨ p2))))) ∨ ((False → (p2 ∨ p5)) ∨ (p3 ∨ p3))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_179549909908958053635912382258 : ((p1 → (False ∨ ((True → ((False → p1) → (True ∧ False))) ∧ (p4 ∧ p3)))) ∨ (p3 → ((p3 ∨ ((p4 → True) → ((True → p2) ∧ p4))) ∨ p1))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_217793704506113447716349543193 : (((False ∨ (p2 → True)) → p1) → (((((False ∨ p4) → (True ∧ ((((p3 ∨ p5) ∨ (False ∨ True)) ∧ (p4 ∧ p5)) ∧ p3))) ∨ p3) → p4) ∨ p1)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h2 : (False ∨ (p2 → True)) := by
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h3
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h4 := h1 h2
  -- One of the premise coincides with the conclusion.
  exact h4



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_148251735872479051393781344358 : ((((p3 ∧ True) ∨ (p2 ∨ ((False ∨ ((p2 → p1) → (p5 ∨ False))) ∧ (p4 ∨ p3)))) ∨ ((p3 ∧ False) → p4)) ∨ (p5 → ((p4 ∨ p2) ∧ p3))) := by
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
  apply False.elim h3



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_113623489628228131717605272413 : (((p1 → ((p3 ∧ (((p1 → (p5 ∧ p1)) ∨ p4) ∧ (((p1 ∨ (p2 ∧ (False ∨ p3))) → p5) → p2))) ∨ p5)) ∨ (p1 ∨ p4)) ∨ (p3 → True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_157322795734258958799848270666 : (((p5 ∧ ((((((p5 ∧ p4) ∧ True) → p3) → True) ∧ (p4 ∧ ((p1 ∧ p5) → False))) ∨ p3)) → False) ∨ (True ∧ ((p3 → True) ∨ (False ∧ p2)))) := by
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
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_14988536321153234624540051912 : ((((p4 → p3) ∧ (((p5 ∧ (p4 ∨ ((p2 ∨ p5) → p1))) ∨ (p1 ∨ (False ∧ (True → ((p4 ∨ True) ∨ False))))) ∨ True)) ∨ (p2 ∨ True)) ∧ True) := by
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
theorem thm_5_vars_213449291372619560183167511874 : (((p5 ∨ (p5 ∨ False)) ∧ p1) ∨ (True → ((((p5 ∧ (False → p5)) ∨ False) ∨ p3) ∨ ((True ∨ False) → ((True ∧ True) ∨ (p5 ∧ (p1 ∧ p2))))))) := by
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
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Conjunctions on the right can always be decomposed.
    apply And.intro
    -- True on the right can always be proven directly.
    apply True.intro
    -- True on the right can always be proven directly.
    apply True.intro
  case inr h4 =>
    -- False on the left can always be used.
    apply False.elim h4



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_149707016845985017708979153555 : ((p5 ∧ (p1 ∧ (p3 → (((False → ((p5 → p3) → (p4 → ((p2 → (True ∧ p5)) → p1)))) → p1) → False)))) ∨ (False ∨ ((p4 ∧ p1) ∨ True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_344346078166743651691906901775 : (p2 → (p4 ∨ (((((((p2 → (((p3 ∨ p4) → p4) ∧ ((p2 ∨ False) ∧ False))) ∧ p4) → False) ∧ (p1 → (p4 ∧ p2))) ∧ True) ∨ p2) ∨ p2))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_320502874906369640990991957128 : (p4 ∨ (True ∧ ((((((p3 ∧ (p2 ∨ p3)) ∧ False) → True) ∨ (True ∧ (p3 → ((p3 → (p4 ∧ (p4 → (p5 → p4)))) → True)))) → p2) ∨ True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_61160844950484256088296084606 : ((False ∧ (((p1 ∨ p3) ∧ p4) ∧ ((False ∨ (p4 ∨ (((p2 ∧ (p4 → (p1 ∨ ((p5 → p1) ∧ p2)))) → p3) ∨ (p2 ∨ p1)))) ∧ p5))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_329774455607532004295841779686 : (True → (True ∧ ((p3 ∧ ((False ∨ p5) → ((p1 → p5) → p3))) ∨ (((p1 ∧ p5) → (((p2 ∨ p1) ∨ p3) ∨ ((p4 ∨ p2) ∨ p1))) ∨ p3)))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h2
  -- Conjunctions on the left can always be decomposed.
  let h3 := h2.left
  let h4 := h2.right
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h3



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_232320185868156847604154487434 : (((p3 → p4) → True) → ((((p1 → ((p4 ∨ p3) ∧ p3)) ∨ (p1 ∨ p3)) ∨ (p2 → (p3 ∨ (((p4 ∨ p2) ∧ p4) → (p5 ∧ p4))))) ∨ True)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_233890909395435162947648071010 : ((p4 ∨ (p3 ∨ p1)) → ((((p5 ∧ ((p5 → (p3 ∧ False)) ∨ p2)) ∧ (p4 → p4)) ∨ p2) ∨ ((((p5 → p2) ∨ p4) → (False ∧ p2)) ∨ True))) := by
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
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- True on the right can always be proven directly.
      apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_58494395861805642545126598908 : (((p4 ∨ p2) ∧ (p4 ∨ (((p1 → (False → False)) → p2) ∨ (((True ∧ True) → (((True → p1) ∧ p3) → p1)) ∨ (False ∨ (p3 → False)))))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_618550861263035632633450830837 : (((((p2 ∧ (True ∧ (p3 → p5))) → (((p2 ∧ p5) → (p5 → ((False ∨ ((True ∧ p5) ∧ (True → True))) → (True ∧ False)))) ∧ True)) ∨ p3) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_203957111464117129950755743637 : ((p2 → (p1 → ((p1 ∧ True) ∨ p5))) ∧ ((True → (False ∧ p5)) → ((p4 ∧ True) ∨ (((p4 → p1) → (p2 ∨ (p3 ∧ p5))) ∧ (p2 ∨ p5))))) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- One of the premise coincides with the conclusion.
  exact h2
  -- True on the right can always be proven directly.
  apply True.intro
  -- Implications on the right can always be decomposed.
  intro h3
  -- We want to use the implication h3 based on <expert-advice>. So we show its premise.
  have h4 : True := by
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h3, we can now drive its conclusion.
  let h5 := h3 h4
  -- We need to get the left conjuct of h5 based on <expert-advice>.
  let h6 := h5.left
  -- False on the left can always be used.
  apply False.elim h6



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_689610032886755731323849372887 : (((((p2 ∨ ((p4 → p1) ∧ (True ∨ p1))) ∨ (((p4 ∧ p4) ∨ p4) ∧ (p3 ∨ p1))) ∨ (p1 → ((p2 → p4) ∧ ((p5 → True) ∧ p1)))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_106983845385426903385928246869 : ((((p5 ∨ p4) ∧ (True → p4)) ∨ ((p2 ∨ (False ∨ (p3 ∨ ((p4 → (p2 ∧ p5)) → (((p2 ∨ False) ∧ False) → p1))))) ∨ p1)) ∧ (p1 → p1)) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
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
  -- Implications on the right can always be decomposed.
  intro h2
  -- Conjunctions on the left can always be decomposed.
  let h3 := h2.left
  let h4 := h2.right
  -- Disjunctions on the left can always be decomposed.
  cases h3
  case inl h5 =>
    -- False on the left can always be used.
    apply False.elim h4
  case inr h6 =>
    -- False on the left can always be used.
    apply False.elim h6
  -- Implications on the right can always be decomposed.
  intro h7
  -- One of the premise coincides with the conclusion.
  exact h7



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_326145066599689732485719971862 : (p5 ∨ (p1 → (p5 ∨ ((((p3 → p1) ∧ p4) → (((p2 ∨ True) → (((p1 → p3) ∨ ((p1 → False) → True)) ∨ (p5 → True))) → p2)) ∨ p1)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_671074729777188311432199261619 : ((((False ∨ ((True → (True → p4)) ∨ (p1 ∧ (p3 ∨ (((p3 → p5) → (((p3 ∧ p5) ∧ p5) → p2)) ∨ True))))) ∨ (p4 ∨ (p5 → True))) ∨ p3) ∧ True) := by
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
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_172706827506864262830393651161 : (((p1 ∨ p2) ∨ ((p1 ∧ ((p3 ∧ False) ∧ (((p2 ∧ p3) → False) ∧ p3))) ∨ p2)) ∨ ((((p5 ∨ (p5 → (p5 ∧ p3))) ∧ False) ∧ p1) → True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_51148561736212495387824295963 : ((((((p5 ∨ (False ∧ False)) → p5) ∨ (False ∨ ((False ∨ (p2 → (p1 → True))) ∨ True))) → p5) ∨ (((p5 ∧ p3) ∧ p3) → (p2 → p5))) ∨ False) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
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
  -- One of the premise coincides with the conclusion.
  exact h5



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_606736690035815101732375968912 : ((((((((p3 ∨ p1) ∧ True) ∨ (p3 → (((True ∧ (p5 ∧ (p4 → (p4 → False)))) ∧ p4) ∧ (p1 → p5)))) ∨ (False → False)) ∧ False) ∨ p2) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_337650388330297626128077488889 : (p1 → (((((True → (p3 ∨ (True ∧ p2))) ∨ (True ∨ ((True → False) ∧ (p5 ∨ p1)))) → p5) ∨ False) ∨ (False → ((p1 ∧ p4) ∨ (p3 → p2))))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h2
  -- False on the left can always be used.
  apply False.elim h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_621038332630158521972124739487 : (((((p1 → p1) → ((p1 ∧ ((p5 ∨ (((((p4 ∧ p1) ∧ p4) ∨ p5) → ((p4 → p5) ∨ False)) ∨ (p1 → False))) ∨ p2)) ∧ False)) ∨ True) ∨ p3) ∧ True) := by
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
theorem thm_5_vars_620850893977305118412734154006 : (((((p1 ∨ True) → (((p1 ∨ ((p4 → p5) ∧ (False ∧ p1))) ∧ ((((p3 ∧ p5) ∧ p2) ∨ (p5 → (p4 ∧ p4))) → p1)) ∧ p1)) ∨ True) ∨ p4) ∧ True) := by
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
theorem thm_5_vars_156630936192205978336609256222 : (((((p5 → (p5 ∨ (False → p5))) → (p5 ∨ (((p3 ∨ True) ∨ (False ∧ p3)) ∧ p3))) ∨ p1) ∧ p1) ∨ (True ∨ ((p5 ∨ p5) ∨ (p2 ∨ True)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_222181846348856368929627552224 : (((p5 ∨ False) → True) ∧ ((((p4 ∧ (True ∨ p3)) ∧ (p1 ∨ p4)) ∨ (p1 → (((p5 ∧ (p2 ∧ (False ∨ p1))) ∨ False) ∨ True))) ∨ (p5 → p1))) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h2
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_46534244093351341904953085521 : ((((p1 ∨ False) ∨ ((((((True ∧ p1) → p5) ∧ p3) → p4) ∨ (((True ∨ p5) → p2) ∧ ((True ∨ p2) ∨ False))) ∨ False)) ∧ (p5 ∨ p1)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_636310886375956551051355987791 : ((((((((p4 ∧ p1) → (((((True ∧ p2) → True) ∨ p3) ∨ p1) ∧ p5)) ∧ p2) → p5) → (True ∧ (p3 ∨ (p1 ∧ (p4 ∧ p3))))) → p4) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_639104122947546387929217730688 : ((((((p4 → (p3 → p5)) → p3) ∨ (False ∨ ((p1 → (((True → True) ∨ (False → True)) ∨ ((p1 → (p2 → False)) → False))) ∨ p3))) → p1) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_148833609578469004550713091145 : ((((p3 ∨ (p5 ∨ p3)) ∧ p5) ∧ ((((p4 ∨ (p2 ∨ (p2 ∨ p2))) ∨ p1) → (p2 ∧ p4)) ∨ (True ∧ True))) ∨ (((False ∧ False) → p5) → True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_306580572569546235907007958608 : (p1 ∨ ((p4 ∨ p4) → (((((((p1 ∨ p4) ∨ (p2 → p1)) ∨ p4) ∧ p3) ∧ p4) ∨ True) → ((p2 ∨ ((False ∧ p1) → (p4 ∧ p5))) ∨ p4)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
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
    -- Disjunctions on the left can always be decomposed.
    cases h6
    case inl h8 =>
      -- Disjunctions on the left can always be decomposed.
      cases h8
      case inl h9 =>
        -- Disjunctions on the left can always be decomposed.
        cases h9
        case inl h10 =>
          -- Disjunctions on the left can always be decomposed.
          cases h1
          case inl h11 =>
            -- Show the right disjunct based on <expert-advice>.
            apply Or.inr
            -- One of the premise coincides with the conclusion.
            exact h11
          case inr h12 =>
            -- Show the right disjunct based on <expert-advice>.
            apply Or.inr
            -- One of the premise coincides with the conclusion.
            exact h12
        case inr h13 =>
          -- Disjunctions on the left can always be decomposed.
          cases h1
          case inl h14 =>
            -- Show the right disjunct based on <expert-advice>.
            apply Or.inr
            -- One of the premise coincides with the conclusion.
            exact h14
          case inr h15 =>
            -- Show the right disjunct based on <expert-advice>.
            apply Or.inr
            -- One of the premise coincides with the conclusion.
            exact h15
      case inr h16 =>
        -- Disjunctions on the left can always be decomposed.
        cases h1
        case inl h17 =>
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- One of the premise coincides with the conclusion.
          exact h17
        case inr h18 =>
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- One of the premise coincides with the conclusion.
          exact h18
    case inr h19 =>
      -- Disjunctions on the left can always be decomposed.
      cases h1
      case inl h20 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- One of the premise coincides with the conclusion.
        exact h20
      case inr h21 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- One of the premise coincides with the conclusion.
        exact h21
  case inr h22 =>
    -- Disjunctions on the left can always be decomposed.
    cases h1
    case inl h23 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- One of the premise coincides with the conclusion.
      exact h23
    case inr h24 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- One of the premise coincides with the conclusion.
      exact h24



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_75909969569734898876092764094 : ((((((((True ∧ (p4 → p3)) → (p4 → ((p1 → (p1 ∨ p1)) ∧ ((True → p1) ∧ (p3 ∧ False))))) ∧ p3) ∧ p4) ∧ p2) → False) → False) → p4) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h2 : ((((((True ∧ (p4 → p3)) → (p4 → ((p1 → (p1 ∨ p1)) ∧ ((True → p1) ∧ (p3 ∧ False))))) ∧ p3) ∧ p4) ∧ p2) → False) := by
    -- Implications on the right can always be decomposed.
    intro h3
    -- Conjunctions on the left can always be decomposed.
    let h4 := h3.left
    let h5 := h3.right
    -- Conjunctions on the left can always be decomposed.
    let h6 := h4.left
    let h7 := h4.right
    -- Conjunctions on the left can always be decomposed.
    let h8 := h6.left
    let h9 := h6.right
    -- We want to use the implication h8 based on <expert-advice>. So we show its premise.
    have h10 : (True ∧ (p4 → p3)) := by
      -- Conjunctions on the right can always be decomposed.
      apply And.intro
      -- True on the right can always be proven directly.
      apply True.intro
      -- Implications on the right can always be decomposed.
      intro h11
      -- One of the premise coincides with the conclusion.
      exact h9
    -- We have shown the premise of h8, we can now drive its conclusion.
    let h12 := h8 h10
    -- We want to use the implication h12 based on <expert-advice>. So we show its premise.
    have h13 : p4 := by
      -- One of the premise coincides with the conclusion.
      exact h7
    -- We have shown the premise of h12, we can now drive its conclusion.
    let h14 := h12 h13
    -- We need to get the right conjuct of h14 based on <expert-advice>.
    let h15 := h14.right
    -- We need to get the right conjuct of h15 based on <expert-advice>.
    let h16 := h15.right
    -- We need to get the right conjuct of h16 based on <expert-advice>.
    let h17 := h16.right
    -- False on the left can always be used.
    apply False.elim h17
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h18 := h1 h2
  -- False on the left can always be used.
  apply False.elim h18



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_328831684852443299961805491175 : (True → ((p2 ∧ (((p1 → p3) → (p1 ∧ p5)) ∧ (p3 ∨ p2))) → (((p5 → True) → p1) ∨ (p5 → ((p4 ∨ (True ∧ (p2 ∨ p4))) ∧ p5))))) := by
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
  -- Disjunctions on the left can always be decomposed.
  cases h6
  case inl h7 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h8
    -- Conjunctions on the right can always be decomposed.
    apply And.intro
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Conjunctions on the right can always be decomposed.
    apply And.intro
    -- True on the right can always be proven directly.
    apply True.intro
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- One of the premise coincides with the conclusion.
    exact h3
    -- One of the premise coincides with the conclusion.
    exact h8
  case inr h9 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h10
    -- Conjunctions on the right can always be decomposed.
    apply And.intro
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Conjunctions on the right can always be decomposed.
    apply And.intro
    -- True on the right can always be proven directly.
    apply True.intro
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- One of the premise coincides with the conclusion.
    exact h9
    -- One of the premise coincides with the conclusion.
    exact h10



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_172130814447019149634523868187 : (((((p3 ∧ p3) ∧ p5) ∧ ((p1 ∧ (p1 ∧ p2)) ∨ True)) ∧ (True ∨ (True ∧ p1))) ∨ ((p4 ∨ p4) → ((p5 ∨ ((p2 → p3) ∧ p2)) → True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- True on the right can always be proven directly.
  apply True.intro



