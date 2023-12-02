variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_133632843255756515779305846684 : ((((True ∨ ((True ∧ (p2 ∨ p1)) → (True → (((p5 ∨ (p2 → (False ∧ (p2 ∨ p4)))) ∧ p1) ∨ False)))) → p1) ∧ True) ∨ (p2 ∨ (p2 → True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_112668288973398830983824310275 : ((((p5 ∧ ((p5 ∧ (((((p2 → (p5 ∨ p5)) ∨ (False ∧ p3)) ∨ p4) ∧ p3) → False)) → p2)) ∨ (p4 → (p1 → p2))) → p4) ∨ (False → p1)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_59485496033809676040535454647 : (((p1 → p4) ∨ ((((True ∧ p3) ∨ ((True ∧ (True ∧ p2)) ∨ p3)) → ((p4 ∨ (p3 → (p2 ∨ ((False ∧ p4) ∨ False)))) ∨ p4)) ∨ p2)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_49125530214177163647073334392 : ((((p4 ∨ ((False → p1) ∨ (p1 ∨ (p5 ∧ (True ∧ (p3 → False)))))) ∧ (((p3 ∨ (p1 ∧ p3)) → p3) → p3)) ∨ ((p3 ∧ False) ∨ p3)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_53204164162710920942549537235 : (((((True ∨ (p4 ∨ True)) → ((False ∧ True) → p3)) → (True → False)) ∨ (((p3 ∧ (True ∨ (False ∨ (p4 ∧ (True ∧ p2))))) ∨ p1) ∨ p2)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_94000881986968938161152133517 : ((p1 ∧ (True ∧ ((False ∨ (p1 → ((p2 ∧ (((p3 ∨ (False ∨ False)) ∧ (True ∧ p1)) ∨ p2)) ∧ False))) ∧ (p5 → ((p5 → p1) ∧ False))))) → p5) := by
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
  cases h6
  case inl h8 =>
    -- False on the left can always be used.
    apply False.elim h8
  case inr h9 =>
    -- We want to use the implication h9 based on <expert-advice>. So we show its premise.
    have h10 : p1 := by
      -- One of the premise coincides with the conclusion.
      exact h2
    -- We have shown the premise of h9, we can now drive its conclusion.
    let h11 := h9 h10
    -- We need to get the right conjuct of h11 based on <expert-advice>.
    let h12 := h11.right
    -- False on the left can always be used.
    apply False.elim h12



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_800324567686756781551399794466 : (((p2 → ((((True ∨ (p4 ∧ False)) ∧ (p4 ∨ ((p5 ∧ p1) ∨ p1))) ∨ (False ∨ (p2 ∧ (((p1 → p5) ∧ (False ∨ p2)) ∧ p3)))) ∨ p5)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_159898469682639782223967510974 : (((((p4 ∧ (p3 ∨ (((p3 → p1) ∧ p5) ∨ True))) ∧ (((p3 ∨ p2) ∧ p5) ∨ p2)) ∨ p4) → p5) → (((True ∨ p1) → (p2 ∧ p4)) ∨ True)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_148734037626245029311332574548 : (((((False ∧ (False ∨ p5)) ∨ False) ∨ True) ∧ (((p1 ∨ p2) ∨ (p5 → False)) → (p4 ∨ ((p2 ∧ p1) → p2)))) ∨ ((False ∨ (p3 ∨ p2)) → p1)) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
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
      -- Implications on the right can always be decomposed.
      intro h4
      -- Conjunctions on the left can always be decomposed.
      let h5 := h4.left
      let h6 := h4.right
      -- One of the premise coincides with the conclusion.
      exact h5
    case inr h7 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Implications on the right can always be decomposed.
      intro h8
      -- Conjunctions on the left can always be decomposed.
      let h9 := h8.left
      let h10 := h8.right
      -- One of the premise coincides with the conclusion.
      exact h9
  case inr h11 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h12
    -- Conjunctions on the left can always be decomposed.
    let h13 := h12.left
    let h14 := h12.right
    -- One of the premise coincides with the conclusion.
    exact h13



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_172271714719034312213203656024 : (((((p4 ∧ (p3 ∨ p1)) → p1) → (p1 → p4)) ∨ ((p2 ∧ (p2 → p3)) → p4)) ∨ ((True ∨ ((p2 ∨ p2) ∧ (True ∨ True))) → (p5 → p5))) := by
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
    -- Conjunctions on the left can always be decomposed.
    let h5 := h4.left
    let h6 := h4.right
    -- Disjunctions on the left can always be decomposed.
    cases h5
    case inl h7 =>
      -- Disjunctions on the left can always be decomposed.
      cases h6
      case inl h8 =>
        -- One of the premise coincides with the conclusion.
        exact h2
      case inr h9 =>
        -- One of the premise coincides with the conclusion.
        exact h2
    case inr h10 =>
      -- Disjunctions on the left can always be decomposed.
      cases h6
      case inl h11 =>
        -- One of the premise coincides with the conclusion.
        exact h2
      case inr h12 =>
        -- One of the premise coincides with the conclusion.
        exact h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_134951144860767094473056906729 : (((((((p4 ∨ (p2 → True)) ∨ ((p3 → (False → p5)) ∧ p4)) → p4) ∧ p4) → (True ∧ (p3 ∧ True))) ∧ (p4 ∨ p3)) ∨ ((p3 ∧ True) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_613977387933893085149835241713 : ((((((p2 ∨ (False → (p4 → ((p1 ∧ p5) → p1)))) ∧ (p3 ∨ ((((p5 ∨ p4) → True) ∨ p5) → False))) ∨ (p5 ∨ (True ∨ p3))) ∨ p4) ∨ False) ∧ True) := by
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
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_48925875872729114150062286892 : ((((((p2 → (True → ((p2 ∨ ((p4 → False) ∧ p5)) ∧ (p1 → p3)))) ∨ ((p1 → False) ∨ p4)) → False) ∧ True) ∨ (False ∨ (p3 ∧ False))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_59477402123074246719512003438 : (((p1 → p2) ∨ ((True ∨ False) → (p1 ∨ (p5 → (p4 → (p1 ∨ (((True ∧ p3) ∨ (p1 ∧ (p3 ∨ (p2 ∨ True)))) ∨ (p4 → p2)))))))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_3249885199106412692024246831 : ((p5 ∨ p3) ∨ (((p3 ∨ p5) → (p1 ∨ False)) → (((False ∨ ((p5 ∧ p2) ∧ ((p1 → True) ∨ True))) ∨ (p1 → p3)) ∨ (True ∨ True)))) := by
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
theorem thm_5_vars_185199813245116908740867728023 : ((True ∧ ((((p2 ∨ True) ∨ p2) ∧ p3) → ((p1 → p5) → p1))) ∨ (((True → ((False ∧ p1) ∧ p1)) → ((p4 ∧ p3) ∧ False)) → (p2 → p2))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- One of the premise coincides with the conclusion.
  exact h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_772671272671330769238988246 : (((False ∧ p5) ∨ (p3 ∨ (((((p3 → (p4 ∨ (False → p5))) → False) ∧ (p1 → p3)) ∧ (p2 ∧ p2)) → (p3 ∧ (p4 → p2))))) ∨ p4) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
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
  let h6 := h3.left
  let h7 := h3.right
  -- We want to use the implication h4 based on <expert-advice>. So we show its premise.
  have h8 : (p3 → (p4 ∨ (False → p5))) := by
    -- Implications on the right can always be decomposed.
    intro h9
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h10
    -- False on the left can always be used.
    apply False.elim h10
  -- We have shown the premise of h4, we can now drive its conclusion.
  let h11 := h4 h8
  -- False on the left can always be used.
  apply False.elim h11
  -- Implications on the right can always be decomposed.
  intro h12
  -- Conjunctions on the left can always be decomposed.
  let h13 := h1.left
  let h14 := h1.right
  -- Conjunctions on the left can always be decomposed.
  let h15 := h13.left
  let h16 := h13.right
  -- Conjunctions on the left can always be decomposed.
  let h17 := h14.left
  let h18 := h14.right
  -- One of the premise coincides with the conclusion.
  exact h18



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_111708848457962208216296557465 : ((((((p2 ∧ ((True ∨ p1) ∧ True)) ∨ ((p3 ∧ False) ∨ (True → (p1 ∨ p3)))) ∧ ((p5 ∨ (p1 ∨ p5)) → True)) → p4) ∨ p4) ∨ (p3 → True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_256630764032057576790161408275 : ((p1 ∨ True) → (p5 → ((p5 → (False ∧ p1)) ∨ (((p3 ∧ True) ∨ (p5 → p3)) ∨ ((False ∧ ((p2 → (p5 → p1)) ∨ p3)) → (True → False)))))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h3 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h4
    -- Implications on the right can always be decomposed.
    intro h5
    -- Conjunctions on the left can always be decomposed.
    let h6 := h4.left
    let h7 := h4.right
    -- False on the left can always be used.
    apply False.elim h6
  case inr h8 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h9
    -- Implications on the right can always be decomposed.
    intro h10
    -- Conjunctions on the left can always be decomposed.
    let h11 := h9.left
    let h12 := h9.right
    -- False on the left can always be used.
    apply False.elim h11



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_258928768885733238833936979314 : ((True → p2) → (False ∨ (((p4 ∨ (p4 ∧ (p3 ∧ (p5 → False)))) ∨ p3) ∨ (((p3 ∨ p5) ∨ ((True ∨ p3) ∨ (p2 ∨ False))) → (True ∨ p2))))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
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
      -- True on the right can always be proven directly.
      apply True.intro
    case inr h5 =>
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- True on the right can always be proven directly.
      apply True.intro
  case inr h6 =>
    -- Disjunctions on the left can always be decomposed.
    cases h6
    case inl h7 =>
      -- Disjunctions on the left can always be decomposed.
      cases h7
      case inl h8 =>
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- True on the right can always be proven directly.
        apply True.intro
      case inr h9 =>
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- True on the right can always be proven directly.
        apply True.intro
    case inr h10 =>
      -- Disjunctions on the left can always be decomposed.
      cases h10
      case inl h11 =>
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- True on the right can always be proven directly.
        apply True.intro
      case inr h12 =>
        -- False on the left can always be used.
        apply False.elim h12



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_2656975589817062972628028979 : ((((p1 ∨ p2) ∧ p5) ∨ (p4 ∧ True)) ∨ (((p1 ∧ False) ∧ (False → ((True ∧ p3) ∨ p3))) ∨ (False → (p5 ∨ (p1 → (False → False)))))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_42390703046019368409186864559 : (((p4 ∧ (((p3 ∨ (p5 → True)) ∧ p1) → (p1 → (p4 → (p1 → (False ∨ (p3 ∧ (p5 → (((p2 ∨ p1) → True) ∨ False))))))))) ∨ True) ∨ p1) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_50088800397934816551912657289 : (((p2 ∧ ((((((p3 ∧ (p1 ∨ False)) → (p3 → p2)) ∧ False) → p4) → ((p2 → False) ∧ p1)) ∧ True)) ∧ ((p1 ∧ (p4 ∨ p2)) → True)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_116041620042295855351926729506 : (((p4 ∨ (p4 ∧ (p1 ∨ p2))) → ((p4 → p5) ∧ ((((p4 ∨ ((False ∧ (True ∨ p4)) → True)) ∧ (p3 ∧ p2)) ∧ True) ∧ p1))) ∨ (p2 ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_300609115804637776829176901461 : (False ∨ (((True → p4) ∨ ((p1 ∧ p1) ∨ ((p4 → ((((p5 → p1) → p1) → (p3 ∨ True)) ∧ False)) → p1))) → (False ∨ (p2 ∨ (p1 → p1))))) := by
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
    -- One of the premise coincides with the conclusion.
    exact h3
  case inr h4 =>
    -- Disjunctions on the left can always be decomposed.
    cases h4
    case inl h5 =>
      -- Conjunctions on the left can always be decomposed.
      let h6 := h5.left
      let h7 := h5.right
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
theorem thm_5_vars_315713904116502247912604783770 : (p3 ∨ ((p5 ∨ p4) ∨ ((((((True → True) ∨ True) ∨ (p2 ∨ p1)) → (p5 ∨ (((p1 ∧ (p1 → (p4 → p4))) → p5) ∧ p2))) ∨ True) ∨ True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_200648351352386661752511482160 : ((p1 ∧ ((p2 → ((p5 ∧ p5) ∨ p1)) ∧ True)) → (((p3 ∨ p4) → ((p3 ∨ (False ∧ True)) → p4)) ∨ ((((p2 → p1) → p2) ∨ False) ∨ True))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- Conjunctions on the left can always be decomposed.
  let h4 := h3.left
  let h5 := h3.right
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_227365556916970869155041224306 : (((p3 → p4) → p5) ∨ ((((False ∨ (((((p1 ∧ p4) → True) → p2) ∨ p3) ∨ p4)) → p4) → ((p5 ∨ (p1 ∨ p4)) → p2)) ∨ (True ∨ False))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_806977498039100505070070894833 : (((p4 → (((((True ∧ (p1 ∧ p5)) ∨ p5) ∨ (p3 → (p1 ∧ ((False ∨ (p3 ∧ True)) → p1)))) ∧ (p4 → p5)) ∨ (p4 ∨ (p2 ∧ p1)))) ∨ p3) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- One of the premise coincides with the conclusion.
  exact h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_203705137376797459242961939519 : ((p4 ∨ ((False → False) ∨ (False → False))) ∧ (False ∨ (((False → p3) → ((True → p2) ∧ True)) ∨ (((p1 ∧ (False → p5)) ∧ False) ∨ (True ∨ p1))))) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- False on the left can always be used.
  apply False.elim h1
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
theorem thm_5_vars_673597230988400697665640997470 : ((((((False ∨ p5) → p5) ∨ (((p5 → p3) ∧ (p2 ∧ (p4 ∨ ((False ∧ p1) ∧ ((p2 ∨ p3) ∧ p2))))) ∨ p2)) → (p5 → (p2 ∨ False))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_323720442530254327676309766400 : (p5 ∨ (((p2 ∨ (True ∧ p3)) ∧ ((p5 ∧ (False → p2)) ∨ ((p4 ∨ (((p4 → p4) → p5) ∨ p5)) ∨ False))) → ((p1 → p2) ∨ (True ∧ True)))) := by
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
    cases h3
    case inl h5 =>
      -- Conjunctions on the left can always be decomposed.
      let h6 := h5.left
      let h7 := h5.right
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Conjunctions on the right can always be decomposed.
      apply And.intro
      -- True on the right can always be proven directly.
      apply True.intro
      -- True on the right can always be proven directly.
      apply True.intro
    case inr h8 =>
      -- Disjunctions on the left can always be decomposed.
      cases h8
      case inl h9 =>
        -- Disjunctions on the left can always be decomposed.
        cases h9
        case inl h10 =>
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- Conjunctions on the right can always be decomposed.
          apply And.intro
          -- True on the right can always be proven directly.
          apply True.intro
          -- True on the right can always be proven directly.
          apply True.intro
        case inr h11 =>
          -- Disjunctions on the left can always be decomposed.
          cases h11
          case inl h12 =>
            -- Show the right disjunct based on <expert-advice>.
            apply Or.inr
            -- Conjunctions on the right can always be decomposed.
            apply And.intro
            -- True on the right can always be proven directly.
            apply True.intro
            -- True on the right can always be proven directly.
            apply True.intro
          case inr h13 =>
            -- Show the right disjunct based on <expert-advice>.
            apply Or.inr
            -- Conjunctions on the right can always be decomposed.
            apply And.intro
            -- True on the right can always be proven directly.
            apply True.intro
            -- True on the right can always be proven directly.
            apply True.intro
      case inr h14 =>
        -- False on the left can always be used.
        apply False.elim h14
  case inr h15 =>
    -- Conjunctions on the left can always be decomposed.
    let h16 := h15.left
    let h17 := h15.right
    -- Disjunctions on the left can always be decomposed.
    cases h3
    case inl h18 =>
      -- Conjunctions on the left can always be decomposed.
      let h19 := h18.left
      let h20 := h18.right
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Conjunctions on the right can always be decomposed.
      apply And.intro
      -- True on the right can always be proven directly.
      apply True.intro
      -- True on the right can always be proven directly.
      apply True.intro
    case inr h21 =>
      -- Disjunctions on the left can always be decomposed.
      cases h21
      case inl h22 =>
        -- Disjunctions on the left can always be decomposed.
        cases h22
        case inl h23 =>
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- Conjunctions on the right can always be decomposed.
          apply And.intro
          -- True on the right can always be proven directly.
          apply True.intro
          -- True on the right can always be proven directly.
          apply True.intro
        case inr h24 =>
          -- Disjunctions on the left can always be decomposed.
          cases h24
          case inl h25 =>
            -- Show the right disjunct based on <expert-advice>.
            apply Or.inr
            -- Conjunctions on the right can always be decomposed.
            apply And.intro
            -- True on the right can always be proven directly.
            apply True.intro
            -- True on the right can always be proven directly.
            apply True.intro
          case inr h26 =>
            -- Show the right disjunct based on <expert-advice>.
            apply Or.inr
            -- Conjunctions on the right can always be decomposed.
            apply And.intro
            -- True on the right can always be proven directly.
            apply True.intro
            -- True on the right can always be proven directly.
            apply True.intro
      case inr h27 =>
        -- False on the left can always be used.
        apply False.elim h27



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_324722288594241068266431764417 : (p5 ∨ (((p2 ∧ False) → False) → (((False ∨ p5) ∨ ((((p1 ∨ (p4 → (p3 ∨ (p1 ∨ True)))) ∨ p4) ∨ False) ∨ (p5 ∨ p2))) ∨ (p3 ∧ p5)))) := by
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
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h2
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_171986374106403107446769997662 : (((((((True ∧ p2) ∨ False) ∧ (p2 ∧ (p1 ∨ p4))) ∨ p5) ∧ p4) ∨ (p1 → p1)) ∨ (p4 ∧ (p3 → (p2 ∨ (True ∧ ((p5 ∧ p5) ∨ False)))))) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_142283121457485145901814119076 : ((p2 ∧ ((p3 ∧ p3) ∨ (p2 ∧ (p3 ∨ ((((True → (p3 ∧ (((p4 → p5) → p4) ∨ p2))) ∨ False) ∧ p5) ∧ True))))) → ((p4 ∨ p4) ∨ True)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- Disjunctions on the left can always be decomposed.
  cases h3
  case inl h4 =>
    -- Conjunctions on the left can always be decomposed.
    let h5 := h4.left
    let h6 := h4.right
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
      -- Conjunctions on the left can always be decomposed.
      let h12 := h11.left
      let h13 := h11.right
      -- Conjunctions on the left can always be decomposed.
      let h14 := h12.left
      let h15 := h12.right
      -- Disjunctions on the left can always be decomposed.
      cases h14
      case inl h16 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- True on the right can always be proven directly.
        apply True.intro
      case inr h17 =>
        -- False on the left can always be used.
        apply False.elim h17



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_350319623396692674445923574757 : (p4 → ((p5 ∨ (p2 ∨ (True → (((p3 ∧ ((((True ∧ p4) ∧ (p1 ∧ ((True ∧ (p2 → p3)) ∧ p4))) ∨ False) ∧ p5)) → True) → False)))) ∨ True)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_149142928326697084730117952969 : (((True ∨ False) ∧ (((True → (p5 ∨ (p5 ∨ p2))) ∧ (p4 ∨ (((p1 → (p4 → p5)) ∨ False) ∨ p4))) ∧ True)) ∨ (True ∧ (True ∧ (False → p1)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- Implications on the right can always be decomposed.
  intro h1
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_83986417411084833619742635193 : ((((p4 ∧ ((p2 ∧ p1) ∧ (p2 ∨ (((p4 → True) ∧ p5) → (p3 ∧ p2))))) ∧ p3) ∧ (((p1 ∨ False) → (False → p3)) ∨ (p5 → p3))) → p3) := by
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
  -- Conjunctions on the left can always be decomposed.
  let h10 := h8.left
  let h11 := h8.right
  -- Disjunctions on the left can always be decomposed.
  cases h9
  case inl h12 =>
    -- Disjunctions on the left can always be decomposed.
    cases h3
    case inl h13 =>
      -- One of the premise coincides with the conclusion.
      exact h5
    case inr h14 =>
      -- One of the premise coincides with the conclusion.
      exact h5
  case inr h15 =>
    -- Disjunctions on the left can always be decomposed.
    cases h3
    case inl h16 =>
      -- One of the premise coincides with the conclusion.
      exact h5
    case inr h17 =>
      -- One of the premise coincides with the conclusion.
      exact h5



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_342869031426983534806333900200 : (p2 → ((p1 ∧ ((p1 ∧ (p4 ∨ p4)) ∨ False)) ∨ ((((((p2 → False) ∨ p1) ∧ p1) ∧ False) ∧ ((((p3 → p5) ∧ p1) ∨ p2) ∨ p2)) ∨ True))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_190284114184520530615743155706 : ((((((p1 → (p3 ∨ True)) ∨ p4) ∧ p2) → p1) ∨ p3) ∨ ((p5 ∧ ((False ∧ p5) → (p4 ∧ ((p5 ∧ p5) → (p4 → p1))))) → (False ∨ p5))) := by
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
  exact h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_114983344688384223778767421290 : ((((p5 → ((p2 ∨ False) → (((p1 ∨ p2) ∧ p2) ∧ True))) ∨ p1) ∧ (((((False ∨ p5) → (True → p2)) ∧ p1) ∧ False) ∨ False)) ∨ (p3 ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_137909128943048054453036032564 : ((p4 ∨ ((p2 ∨ (((p4 ∧ (p5 ∨ p4)) ∨ p4) ∧ p4)) → (((p5 ∨ (((p5 → False) ∨ p2) ∨ p3)) ∨ False) ∧ p3))) ∨ (p4 ∨ (p1 ∨ True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_110707506170245705810562244513 : (((((((p3 → p5) ∨ p4) ∨ ((p2 ∧ p5) → ((p3 ∨ ((True ∧ ((p1 ∨ p4) ∨ True)) → p3)) ∧ p3))) ∨ True) ∧ True) ∧ True) ∨ (p5 → True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_56023844842548372619773738312 : ((((True ∧ (p5 → p3)) ∨ False) ∨ (p3 ∧ (p1 ∧ ((p3 → (p3 ∧ ((True → False) ∧ ((p2 ∨ (p5 → (p1 ∨ p5))) ∧ False)))) ∨ False)))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_66585232147172886727221090113 : ((True → (((p3 ∨ (True ∨ (((p3 ∧ (p3 ∨ p1)) ∨ (p1 ∧ (p3 → False))) ∧ True))) → (p2 → (p1 ∨ p1))) ∧ (False ∨ (p4 → p5)))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_41485566624195209733431377555 : ((((p3 ∨ ((p3 ∨ ((p1 ∨ p3) ∨ ((p5 ∨ p4) → p3))) → False)) ∨ (False ∧ (True ∨ (((p1 ∧ False) ∨ (False ∨ True)) ∨ p4)))) ∨ p4) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_50386816648715840435715094144 : ((((p4 ∧ p5) ∨ ((((p4 ∨ (p4 ∨ p4)) → (p2 ∧ p1)) ∧ (p3 ∧ (p4 ∧ p2))) ∧ (False ∧ False))) ∨ ((p1 ∧ (True ∨ False)) → p3)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_113192774151108174082611986418 : ((((p4 ∧ (((p5 ∧ p3) ∧ (p2 ∨ ((True ∨ p2) ∧ (p5 → (p4 ∨ (p2 → (p4 ∨ True))))))) → p4)) ∧ p1) ∧ (p2 ∧ p3)) ∨ (True ∨ False)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_207727351494077741399741064351 : (((p3 ∧ (False ∧ (False → p3))) → p1) → ((False ∧ (p5 ∨ (((p2 ∧ p2) ∨ (False ∨ (p5 → False))) → p5))) ∨ (True ∨ ((p5 ∧ p1) → p2)))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_228055751297975742012131267539 : ((p4 ∧ (p1 ∧ p3)) ∨ ((((p4 ∨ p4) ∧ (p5 ∧ (p5 ∧ p5))) → p5) ∧ (((p3 ∧ (p3 ∨ p1)) ∧ ((p1 ∨ p3) ∧ p1)) ∨ (p1 ∨ True)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
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
    -- Conjunctions on the left can always be decomposed.
    let h7 := h6.left
    let h8 := h6.right
    -- One of the premise coincides with the conclusion.
    exact h8
  case inr h9 =>
    -- Conjunctions on the left can always be decomposed.
    let h10 := h3.left
    let h11 := h3.right
    -- Conjunctions on the left can always be decomposed.
    let h12 := h11.left
    let h13 := h11.right
    -- One of the premise coincides with the conclusion.
    exact h13
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_177961363411747007943793389019 : ((((p3 ∨ p1) ∨ (((p2 ∨ (True → (True ∨ p4))) ∧ p3) ∨ p5)) ∨ False) ∨ ((p4 ∨ (((p5 ∧ p5) → p5) → True)) ∧ ((p4 ∧ False) → p5))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
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
  -- Conjunctions on the left can always be decomposed.
  let h3 := h2.left
  let h4 := h2.right
  -- False on the left can always be used.
  apply False.elim h4



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_118478418710832387426464844239 : ((p3 ∨ ((p5 → ((p1 ∨ p4) ∧ (p3 ∨ ((p1 ∨ (p2 ∨ ((((True → p1) ∧ False) ∨ True) ∧ p4))) ∨ p1)))) ∧ (False ∨ p3))) ∨ (False → p3)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_621693344796447474340744347120 : ((((False ∧ (p1 → ((((p5 ∨ True) ∧ (True ∧ ((((p1 ∧ (p1 ∨ True)) → True) → False) ∨ False))) ∧ p1) ∧ (p5 ∨ (p2 ∨ True))))) ∨ True) ∨ p3) ∧ True) := by
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
theorem thm_5_vars_200356599934733091150334783365 : (((False → False) ∧ ((p1 → (p1 → p2)) ∧ p4)) → (((True ∧ p3) ∨ p3) ∨ (False ∨ ((p4 → (p1 ∧ p1)) ∨ ((False → p5) ∧ (True → True)))))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- Conjunctions on the left can always be decomposed.
  let h4 := h3.left
  let h5 := h3.right
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h6
  -- False on the left can always be used.
  apply False.elim h6
  -- Implications on the right can always be decomposed.
  intro h7
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_17848017508822134394008661112 : ((((((((p3 ∨ p2) ∧ True) ∨ p1) → (True ∧ (True → (False ∨ (p3 ∧ p5))))) ∧ (True ∨ p4)) ∨ True) ∨ (p4 ∧ ((p4 → False) ∧ p1))) ∧ True) := by
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
theorem thm_5_vars_190815025971450693151999444624 : (((p1 ∧ ((p4 ∨ p5) → (p1 ∨ p5))) ∨ (p5 ∨ p4)) ∨ (False → (((p2 → p5) → p5) ∧ ((((True ∨ True) ∧ (p2 ∨ p4)) ∨ True) ∧ True)))) := by
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
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- False on the left can always be used.
  apply False.elim h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_180594248186768681823131153825 : (((p3 → (((p3 → (False ∧ p5)) ∨ True) → p2)) → ((p3 → p3) ∧ p1)) → (((True → p1) ∨ ((p2 → p5) ∨ ((p3 ∧ p2) ∧ True))) ∨ True)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_299089315814519176022107726051 : (False ∨ (((((((p4 ∨ (True ∨ ((True ∨ p4) ∨ (p5 ∧ p4)))) → p1) ∨ ((((p2 ∨ False) ∨ p3) ∨ p1) ∧ p5)) → p3) → p5) ∧ p5) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_356434912050738305340251590171 : (p5 → (((False ∨ (p1 ∧ ((p3 ∧ (p2 → p5)) ∧ (p1 ∨ p4)))) ∨ True) ∨ ((True → p3) → ((((p1 → (p4 ∨ p1)) ∧ p4) ∧ p3) → p3)))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_387378724124050640047566706031 : ((((((p5 ∧ (((p5 → (((False ∧ p2) ∨ (True → p2)) ∧ p4)) ∧ (p5 → (True → p2))) ∨ p1)) → p1) ∨ (p2 ∧ (p1 ∧ p1))) ∨ True) ∧ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_352250948784456495659761496990 : (p4 → ((p5 ∨ ((p3 ∧ p1) ∨ p1)) ∨ (((p5 ∧ (False ∨ False)) ∨ (p4 ∨ True)) ∨ (False → (p3 ∨ (((p3 ∧ p3) → (False ∨ True)) ∧ p4)))))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_58973754254895523306856849538 : (((p2 ∧ p4) ∨ ((((p3 ∨ False) ∨ ((p1 ∧ ((p1 ∧ p5) ∨ (p5 ∧ True))) ∧ False)) ∧ (((p2 ∨ (False ∨ p2)) ∨ p3) → p2)) ∨ True)) ∨ p1) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_46935016836543735266925530877 : ((((p1 ∧ ((p2 ∧ p5) ∧ (p5 ∧ (((((True ∧ p3) → True) → p2) → ((p5 ∨ p1) → p4)) ∧ (p3 ∧ p3))))) ∨ p5) ∨ (p4 ∨ True)) ∨ p1) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_118727947042717766722490010741 : ((p5 ∨ (((True ∨ (((p3 ∨ True) → p2) → (((p4 ∧ p2) ∧ p2) ∧ p4))) → (p3 ∨ p1)) ∨ ((False ∧ (p5 ∨ True)) → p2))) ∨ (p2 → True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_148741842385958224546742779908 : (((((p2 ∨ p2) → p1) ∧ (p4 ∨ p3)) ∧ ((p1 → (((p1 → p4) ∧ p3) ∧ ((False ∧ p4) ∨ p2))) ∧ p3)) ∨ (((p1 ∨ p5) → p1) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_57006115925832606320769752456 : (((True → (p1 → p5)) ∧ ((((((((True → p1) ∧ p4) ∧ True) → ((p2 ∨ True) → p2)) ∨ p3) ∧ ((True → p5) ∧ p2)) ∨ False) → False)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_346590319172978437354227915578 : (p3 → ((((True ∧ (p5 ∧ (p1 ∨ (p5 ∧ (((True → p1) ∨ p5) ∧ (True → (False → p3))))))) ∧ (p2 ∧ p4)) ∨ p3) ∨ (False → (True → p1)))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_147243359046053502665824526735 : (((((True ∧ ((((p4 → p4) ∧ p2) ∨ p3) ∨ p1)) → (((p4 ∧ p1) ∨ False) ∨ (p5 ∨ False))) ∧ False) ∨ p2) ∨ (False → ((True ∧ p4) ∧ p4))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- False on the left can always be used.
  apply False.elim h1
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_156698955328016891734817373795 : (((((((p2 ∧ ((False ∨ False) ∨ (False ∧ p3))) ∨ p4) → p2) ∨ p4) → (p1 ∧ (p1 → p5))) ∧ False) ∨ (p2 ∨ (((False → False) ∧ p3) ∨ True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_719681048869642787160645894790 : ((((True → (p1 ∨ (False ∨ p3))) ∨ ((p3 ∧ ((p5 ∨ ((((((p3 ∨ (p5 → p5)) → p2) ∧ True) ∨ True) → p2) ∧ True)) ∨ False)) ∧ True)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_161653290373240603982593586282 : ((p1 ∨ ((((((p1 → (p5 ∧ p2)) ∧ p1) → True) → p4) ∨ p4) ∧ (((p3 → False) → p1) → p2))) → (p3 ∨ ((p4 → p1) → (p5 ∨ True)))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h2 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h3
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro
  case inr h4 =>
    -- Conjunctions on the left can always be decomposed.
    let h5 := h4.left
    let h6 := h4.right
    -- Disjunctions on the left can always be decomposed.
    cases h5
    case inl h7 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Implications on the right can always be decomposed.
      intro h8
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- True on the right can always be proven directly.
      apply True.intro
    case inr h9 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Implications on the right can always be decomposed.
      intro h10
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- True on the right can always be proven directly.
      apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_355710685829926183359518135602 : (p5 → ((((True → (p4 ∧ p3)) ∧ p4) ∧ ((True → (((p2 ∨ p1) → p4) → p1)) ∨ (True ∨ (((False ∨ True) → p4) ∧ p1)))) → (p5 → p3))) := by
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
  -- Disjunctions on the left can always be decomposed.
  cases h5
  case inl h8 =>
    -- We want to use the implication h6 based on <expert-advice>. So we show its premise.
    have h9 : True := by
      -- True on the right can always be proven directly.
      apply True.intro
    -- We have shown the premise of h6, we can now drive its conclusion.
    let h10 := h6 h9
    -- We need to get the right conjuct of h10 based on <expert-advice>.
    let h11 := h10.right
    -- One of the premise coincides with the conclusion.
    exact h11
  case inr h12 =>
    -- Disjunctions on the left can always be decomposed.
    cases h12
    case inl h13 =>
      -- We want to use the implication h6 based on <expert-advice>. So we show its premise.
      have h14 : True := by
        -- True on the right can always be proven directly.
        apply True.intro
      -- We have shown the premise of h6, we can now drive its conclusion.
      let h15 := h6 h14
      -- We need to get the right conjuct of h15 based on <expert-advice>.
      let h16 := h15.right
      -- One of the premise coincides with the conclusion.
      exact h16
    case inr h17 =>
      -- Conjunctions on the left can always be decomposed.
      let h18 := h17.left
      let h19 := h17.right
      -- We want to use the implication h6 based on <expert-advice>. So we show its premise.
      have h20 : True := by
        -- True on the right can always be proven directly.
        apply True.intro
      -- We have shown the premise of h6, we can now drive its conclusion.
      let h21 := h6 h20
      -- We need to get the right conjuct of h21 based on <expert-advice>.
      let h22 := h21.right
      -- One of the premise coincides with the conclusion.
      exact h22



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_705409322450085089518648123276 : (((((p1 ∧ (False → ((p4 → True) → p1))) ∨ p3) ∧ ((p2 → (p3 ∧ (p4 ∨ ((((False → p5) ∧ p3) → p4) ∧ (p3 ∧ p2))))) → p4)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_336279630138052758418751538671 : (p1 → (((((p5 ∨ False) ∧ p4) ∨ ((p3 ∨ (True ∨ p5)) ∨ True)) ∧ (True → (p3 → (((((p2 → p5) ∨ p1) ∨ p5) → p2) → p2)))) ∨ True)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_148583117260165693746674408176 : (((((p3 ∧ (p2 → p5)) ∧ ((p3 → p4) → p5)) → False) ∨ (((False → ((p1 ∧ p2) ∧ True)) ∧ p1) ∨ True)) ∨ ((p2 ∧ p3) ∧ (p2 → p3))) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_689598254186453413813001535251 : (((((((p5 → (p2 ∨ True)) ∨ p5) → p2) ∨ (p4 → (p1 ∨ ((False ∨ p1) ∨ p4)))) ∨ ((((p3 ∨ p2) ∨ (p5 ∨ True)) → p3) ∨ p4)) ∨ p5) ∧ True) := by
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
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_56545911817177584459060559297 : (((p2 ∨ ((p2 → False) → p2)) → ((p5 ∨ p3) → ((p4 → (((p1 ∧ ((p5 → p3) ∧ False)) ∨ True) ∨ ((p4 ∨ True) → True))) ∨ p4))) ∨ False) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
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
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- Implications on the right can always be decomposed.
      intro h5
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- True on the right can always be proven directly.
      apply True.intro
    case inr h6 =>
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- Implications on the right can always be decomposed.
      intro h7
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- True on the right can always be proven directly.
      apply True.intro
  case inr h8 =>
    -- Disjunctions on the left can always be decomposed.
    cases h1
    case inl h9 =>
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- Implications on the right can always be decomposed.
      intro h10
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- True on the right can always be proven directly.
      apply True.intro
    case inr h11 =>
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- Implications on the right can always be decomposed.
      intro h12
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- True on the right can always be proven directly.
      apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_157030135325903864415301561798 : ((((p1 → p5) ∨ ((p1 → (p3 ∨ ((p5 ∨ (True ∧ (p5 ∧ p1))) ∧ p5))) → (False ∧ True))) ∨ False) ∨ (((p3 ∨ False) ∨ p3) ∨ (p4 ∨ True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_49705587815873450231046911327 : ((((p4 ∨ True) → (p1 → ((p4 ∨ (((p5 ∧ True) ∧ p1) ∧ ((p2 ∨ False) → ((p5 → p4) ∧ True)))) → p1))) → (p5 ∨ (False ∧ True))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_62412817240670469861649633636 : ((p3 ∧ ((((p4 ∧ p2) ∧ p4) ∧ (p3 ∨ p5)) ∧ (True ∧ ((False → (((p3 ∨ (p5 ∧ p4)) → p3) → p2)) → (p4 → (True ∧ True)))))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_663923705230546260825425455327 : ((((p4 ∧ ((p1 → (((((True → (p3 → p4)) ∧ p2) → False) ∨ (((p1 → False) ∨ p5) → p5)) → False)) ∧ (p4 → p1))) → (p2 ∧ p2)) ∨ p5) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- Conjunctions on the left can always be decomposed.
  let h4 := h3.left
  let h5 := h3.right
  -- We want to use the implication h5 based on <expert-advice>. So we show its premise.
  have h6 : p4 := by
    -- One of the premise coincides with the conclusion.
    exact h2
  -- We have shown the premise of h5, we can now drive its conclusion.
  let h7 := h5 h6
  -- We want to use the implication h4 based on <expert-advice>. So we show its premise.
  have h8 : p1 := by
    -- One of the premise coincides with the conclusion.
    exact h7
  -- We have shown the premise of h4, we can now drive its conclusion.
  let h9 := h4 h8
  -- We want to use the implication h9 based on <expert-advice>. So we show its premise.
  have h10 : ((((True → (p3 → p4)) ∧ p2) → False) ∨ (((p1 → False) ∨ p5) → p5)) := by
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h11
    -- Disjunctions on the left can always be decomposed.
    cases h11
    case inl h12 =>
      -- We want to use the implication h12 based on <expert-advice>. So we show its premise.
      have h13 : p1 := by
        -- One of the premise coincides with the conclusion.
        exact h7
      -- We have shown the premise of h12, we can now drive its conclusion.
      let h14 := h12 h13
      -- False on the left can always be used.
      apply False.elim h14
    case inr h15 =>
      -- One of the premise coincides with the conclusion.
      exact h15
  -- We have shown the premise of h9, we can now drive its conclusion.
  let h16 := h9 h10
  -- False on the left can always be used.
  apply False.elim h16
  -- Conjunctions on the left can always be decomposed.
  let h17 := h1.left
  let h18 := h1.right
  -- Conjunctions on the left can always be decomposed.
  let h19 := h18.left
  let h20 := h18.right
  -- We want to use the implication h20 based on <expert-advice>. So we show its premise.
  have h21 : p4 := by
    -- One of the premise coincides with the conclusion.
    exact h17
  -- We have shown the premise of h20, we can now drive its conclusion.
  let h22 := h20 h21
  -- We want to use the implication h19 based on <expert-advice>. So we show its premise.
  have h23 : p1 := by
    -- One of the premise coincides with the conclusion.
    exact h22
  -- We have shown the premise of h19, we can now drive its conclusion.
  let h24 := h19 h23
  -- We want to use the implication h24 based on <expert-advice>. So we show its premise.
  have h25 : ((((True → (p3 → p4)) ∧ p2) → False) ∨ (((p1 → False) ∨ p5) → p5)) := by
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h26
    -- Disjunctions on the left can always be decomposed.
    cases h26
    case inl h27 =>
      -- We want to use the implication h27 based on <expert-advice>. So we show its premise.
      have h28 : p1 := by
        -- One of the premise coincides with the conclusion.
        exact h22
      -- We have shown the premise of h27, we can now drive its conclusion.
      let h29 := h27 h28
      -- False on the left can always be used.
      apply False.elim h29
    case inr h30 =>
      -- One of the premise coincides with the conclusion.
      exact h30
  -- We have shown the premise of h24, we can now drive its conclusion.
  let h31 := h24 h25
  -- False on the left can always be used.
  apply False.elim h31
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_191941674764777899857109925250 : ((True → ((p1 ∨ p5) → ((p2 → p3) → (p1 ∧ p1)))) ∨ (((p2 ∨ p4) → (((False ∧ ((True ∧ p2) ∧ p3)) ∨ (False ∨ p4)) ∨ True)) ∨ False)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
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
theorem thm_5_vars_149410364128756444752488290384 : ((True ∧ ((((False → False) ∧ ((True ∨ p2) → (((False ∨ False) ∨ False) ∨ True))) → False) → ((p2 ∧ p3) ∨ p3))) ∨ (((p5 ∨ p2) ∨ True) → p4)) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- Implications on the right can always be decomposed.
  intro h1
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h2 : ((False → False) ∧ ((True ∨ p2) → (((False ∨ False) ∨ False) ∨ True))) := by
    -- Conjunctions on the right can always be decomposed.
    apply And.intro
    -- Implications on the right can always be decomposed.
    intro h3
    -- False on the left can always be used.
    apply False.elim h3
    -- Implications on the right can always be decomposed.
    intro h4
    -- Disjunctions on the left can always be decomposed.
    cases h4
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
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h7 := h1 h2
  -- False on the left can always be used.
  apply False.elim h7



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_204821966989788954137410051521 : ((((True ∧ (p3 → p1)) ∨ p1) → p4) ∨ (False ∨ (p1 → ((p5 ∨ ((False → False) ∨ p4)) ∨ ((p5 ∨ (p1 → True)) ∨ (p1 ∧ (True ∧ p1))))))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
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
  -- Implications on the right can always be decomposed.
  intro h2
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_218389111015652008380052457927 : (((p5 → p4) ∨ (p2 → p3)) → (p4 → ((p3 → (((p4 ∨ ((p4 ∧ p4) ∨ p1)) → (p1 ∨ p1)) → (False ∧ (False → p5)))) ∨ (True ∨ True)))) := by
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
theorem thm_5_vars_158497602932012320929711360767 : (((p4 ∧ p2) → ((((((False ∨ p3) → False) → p3) ∧ ((p2 → False) → p4)) → (p3 ∧ p1)) ∧ p1)) ∨ (False → (((p1 ∨ p5) → p5) ∧ p3))) := by
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
    apply False.elim h1
  case inr h4 =>
    -- False on the left can always be used.
    apply False.elim h1
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_40459796127012643804153133508 : ((((((True ∨ False) ∨ (True ∧ p1)) → (p1 ∧ (((p2 ∧ (p5 → ((p4 ∧ p3) → True))) ∧ (True → (False ∧ p4))) ∧ p2))) ∨ p1) ∨ True) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_197103146718935578766605384689 : (((p5 ∧ ((True → (p5 → p5)) → False)) ∨ p4) ∨ ((p1 ∨ p2) → (((True → ((p2 ∨ p1) → p2)) ∧ ((p1 ∧ p5) ∨ False)) → (False ∨ p5)))) := by
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
    -- Conjunctions on the left can always be decomposed.
    let h6 := h5.left
    let h7 := h5.right
    -- Disjunctions on the left can always be decomposed.
    cases h1
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
  case inr h10 =>
    -- False on the left can always be used.
    apply False.elim h10



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_302670873881504891336540872145 : (False ∨ (p2 ∨ (p4 → (p5 ∨ (((p2 ∧ ((p4 ∨ True) → p2)) ∧ p2) → ((p1 ∨ p5) ∨ ((p1 ∨ False) → ((p1 ∧ (p3 ∨ p2)) ∧ p1)))))))) := by
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
  -- Conjunctions on the left can always be decomposed.
  let h3 := h2.left
  let h4 := h2.right
  -- Conjunctions on the left can always be decomposed.
  let h5 := h3.left
  let h6 := h3.right
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h7
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Disjunctions on the left can always be decomposed.
  cases h7
  case inl h8 =>
    -- One of the premise coincides with the conclusion.
    exact h8
  case inr h9 =>
    -- False on the left can always be used.
    apply False.elim h9
  -- Disjunctions on the left can always be decomposed.
  cases h7
  case inl h10 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h4
  case inr h11 =>
    -- False on the left can always be used.
    apply False.elim h11
  -- Disjunctions on the left can always be decomposed.
  cases h7
  case inl h12 =>
    -- One of the premise coincides with the conclusion.
    exact h12
  case inr h13 =>
    -- False on the left can always be used.
    apply False.elim h13



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_197265715286081462576528339486 : (((((p5 → False) ∨ p3) ∧ (p3 → p1)) → False) ∨ (((p3 ∨ ((p5 → False) ∨ p4)) ∧ p1) → (((p3 ∨ p5) ∨ ((p5 ∧ False) ∧ True)) → True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_199402601628107992418232629211 : ((((p2 → p3) ∧ (True → (p4 ∨ p4))) ∨ p3) → (((p3 ∧ (((p5 ∨ (p5 → p3)) ∧ (p2 ∧ p3)) ∨ p5)) ∧ (False ∨ p4)) ∨ (p3 ∨ True))) := by
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
theorem thm_5_vars_178111921581807331421531594444 : (((((True → (p2 → (p1 ∨ (p2 ∨ p5)))) ∨ p4) → (p1 ∧ True)) → p5) ∨ (((p5 ∧ p4) → p2) ∨ ((p2 ∨ (True ∨ True)) ∨ (p3 → False)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
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
theorem thm_5_vars_154931233564934360489490631635 : ((((True ∨ True) → ((False → (p3 ∨ (p1 ∧ (p4 ∧ p4)))) ∧ (p3 ∧ p1))) ∨ (p3 ∨ (p4 ∨ True))) ∧ (((p2 ∧ True) ∧ False) → (True → True))) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_670739860486728640736251125982 : ((((True ∧ (p1 → (((p2 ∧ (p4 ∨ ((p5 ∨ (p2 ∧ p3)) ∨ (((p3 → p3) → False) → p2)))) ∨ p1) ∨ p5))) ∨ (p5 ∧ (True → False))) ∨ p5) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_136026824726044672516555451932 : (((((p1 → (p5 → False)) ∨ False) ∨ ((False → True) ∧ False)) → ((True ∨ p3) ∧ (p4 → ((p2 → (p2 ∧ p3)) → p1)))) ∨ ((True ∨ p5) ∨ p1)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_112226169129750931383508153606 : (((p1 ∨ (p1 ∨ (p1 → (p1 ∧ (((p2 ∧ (p3 ∨ p4)) ∨ p5) ∨ (((p1 ∧ ((True → p3) ∨ False)) ∧ True) → False)))))) ∨ p2) ∨ (True ∧ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_116304200944907990789707796075 : (((p1 → (p2 ∨ p5)) ∨ ((p2 ∨ (p3 ∧ ((False → p2) ∨ ((p4 → p4) → p4)))) → ((p2 → ((p4 → p5) ∨ p2)) ∨ False))) ∨ (p5 → p1)) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h2 =>
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Implications on the right can always be decomposed.
    intro h3
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h3
  case inr h4 =>
    -- Conjunctions on the left can always be decomposed.
    let h5 := h4.left
    let h6 := h4.right
    -- Disjunctions on the left can always be decomposed.
    cases h6
    case inl h7 =>
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- Implications on the right can always be decomposed.
      intro h8
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
      -- One of the premise coincides with the conclusion.
      exact h10



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_299183891817987538692506896209 : (False ∨ (((((p2 ∧ True) ∧ p2) ∨ (p3 ∨ ((((((p3 → False) ∧ (p1 → True)) ∧ p3) ∨ p4) ∨ p4) → (p2 → (p5 ∧ p2))))) → p4) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_262469632452882848151795555828 : (True ∧ ((p3 ∨ ((p1 → p4) → (p2 → ((True → True) ∧ (False ∨ (True ∧ ((((p4 → False) ∧ (p5 ∧ p3)) → (p5 → p1)) ∨ p3))))))) ∨ True)) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_321294463398225022908580514330 : (p4 ∨ (p5 ∨ ((((False ∧ True) ∧ p5) ∨ (p1 ∨ ((((p5 ∨ (p5 ∧ ((((p3 ∧ p1) ∨ p2) ∧ True) ∧ p1))) ∧ False) → p4) → True))) ∨ p4))) := by
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
  -- True on the right can always be proven directly.
  apply True.intro



