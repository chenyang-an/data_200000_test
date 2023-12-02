variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_225321258260588868138970716785 : (((False ∨ p5) ∧ p1) ∨ (((p2 → (True → (p4 → p5))) → (((p1 ∨ (p2 ∨ True)) ∨ p4) ∧ p3)) ∨ (p4 → ((p3 → p5) ∨ (p2 → p4))))) := by
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
theorem thm_5_vars_622605305508141776706134855571 : ((((p4 ∧ (((False → p5) ∧ (p3 ∨ (((True → (True ∨ True)) → (p1 ∨ (p3 ∨ (p1 ∧ (p3 ∨ p5))))) → (p3 → p1)))) → p2)) ∨ True) ∨ p5) ∧ True) := by
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
theorem thm_5_vars_83191771102993569892989085508 : ((((((True ∨ (((p1 ∨ False) ∧ (True ∨ (p2 → p3))) ∨ p1)) → p5) ∧ (p3 ∨ p3)) ∧ p5) ∧ (((p1 ∨ p2) ∧ (p1 ∨ p3)) → p1)) → p3) := by
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
  -- Disjunctions on the left can always be decomposed.
  cases h7
  case inl h8 =>
    -- One of the premise coincides with the conclusion.
    exact h8
  case inr h9 =>
    -- One of the premise coincides with the conclusion.
    exact h9



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_598057149632864588256587931969 : (((((False → (p5 ∧ p4)) ∧ ((((False ∨ True) ∧ p4) → ((p3 ∧ p3) → (p5 → (p5 ∨ p4)))) → ((True → (p2 ∧ False)) → False))) ∧ p5) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_313068220915791265405884983734 : (p3 ∨ (((p5 → (p2 ∧ (True → ((((True ∧ p4) ∨ (((((p5 ∨ True) ∨ False) ∧ p5) ∧ p2) ∨ True)) ∨ True) ∨ (True ∧ False))))) → p1) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_48068337107068522452374424300 : ((((p2 ∨ (p5 ∧ (p5 → (False ∨ (p3 ∧ p5))))) → (True → (p4 → (p1 → (((p5 ∧ p4) ∨ (p2 → True)) → p1))))) → (p5 ∧ p4)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_117521545766609404496378577632 : ((p2 ∧ (((p2 ∨ (p2 ∧ ((((p4 → ((p3 ∨ False) ∨ p4)) ∨ (p3 ∧ ((False → p3) → p4))) ∨ p1) → p3))) ∨ p2) → p3)) ∨ (p5 ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_673213328442727621992995357183 : (((((((p2 → (((p3 → p1) ∨ p3) ∧ p1)) → p2) → p5) → (p4 ∨ ((p4 → p1) ∧ (p3 ∧ (p5 ∨ p2))))) → ((True ∨ p3) → p1)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_715874051863469655556504356203 : (((((p4 ∧ (p2 ∨ p5)) ∨ False) ∧ (((p3 ∨ (p3 ∨ (p1 → (False → (((p3 ∨ p2) ∨ (p3 ∨ False)) → p2))))) → p4) ∨ (True ∨ p2))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_398479667306056556199452270441 : ((((p5 ∨ (p3 → (p4 ∨ (((((((p1 ∧ False) ∧ True) ∨ p4) ∧ ((p2 ∧ (p1 → p1)) ∨ (False ∧ p1))) → False) ∨ True) ∨ False)))) ∨ p4) ∧ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
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
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_611874931015475254955152472350 : (((((p4 → (p3 → (p5 ∧ (p3 ∧ (((False ∧ (True ∧ p1)) ∨ ((((p4 → p3) ∧ True) ∨ p5) → True)) → (p3 ∨ p4)))))) → p1) ∨ p5) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_313157010964499546844279658896 : (p3 ∨ (((((p4 ∧ p1) → ((p1 ∧ (False → (p4 ∧ False))) → True)) ∧ p3) ∨ ((p4 → (p5 → (p5 → False))) ∨ (p3 ∧ (p1 ∧ p5)))) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_148555359370758456320972502455 : (((((((p5 ∨ p5) → True) ∧ p1) → p5) ∨ (True ∨ p5)) ∧ (((p1 ∧ p2) ∨ (p5 ∧ p5)) → (p2 ∧ False))) ∨ ((p1 → (False → False)) → True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_197545944166646053947804923612 : ((((p5 ∨ (False ∨ p5)) ∨ p1) ∨ (True → p5)) ∨ ((((False ∧ ((p2 ∨ (False → (False → p4))) ∧ p1)) → p3) → p3) → (p4 → (p3 ∧ True)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h3 : ((False ∧ ((p2 ∨ (False → (False → p4))) ∧ p1)) → p3) := by
    -- Implications on the right can always be decomposed.
    intro h4
    -- Conjunctions on the left can always be decomposed.
    let h5 := h4.left
    let h6 := h4.right
    -- False on the left can always be used.
    apply False.elim h5
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h7 := h1 h3
  -- One of the premise coincides with the conclusion.
  exact h7
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_173180501902544661556434808732 : ((p4 ∨ ((p5 → (p5 ∧ (True → False))) ∨ (p3 ∧ (p3 → ((True → p5) ∨ p1))))) ∨ (p4 → (False → (False ∧ ((p5 ∨ p2) → (p5 ∨ p4)))))) := by
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
theorem thm_5_vars_348799614975198496074584940989 : (p3 → (p1 ∨ ((((p5 ∨ p2) → (((p2 → (p2 ∨ p4)) ∨ (p2 → ((p4 ∨ p3) ∧ p4))) → (p4 ∧ (p2 ∧ p5)))) → p1) ∨ (True ∨ p2)))) := by
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
theorem thm_5_vars_157718971790830857951188583030 : (((((p3 ∨ p2) ∧ True) → ((p2 → (p5 ∧ (p5 ∨ True))) ∨ (p1 ∨ p2))) → (p4 ∧ (p3 ∨ p1))) ∨ (False → (False ∧ ((p5 ∧ p3) ∧ False)))) := by
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
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_215363607039373362017696698340 : ((p2 ∧ ((p5 ∧ p4) ∨ False)) ∨ ((((True ∨ ((False → p3) → True)) → False) ∨ (False → ((p5 ∧ p5) ∨ (p3 ∨ ((True ∨ p5) → False))))) ∨ p1)) := by
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
theorem thm_5_vars_862355407229903871516689479981 : ((((((((p4 → p4) ∨ p5) ∧ p1) → (((p1 ∧ ((p5 → p5) → p1)) ∧ (p1 → p2)) ∨ p4)) → (((p3 ∨ True) → False) → p1)) → False) → p5) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h1
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h2 : (((((p4 → p4) ∨ p5) ∧ p1) → (((p1 ∧ ((p5 → p5) → p1)) ∧ (p1 → p2)) ∨ p4)) → (((p3 ∨ True) → False) → p1)) := by
    -- Implications on the right can always be decomposed.
    intro h3
    -- Implications on the right can always be decomposed.
    intro h4
    -- We want to use the implication h4 based on <expert-advice>. So we show its premise.
    have h5 : (p3 ∨ True) := by
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- True on the right can always be proven directly.
      apply True.intro
    -- We have shown the premise of h4, we can now drive its conclusion.
    let h6 := h4 h5
    -- False on the left can always be used.
    apply False.elim h6
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h7 := h1 h2
  -- False on the left can always be used.
  apply False.elim h7
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_231225508156968963800994025012 : (((p3 ∨ p5) ∨ p1) → ((((((p4 ∧ p1) ∧ ((p5 → p1) ∧ p3)) ∧ False) → p1) → (p2 ∨ (True → False))) ∨ (p2 ∨ (p1 → (p1 ∨ True))))) := by
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
      -- Implications on the right can always be decomposed.
      intro h4
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- One of the premise coincides with the conclusion.
      exact h4
    case inr h5 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Implications on the right can always be decomposed.
      intro h6
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- One of the premise coincides with the conclusion.
      exact h6
  case inr h7 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h8
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- One of the premise coincides with the conclusion.
    exact h8



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_152314172521949775326768101533 : (((((True → False) → p1) → p1) ∧ (((p5 ∨ (p1 ∨ False)) → (p4 ∨ (p2 → ((p2 ∧ p2) → p1)))) → True)) → ((False ∨ p1) ∨ (p4 ∧ True))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
  have h4 : ((True → False) → p1) := by
    -- Implications on the right can always be decomposed.
    intro h5
    -- We want to use the implication h5 based on <expert-advice>. So we show its premise.
    have h6 : True := by
      -- True on the right can always be proven directly.
      apply True.intro
    -- We have shown the premise of h5, we can now drive its conclusion.
    let h7 := h5 h6
    -- False on the left can always be used.
    apply False.elim h7
  -- We have shown the premise of h2, we can now drive its conclusion.
  let h8 := h2 h4
  -- One of the premise coincides with the conclusion.
  exact h8



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_187354558576767623368449959347 : ((p3 ∧ ((((True ∨ True) ∧ (p5 ∧ p5)) ∨ (p2 ∧ p5)) ∧ p5)) → (((((p3 → False) ∨ (p2 → True)) ∨ p5) ∧ False) ∨ ((True → False) ∨ True))) := by
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
    let h7 := h6.left
    let h8 := h6.right
    -- Disjunctions on the left can always be decomposed.
    cases h7
    case inl h9 =>
      -- Conjunctions on the left can always be decomposed.
      let h10 := h8.left
      let h11 := h8.right
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- True on the right can always be proven directly.
      apply True.intro
    case inr h12 =>
      -- Conjunctions on the left can always be decomposed.
      let h13 := h8.left
      let h14 := h8.right
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- True on the right can always be proven directly.
      apply True.intro
  case inr h15 =>
    -- Conjunctions on the left can always be decomposed.
    let h16 := h15.left
    let h17 := h15.right
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_672626868313323825541163311165 : (((((((p3 ∧ ((p4 ∧ True) → ((p2 ∧ False) → ((p4 → True) ∨ (True ∨ False))))) ∧ p2) ∨ False) ∨ (p3 ∧ p1)) → (True ∧ (p4 ∧ False))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_119118090066331839198447712211 : ((p1 → (True ∧ ((((True ∨ p4) ∧ p5) ∨ (((p4 ∧ p2) → p1) ∨ ((p1 ∨ ((p4 ∨ False) → p1)) → (True ∨ p4)))) → p4))) ∨ (p5 ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_116265436406547723244934004505 : (((p3 ∧ (False ∧ p2)) ∨ (p4 → (((p3 ∧ p1) → (p3 ∨ p4)) → (p1 → (False ∨ ((p5 ∨ (p2 ∨ (True ∧ p1))) ∨ p3)))))) ∨ (p3 ∧ p1)) := by
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
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
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
  -- One of the premise coincides with the conclusion.
  exact h3



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_182079270966505930961899524759 : (((False ∧ (p4 ∨ ((p1 ∨ p2) ∨ ((False → p3) ∨ p4)))) ∨ True) ∧ ((((p2 → (p2 ∨ (False ∨ p3))) → False) ∧ ((False ∨ p2) → p4)) → False)) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
  have h4 : (p2 → (p2 ∨ (False ∨ p3))) := by
    -- Implications on the right can always be decomposed.
    intro h5
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- One of the premise coincides with the conclusion.
    exact h5
  -- We have shown the premise of h2, we can now drive its conclusion.
  let h6 := h2 h4
  -- False on the left can always be used.
  apply False.elim h6



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_137829217964110018782582463544 : ((p3 ∨ (((p2 ∧ (((True ∧ ((p5 → p3) → ((p2 ∧ p2) → p4))) → p1) → (p3 ∨ p1))) → p5) ∨ (p3 → True))) ∨ (False ∧ (True ∨ p2))) := by
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



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_147844300728836513261874616855 : (((p4 ∨ ((((p4 ∨ p3) ∨ p2) ∨ (p1 ∧ p3)) → ((False ∨ (p4 ∧ (p4 ∧ p2))) → (True ∨ p5)))) → p2) ∨ ((False → (p1 ∧ p1)) ∨ p1)) := by
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
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_302847192083084534653175300685 : (False ∨ (p5 ∨ (p4 ∨ ((p3 ∧ (True ∧ (p5 → p2))) → (((((p1 → p3) → (p5 → (False ∧ True))) → False) ∧ (True → (p2 → False))) → p1))))) := by
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
  -- Conjunctions on the left can always be decomposed.
  let h5 := h1.left
  let h6 := h1.right
  -- Conjunctions on the left can always be decomposed.
  let h7 := h6.left
  let h8 := h6.right
  -- We want to use the implication h3 based on <expert-advice>. So we show its premise.
  have h9 : ((p1 → p3) → (p5 → (False ∧ True))) := by
    -- Implications on the right can always be decomposed.
    intro h10
    -- Implications on the right can always be decomposed.
    intro h11
    -- Conjunctions on the right can always be decomposed.
    apply And.intro
    -- We want to use the implication h4 based on <expert-advice>. So we show its premise.
    have h12 : True := by
      -- True on the right can always be proven directly.
      apply True.intro
    -- We have shown the premise of h4, we can now drive its conclusion.
    let h13 := h4 h12
    -- We want to use the implication h13 based on <expert-advice>. So we show its premise.
    have h14 : p2 := by
      -- We want to use the implication h8 based on <expert-advice>. So we show its premise.
      have h15 : p5 := by
        -- One of the premise coincides with the conclusion.
        exact h11
      -- We have shown the premise of h8, we can now drive its conclusion.
      let h16 := h8 h15
      -- One of the premise coincides with the conclusion.
      exact h16
    -- We have shown the premise of h13, we can now drive its conclusion.
    let h17 := h13 h14
    -- False on the left can always be used.
    apply False.elim h17
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h3, we can now drive its conclusion.
  let h18 := h3 h9
  -- False on the left can always be used.
  apply False.elim h18



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_636306646285661860087723717055 : ((((((False ∨ ((True ∨ (p5 ∨ p3)) ∧ ((p4 ∨ p4) ∨ ((p4 → p3) ∧ True)))) ∨ p1) → (p1 ∨ ((False ∧ p3) ∧ (p2 → p5)))) → p4) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_172363275634487377057898799861 : ((((p1 → (p2 ∨ p1)) → (p1 ∨ p1)) ∨ ((((True ∨ False) ∨ p1) → True) ∨ p4)) ∨ (((p1 → (p5 → ((p2 ∨ p3) ∨ p5))) ∨ True) ∨ p5)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_44626690868440105232996594357 : ((((((p5 ∨ p1) ∧ p2) → (p4 → p3)) ∧ (((p3 ∧ ((p2 ∨ p3) ∨ (p1 ∧ p1))) → (p5 → ((p5 → p3) ∨ False))) → p3)) → p4) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_655416888245332249731949066407 : (((((((p1 → (p2 ∧ (p1 → True))) ∨ True) → (((p4 ∨ (p2 ∨ (p1 → p3))) ∧ p4) ∧ (p5 ∨ p3))) ∨ (False → p3)) ∨ (False ∨ p2)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_154213261423495912953364765458 : (((((True → (False → (p2 ∨ ((p5 → (p4 ∧ p3)) ∧ p1)))) ∧ p1) → ((p4 ∨ True) → p5)) ∨ True) ∧ ((((p5 → True) → p1) ∨ True) ∨ False)) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_319061453137634669482888955832 : (p4 ∨ ((False ∨ ((p5 ∨ ((True ∧ ((p5 ∨ ((True ∧ False) ∧ (p5 ∨ p5))) → (p4 ∨ True))) → p5)) ∨ True)) ∨ (((p3 → False) → False) → p2))) := by
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
theorem thm_5_vars_114668967242058414679401728811 : ((((p5 ∨ p4) ∨ (((((p3 ∧ True) → p2) ∧ (p3 → p3)) → False) ∨ (p5 ∨ p1))) ∨ (False ∨ (p5 ∨ ((p1 ∨ True) ∨ p2)))) ∨ (p3 ∧ p3)) := by
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
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_339145360861304713026684608669 : (p1 → (p1 ∧ ((p2 → (p5 ∨ (p2 → p3))) ∨ (((p4 → (p2 ∧ (False ∨ (False ∧ p5)))) → (True ∧ p5)) ∨ (p3 ∨ (p5 ∨ (p2 ∨ True))))))) := by
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
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_259613501003051799568689009650 : ((p1 → False) → (((((p3 ∨ ((((p1 ∧ (p3 ∧ p3)) ∨ (((False → p3) ∧ True) ∧ p5)) → False) → (True ∧ True))) ∨ False) ∧ p1) → p2) ∨ False)) := by
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
    -- Disjunctions on the left can always be decomposed.
    cases h5
    case inl h6 =>
      -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
      have h7 : p1 := by
        -- One of the premise coincides with the conclusion.
        exact h4
      -- We have shown the premise of h1, we can now drive its conclusion.
      let h8 := h1 h7
      -- False on the left can always be used.
      apply False.elim h8
    case inr h9 =>
      -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
      have h10 : p1 := by
        -- One of the premise coincides with the conclusion.
        exact h4
      -- We have shown the premise of h1, we can now drive its conclusion.
      let h11 := h1 h10
      -- False on the left can always be used.
      apply False.elim h11
  case inr h12 =>
    -- False on the left can always be used.
    apply False.elim h12



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_351542674786787409461947782645 : (p4 → ((p1 ∧ ((((p1 → (p2 ∧ p1)) → ((False ∨ False) ∨ (p3 ∧ (False ∧ True)))) ∨ p1) ∨ p5)) ∨ (p4 ∨ (p1 ∨ (False ∨ (p1 → False)))))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_119070602275017761186951788397 : ((p1 → (((((True ∧ p4) ∨ p3) ∧ p2) ∨ (p3 ∨ (p5 ∨ (((((p4 ∧ p1) → p5) → p4) ∧ p5) ∨ p3)))) ∨ (p5 ∧ p2))) ∨ (p2 ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_260709330377374159551129091280 : ((p3 → p4) → (((True ∧ False) ∨ ((True → ((((p1 → False) → False) ∧ (False ∨ p1)) → False)) ∨ (((False ∨ (p2 → p2)) → p4) ∨ True))) ∨ p5)) := by
  -- Implications on the right can always be decomposed.
  intro h1
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
theorem thm_5_vars_158807797283451981075400246439 : ((p5 ∧ (p5 ∧ ((True → (((p2 ∧ p4) ∨ ((False ∨ (p2 → (p3 ∨ p4))) → p2)) ∧ p1)) → p4))) ∨ (p5 → (((p4 ∨ True) → p3) → True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_266253128044725220542329960010 : (True ∧ (p5 → (((((True ∧ (p4 ∧ True)) → p4) → ((False ∨ (p3 ∨ p2)) → p5)) → (False ∧ (((p5 → p2) ∨ True) → False))) ∨ (p5 → p5)))) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h2
  -- One of the premise coincides with the conclusion.
  exact h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_43977512584950509635875723681 : ((((p5 → ((((True ∨ p5) ∨ (((p5 ∧ ((p1 ∨ (p4 ∧ p4)) ∧ (p3 → False))) ∨ p3) → p3)) → p2) → p5)) ∨ (p2 ∧ True)) → p1) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_55795920245205698071382831179 : ((((p4 ∨ p2) ∨ (p2 ∧ p1)) ∧ ((((p4 ∨ p3) ∧ p5) ∧ False) ∨ ((p3 → ((True → p3) → ((p2 → p1) ∧ (True ∧ True)))) → p2))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_605074475914184206118719397006 : ((((p2 → ((((p3 ∧ ((p5 ∨ p2) ∨ False)) ∧ (p1 ∨ (p4 ∨ (p4 → (True ∨ (True ∨ p4)))))) ∨ ((False ∨ p2) → p2)) → p5)) ∧ p1) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_127440432886780380624591917799 : ((p3 ∨ (((p4 → p4) ∨ p2) ∧ ((p3 ∨ (p2 → (((((p2 → (p5 ∧ p2)) ∨ p2) ∨ (p2 ∨ p2)) ∧ False) ∧ False))) ∧ p4))) → (p5 → p5)) := by
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
      -- Conjunctions on the left can always be decomposed.
      let h8 := h6.left
      let h9 := h6.right
      -- Disjunctions on the left can always be decomposed.
      cases h8
      case inl h10 =>
        -- One of the premise coincides with the conclusion.
        exact h2
      case inr h11 =>
        -- One of the premise coincides with the conclusion.
        exact h2
    case inr h12 =>
      -- Conjunctions on the left can always be decomposed.
      let h13 := h6.left
      let h14 := h6.right
      -- Disjunctions on the left can always be decomposed.
      cases h13
      case inl h15 =>
        -- One of the premise coincides with the conclusion.
        exact h2
      case inr h16 =>
        -- One of the premise coincides with the conclusion.
        exact h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_186980368544218460076138812560 : (((p5 ∨ (p3 ∨ p2)) ∨ (p3 ∧ (((p1 ∨ p1) ∧ False) ∧ True))) → (True → (((True → ((p3 → p1) ∨ (p2 ∨ (p3 → False)))) ∨ p1) ∨ True))) := by
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
      -- True on the right can always be proven directly.
      apply True.intro
    case inr h5 =>
      -- Disjunctions on the left can always be decomposed.
      cases h5
      case inl h6 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- True on the right can always be proven directly.
        apply True.intro
      case inr h7 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- True on the right can always be proven directly.
        apply True.intro
  case inr h8 =>
    -- Conjunctions on the left can always be decomposed.
    let h9 := h8.left
    let h10 := h8.right
    -- Conjunctions on the left can always be decomposed.
    let h11 := h10.left
    let h12 := h10.right
    -- Conjunctions on the left can always be decomposed.
    let h13 := h11.left
    let h14 := h11.right
    -- Disjunctions on the left can always be decomposed.
    cases h13
    case inl h15 =>
      -- False on the left can always be used.
      apply False.elim h14
    case inr h16 =>
      -- False on the left can always be used.
      apply False.elim h14



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_777610048178593277345974482948 : (((p1 ∨ ((False ∨ ((((True → p1) ∧ p4) → True) ∧ (p1 → p1))) ∧ (p4 ∧ (((p5 ∧ p3) ∧ ((True → p5) ∧ False)) ∨ (p5 ∨ p3))))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_116829565596273032146653210449 : (((p5 ∨ p2) ∨ (True ∧ (p1 ∧ ((p3 ∨ (True ∨ (False ∧ (p5 ∧ (False ∧ False))))) → ((True → (True ∨ p4)) ∧ (True → False)))))) ∨ (True ∨ p2)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_76885229733326834540816128100 : ((((p2 ∨ (((p4 ∧ (p3 ∨ p1)) ∨ (p1 → p3)) → p1)) ∨ ((False ∧ (True ∨ (p4 → p3))) → (p3 ∧ (p1 ∨ (p1 ∧ p5))))) → p3) → p3) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h2 : ((p2 ∨ (((p4 ∧ (p3 ∨ p1)) ∨ (p1 → p3)) → p1)) ∨ ((False ∧ (True ∨ (p4 → p3))) → (p3 ∧ (p1 ∨ (p1 ∧ p5))))) := by
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h3
    -- Conjunctions on the right can always be decomposed.
    apply And.intro
    -- Conjunctions on the left can always be decomposed.
    let h4 := h3.left
    let h5 := h3.right
    -- False on the left can always be used.
    apply False.elim h4
    -- Conjunctions on the left can always be decomposed.
    let h6 := h3.left
    let h7 := h3.right
    -- False on the left can always be used.
    apply False.elim h6
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h8 := h1 h2
  -- One of the premise coincides with the conclusion.
  exact h8



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_116599102260625090621890886505 : (((p5 ∨ p3) ∧ (((True ∧ (False ∧ p2)) ∨ ((p2 ∨ ((p4 → p3) ∨ (p3 ∨ p5))) ∨ (p1 ∨ (p2 ∧ p3)))) → (True ∧ p4))) ∨ (False → False)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_620106882812692449541386730690 : (((((False ∧ True) ∨ ((((p2 ∧ True) → (p5 ∧ p1)) → p5) ∧ (((p5 → p2) ∨ ((p4 → p4) ∨ ((p1 ∨ p3) ∧ p2))) ∧ p2))) ∨ True) ∨ p4) ∧ True) := by
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
theorem thm_5_vars_137712632989557818916482734872 : ((p1 ∨ ((p1 ∨ ((p2 ∧ p4) → (p5 ∧ p2))) → (((False → p5) ∧ (p4 ∧ ((p5 → p4) ∨ True))) ∨ (p3 → p1)))) ∨ (False → (p4 → False))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_725694546902246222776791494696 : (((((False ∨ False) ∧ False) ∨ (((True ∨ p3) → True) ∧ ((p3 → ((((False ∧ p1) ∧ p3) ∧ p5) ∨ (False → ((p3 ∧ p2) ∨ True)))) → p2))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_90927375446110665609076619335 : (((True → p1) ∧ (((p1 ∨ p3) ∨ p3) → (((p2 ∧ p5) ∨ False) → (p2 ∨ ((p1 ∧ ((((p5 → False) ∧ False) ∨ p2) ∧ p5)) ∧ p5))))) → p1) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
  have h4 : True := by
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h2, we can now drive its conclusion.
  let h5 := h2 h4
  -- One of the premise coincides with the conclusion.
  exact h5



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_614524243923604092765080373994 : (((((((((p4 ∧ (True ∧ p5)) ∧ p4) ∧ False) ∨ ((p5 ∧ True) ∨ False)) ∨ ((p2 ∧ p4) ∨ p1)) ∧ (((p2 ∨ p1) ∨ p4) → False)) ∨ True) ∨ p5) ∧ True) := by
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
theorem thm_5_vars_851648347648917749763774355981 : ((((True → ((p5 ∧ (((p3 ∧ ((False → (((p5 ∧ p4) → p1) ∧ p2)) ∧ p1)) → p2) ∧ (p5 ∧ False))) ∧ ((p1 → p5) ∨ p5))) ∨ False) → p3) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h1
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h2 =>
    -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
    have h3 : True := by
      -- True on the right can always be proven directly.
      apply True.intro
    -- We have shown the premise of h2, we can now drive its conclusion.
    let h4 := h2 h3
    -- We need to get the left conjuct of h4 based on <expert-advice>.
    let h5 := h4.left
    -- We need to get the right conjuct of h5 based on <expert-advice>.
    let h6 := h5.right
    -- We need to get the right conjuct of h6 based on <expert-advice>.
    let h7 := h6.right
    -- We need to get the right conjuct of h7 based on <expert-advice>.
    let h8 := h7.right
    -- False on the left can always be used.
    apply False.elim h8
  case inr h9 =>
    -- False on the left can always be used.
    apply False.elim h9
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_153034384259280931442119901921 : ((p2 ∧ ((p3 ∧ p2) ∨ (((True → (False ∧ p1)) ∨ (((p1 ∧ True) ∧ True) ∧ (p3 ∨ p5))) → (p2 → p3)))) → ((True → p5) → (p5 ∨ p5))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Conjunctions on the left can always be decomposed.
  let h3 := h1.left
  let h4 := h1.right
  -- Disjunctions on the left can always be decomposed.
  cases h4
  case inl h5 =>
    -- Conjunctions on the left can always be decomposed.
    let h6 := h5.left
    let h7 := h5.right
    -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
    have h8 : True := by
      -- True on the right can always be proven directly.
      apply True.intro
    -- We have shown the premise of h2, we can now drive its conclusion.
    let h9 := h2 h8
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- One of the premise coincides with the conclusion.
    exact h9
  case inr h10 =>
    -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
    have h11 : True := by
      -- True on the right can always be proven directly.
      apply True.intro
    -- We have shown the premise of h2, we can now drive its conclusion.
    let h12 := h2 h11
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- One of the premise coincides with the conclusion.
    exact h12



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_188386118403521319107379420097 : ((((p2 ∧ (p4 ∧ (p2 → (p1 ∨ p2)))) → p4) → True) ∧ ((p4 ∨ ((p2 ∧ True) ∨ (((p2 ∨ p3) ∧ p4) ∨ p1))) ∨ (True ∧ (False → p5)))) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- Implications on the right can always be decomposed.
  intro h2
  -- False on the left can always be used.
  apply False.elim h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_610364316904849654544944324981 : (((((((p3 ∨ (((p5 ∨ ((p2 ∧ (p1 → ((p4 ∨ ((p2 ∧ False) → p4)) → True))) ∨ True)) ∧ p4) ∧ p1)) ∨ p4) → p2) → p4) ∨ False) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_317618512188911279588853751038 : (p4 ∨ ((((((p5 ∨ p1) ∧ p2) ∧ ((True ∨ ((((p3 ∨ False) ∧ p5) → ((p3 → p2) ∧ (True → p5))) ∧ True)) → p3)) ∨ True) ∨ p1) ∨ p2)) := by
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
theorem thm_5_vars_719606544684047291494537327909 : ((((p5 ∨ ((False ∧ p5) ∧ p3)) ∨ ((p4 ∨ (p3 → ((False → ((p2 → p2) ∨ True)) ∧ (((True → False) → p2) ∨ p4)))) ∨ (p3 → False))) ∨ p4) ∧ True) := by
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
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h2
  -- False on the left can always be used.
  apply False.elim h2
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h3
  -- We want to use the implication h3 based on <expert-advice>. So we show its premise.
  have h4 : True := by
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h3, we can now drive its conclusion.
  let h5 := h3 h4
  -- False on the left can always be used.
  apply False.elim h5
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_697149039889058282309803754007 : (((((p3 ∧ ((p1 ∨ p2) ∨ True)) → ((p4 ∨ (False ∧ p2)) ∧ p3)) ∧ (p5 ∧ ((((False ∧ p3) → (p1 → p1)) → p4) ∨ (p1 → False)))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_157686997075602308327526308407 : (((p4 ∨ (((True ∧ (p5 ∨ False)) ∧ (False ∧ ((p1 ∨ False) → p3))) ∧ p2)) ∨ ((p5 ∧ p3) → p1)) ∨ (True ∧ (p2 → ((False ∨ False) ∨ p2)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_309492147083359462450801992442 : (p2 ∨ (((p4 → p1) ∧ ((p5 ∨ p1) ∧ (p5 → ((p5 → ((p1 ∨ (p5 → p5)) ∨ (p5 → p4))) ∧ (True ∧ (p3 ∧ True)))))) → (p1 → p1))) := by
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
  let h5 := h4.left
  let h6 := h4.right
  -- Disjunctions on the left can always be decomposed.
  cases h5
  case inl h7 =>
    -- One of the premise coincides with the conclusion.
    exact h2
  case inr h8 =>
    -- One of the premise coincides with the conclusion.
    exact h8



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_341910960933391943665851509786 : (p2 → (((p4 ∨ ((True → (((p3 ∨ (p5 ∧ (p1 ∧ (p2 ∧ p3)))) ∨ (True ∨ p2)) → (p1 ∨ True))) → p4)) → p4) ∧ (False ∨ (p4 → p2)))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h2
  -- Disjunctions on the left can always be decomposed.
  cases h2
  case inl h3 =>
    -- One of the premise coincides with the conclusion.
    exact h3
  case inr h4 =>
    -- We want to use the implication h4 based on <expert-advice>. So we show its premise.
    have h5 : (True → (((p3 ∨ (p5 ∧ (p1 ∧ (p2 ∧ p3)))) ∨ (True ∨ p2)) → (p1 ∨ True))) := by
      -- Implications on the right can always be decomposed.
      intro h6
      -- Implications on the right can always be decomposed.
      intro h7
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
          -- Conjunctions on the left can always be decomposed.
          let h11 := h10.left
          let h12 := h10.right
          -- Conjunctions on the left can always be decomposed.
          let h13 := h12.left
          let h14 := h12.right
          -- Conjunctions on the left can always be decomposed.
          let h15 := h14.left
          let h16 := h14.right
          -- Show the left disjunct based on <expert-advice>.
          apply Or.inl
          -- One of the premise coincides with the conclusion.
          exact h13
      case inr h17 =>
        -- Disjunctions on the left can always be decomposed.
        cases h17
        case inl h18 =>
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- True on the right can always be proven directly.
          apply True.intro
        case inr h19 =>
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- True on the right can always be proven directly.
          apply True.intro
    -- We have shown the premise of h4, we can now drive its conclusion.
    let h20 := h4 h5
    -- One of the premise coincides with the conclusion.
    exact h20
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h21
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_344468113493628327607962786602 : (p2 → (True → ((((((False ∧ ((p5 ∧ (p5 → p5)) → (p5 ∧ (True ∧ True)))) ∧ (False ∧ True)) → ((True ∨ p5) → p2)) ∨ p2) → p5) ∨ p2))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_473602580530638341557043405507 : (((((p5 ∧ True) ∧ ((p4 ∨ p4) ∧ (p5 ∧ ((False → False) ∨ p1)))) → ((True → ((p4 ∧ False) ∧ ((False ∨ p3) ∧ (p2 → p4)))) ∨ p5)) ∧ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
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
  -- Disjunctions on the left can always be decomposed.
  cases h6
  case inl h8 =>
    -- Conjunctions on the left can always be decomposed.
    let h9 := h7.left
    let h10 := h7.right
    -- Disjunctions on the left can always be decomposed.
    cases h10
    case inl h11 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- One of the premise coincides with the conclusion.
      exact h9
    case inr h12 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- One of the premise coincides with the conclusion.
      exact h9
  case inr h13 =>
    -- Conjunctions on the left can always be decomposed.
    let h14 := h7.left
    let h15 := h7.right
    -- Disjunctions on the left can always be decomposed.
    cases h15
    case inl h16 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- One of the premise coincides with the conclusion.
      exact h14
    case inr h17 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- One of the premise coincides with the conclusion.
      exact h14
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_119796881218789491598655937348 : ((((((False → p1) ∨ (((p3 ∧ p3) ∨ False) → (((False ∧ (p1 ∨ p1)) ∧ p1) → (p5 ∧ (p2 ∧ p2))))) → p3) → False) ∧ p4) → (p2 → p2)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Conjunctions on the left can always be decomposed.
  let h3 := h1.left
  let h4 := h1.right
  -- One of the premise coincides with the conclusion.
  exact h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_652329308056039528894419623232 : ((((p4 ∧ (((((p1 → (((p2 → p1) ∨ p1) ∧ p3)) → p1) → (p2 ∧ (p2 → (p5 ∧ (p1 → False))))) → p1) ∧ p1)) ∧ (p3 ∨ True)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_214680960120562685257110827336 : (((p5 → p1) ∧ (True → False)) ∨ ((((p1 → True) ∧ ((False → ((p2 → p5) ∨ ((p3 → (p2 → (p1 → p3))) → p1))) ∨ p3)) → p4) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_43338851348123343685737228304 : (((((((p4 ∨ p1) → (p5 → p5)) ∧ (((False → p3) → (p2 → True)) → ((p5 → p5) → (p4 ∧ (p4 ∧ p5))))) → p4) ∨ False) → False) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_350109293679389356199223961671 : (p4 → ((((p3 ∨ ((p1 ∨ (p4 → (p1 ∧ p3))) ∧ (False → (((p4 ∧ p2) ∧ False) ∧ False)))) ∧ False) ∨ ((p5 ∨ p2) ∧ (p5 → p5))) ∨ True)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_55366446400881773099011257729 : (((p5 → ((p4 ∧ p5) ∨ (p3 → p1))) ∨ ((((True ∨ p3) ∨ (p1 ∨ (p3 → True))) → (p2 ∧ (False ∧ (p2 → p4)))) ∨ (True ∨ p1))) ∨ p1) := by
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
theorem thm_5_vars_198753597888125008848274006645 : ((True → (((p3 ∨ False) ∨ p3) ∨ (p1 ∧ p4))) ∨ (((p3 ∧ False) ∨ p2) ∨ (((True ∧ ((p1 ∧ (p3 ∨ p5)) ∧ True)) ∨ True) ∨ (p4 ∨ p2)))) := by
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
theorem thm_5_vars_186771053557304009984310572585 : (((p1 ∨ ((p1 ∧ p2) ∧ (p4 ∧ p3))) → (False ∧ (False ∨ True))) → (((p2 ∨ p1) → (p4 → p3)) ∨ (p5 → (((True ∨ True) → p5) ∧ True)))) := by
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
  -- Disjunctions on the left can always be decomposed.
  cases h3
  case inl h4 =>
    -- One of the premise coincides with the conclusion.
    exact h2
  case inr h5 =>
    -- One of the premise coincides with the conclusion.
    exact h2
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_62486552461188400367039335601 : ((p3 ∧ ((p4 → p1) → (((((((p1 ∨ False) ∨ ((p1 → p5) ∨ (True → p1))) ∧ p5) ∧ p1) → p2) → ((p3 ∨ False) → p1)) ∨ p1))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_246568423053378161041164937710 : ((p5 ∧ p2) ∨ ((((p3 → (p3 ∨ ((p1 ∨ p4) ∧ ((p4 ∧ ((p5 ∨ p3) → ((p4 ∨ False) ∧ p4))) ∨ p4)))) → p5) ∧ p3) ∨ (False → p1))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_102874073163936502403471547219 : (((((p1 ∨ (p5 → ((p1 ∧ p4) ∨ ((False ∧ ((p2 → (p1 ∨ p4)) ∧ (False → False))) → p4)))) ∨ False) → (p1 → False)) ∨ True) ∧ (True → True)) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_158085686330188385694556408956 : (((p5 ∧ (p2 ∨ ((p4 ∨ p5) → p3))) → (p5 → ((True → (p2 ∧ (True ∧ False))) ∨ (True ∨ p4)))) ∨ (False → (p2 ∧ ((p3 → p1) ∧ p2)))) := by
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
  -- Implications on the right can always be decomposed.
  intro h2
  -- False on the left can always be used.
  apply False.elim h1
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_170046798786987386829556468692 : (((((((p5 → (p4 → p1)) → p4) → p4) ∧ p5) ∧ True) → ((p4 → False) ∨ p5)) ∧ ((((((p3 ∨ p4) ∨ True) ∨ True) ∨ True) → p4) → p4)) := by
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
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h5
  -- Implications on the right can always be decomposed.
  intro h6
  -- We want to use the implication h6 based on <expert-advice>. So we show its premise.
  have h7 : ((((p3 ∨ p4) ∨ True) ∨ True) ∨ True) := by
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h6, we can now drive its conclusion.
  let h8 := h6 h7
  -- One of the premise coincides with the conclusion.
  exact h8



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_701917828570028666003457150976 : ((((p1 ∨ (False ∧ ((((False ∧ True) ∧ p2) ∨ p3) ∧ p3))) ∧ ((p4 ∨ (p4 → (False ∨ p2))) → ((p5 → False) ∨ (True → (p3 → p5))))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_65574401921240517258932985930 : ((p3 ∨ (p4 → (p3 ∧ (((p5 → (True ∨ (p1 ∧ (p3 → ((p3 → p5) → (p1 → p1)))))) → (p5 ∧ (p1 ∨ (p2 ∨ p5)))) → p3)))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_171413059760564738163007005626 : (((((p5 → p4) ∨ p5) ∨ (((p1 ∧ (p2 → True)) → p2) → (True → False))) ∧ p1) ∨ (True → (((True ∨ p4) ∧ (p3 ∧ (p3 → p3))) → True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_677128419247041447340923952355 : ((((p5 → ((p1 ∧ (((p2 ∧ True) → (False ∧ True)) ∧ True)) ∨ (p2 → (((p2 ∨ False) ∧ p5) → p3)))) ∧ ((p1 ∧ p3) ∨ (p5 ∨ p5))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_148841700295196306529210359299 : (((((p2 → False) ∨ False) → False) ∧ (p3 ∧ ((((False ∨ (p4 ∧ p5)) ∨ ((True ∧ p1) ∧ p2)) → False) ∧ p5))) ∨ (p4 → ((True ∨ p2) ∨ p4))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_342770184767697987668295634560 : (p2 → ((True → (((p2 ∨ p5) ∧ (p2 → p1)) ∧ p4)) ∨ (((p1 → p2) → p4) → (p4 → (p1 ∨ (p1 ∨ (p5 ∨ ((p2 → p2) ∧ True)))))))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h2
  -- Implications on the right can always be decomposed.
  intro h3
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h4
  -- One of the premise coincides with the conclusion.
  exact h4
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_134392718924082403914437604501 : (((True → ((p3 → (((p2 ∧ ((p3 ∨ p2) ∨ (((p4 ∨ p5) ∧ p4) → p2))) ∧ (p1 → False)) ∨ p5)) ∧ True)) ∨ p1) ∨ (p3 ∨ (False → p1))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_52104361236769537969504805084 : ((((p5 ∨ (True ∧ (((p1 → False) ∨ True) → (p2 ∨ ((p3 ∨ False) ∨ p2))))) ∨ p5) → ((p4 → ((p3 ∧ True) ∧ p5)) → (p1 ∧ p4))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_219379826406935155355275637845 : ((p3 ∨ ((False → False) → p3)) → ((p4 ∨ p3) ∨ (((False ∨ (p1 → p5)) → ((p3 ∨ p3) → (p3 → (False ∨ (p2 ∨ (p1 → True)))))) ∨ p4))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h2 =>
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h2
  case inr h3 =>
    -- We want to use the implication h3 based on <expert-advice>. So we show its premise.
    have h4 : (False → False) := by
      -- Implications on the right can always be decomposed.
      intro h5
      -- False on the left can always be used.
      apply False.elim h5
    -- We have shown the premise of h3, we can now drive its conclusion.
    let h6 := h3 h4
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h6



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_44381503474232460283038922449 : ((((((p1 → p3) → ((p2 ∨ (((p5 ∨ p2) → p1) → p2)) ∧ p5)) ∨ p5) ∨ ((p2 → (p4 ∧ p5)) ∧ (p1 ∨ (p5 → False)))) → p4) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_628628854592088020277728071510 : (((((p3 ∨ ((((((p1 → p5) ∨ p3) → p1) ∨ p2) → (p3 ∨ (False → p5))) ∨ ((p1 → p4) ∨ ((p4 ∨ p5) ∨ False)))) ∧ p4) → p5) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_209507058373528205320458777594 : ((p4 → ((p1 ∨ (p2 → p5)) ∧ True)) → (((True ∧ (p2 ∨ ((False ∧ (p5 ∨ p3)) ∨ p5))) ∨ ((((True ∧ p2) → p1) ∨ True) → p2)) ∨ True)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_206391800875754937060480630645 : ((p3 ∨ ((p5 ∧ (p3 ∧ p3)) ∨ False)) ∨ ((p5 ∧ p2) → (True ∧ (((True → True) ∨ (p3 ∨ (False ∨ ((False ∧ (p4 ∨ p4)) → p5)))) ∨ p2)))) := by
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
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h3



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_178116042796784446357556364511 : ((((p2 ∨ (((p1 ∨ (p1 ∨ True)) ∧ False) ∨ p5)) → (True ∧ p2)) → p2) ∨ (((((p5 → False) ∧ p5) ∨ (p3 ∧ p3)) ∧ p3) → (True ∧ True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_684782861372073710983206880165 : (((((p4 ∨ p2) ∨ ((p5 ∧ (True ∧ p4)) ∧ (p2 → (False ∨ (((p5 ∨ p3) ∧ p1) ∨ p5))))) ∨ (False ∨ ((False → (p3 → False)) ∨ True))) ∨ p4) ∧ True) := by
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
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_324398809918521050476190686756 : (p5 ∨ ((((p1 → (p2 ∨ p4)) ∨ False) → p1) → ((False ∧ (p1 ∨ (((p1 ∨ ((p3 ∨ p5) ∧ p5)) ∨ p5) ∨ ((p1 ∧ p3) → True)))) ∨ True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_117479823627980409312782048190 : ((p1 ∧ (p1 ∨ (True ∧ (p3 ∧ ((((False → False) → (p1 ∨ True)) ∧ ((p1 ∨ p5) ∧ p5)) ∧ (False → (False ∨ (False ∧ False)))))))) ∨ (True ∨ p3)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_190260275467103380586512988801 : (((((p5 ∧ ((p5 → p4) ∨ True)) ∧ False) ∨ p3) ∨ p2) ∨ ((p5 → (p5 → p2)) ∨ ((p5 ∨ ((True ∨ False) ∨ ((p3 → p5) ∧ p1))) ∨ p4))) := by
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
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



