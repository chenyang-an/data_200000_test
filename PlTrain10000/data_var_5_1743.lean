variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_148017041069491433575325614712 : (((((p1 ∧ ((p2 ∨ True) → p4)) → ((False ∧ p1) ∨ p3)) ∨ ((p1 → False) ∨ (p3 ∨ p5))) ∨ (p2 ∨ p1)) ∨ (False → (p2 → (p1 ∧ p1)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- False on the left can always be used.
  apply False.elim h1
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_135961195000995781659832002595 : (((p4 ∧ (((p3 ∨ (p2 ∧ p5)) ∧ p4) ∨ (p2 → p3))) ∧ ((p3 ∧ p4) → (((p4 → p3) → True) ∨ (p2 → p2)))) ∨ ((p2 → False) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_118466661061647455490576991596 : ((p3 ∨ ((((p5 ∨ ((True ∨ p2) ∧ (((p5 → (p4 ∧ True)) → ((True → p3) ∨ (p1 ∧ True))) ∨ False))) → p3) → p1) → p4)) ∨ (p2 → p2)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_616678290879984651255210558236 : ((((((((p4 ∨ False) ∧ ((p1 ∨ False) → p4)) ∧ False) ∧ p3) ∨ ((p1 → ((p3 → (True ∧ False)) → ((p2 → p1) ∨ p3))) ∨ p4)) ∨ p4) ∨ p3) ∧ True) := by
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
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h3
  -- One of the premise coincides with the conclusion.
  exact h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_715925657140297728600009328844 : (((((p4 ∨ (p4 ∨ p5)) ∨ p5) ∧ (p5 ∨ ((((p5 ∨ ((p2 → True) → (p4 ∧ False))) ∨ ((False ∧ p5) → True)) ∨ p3) → (p2 → p1)))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_116415260344594755166268476783 : (((p2 ∨ (p2 ∧ p3)) → (p3 → ((True → (False ∨ (False ∧ (((p1 ∧ p3) ∨ p2) → (True ∨ ((p2 → p4) ∧ p1)))))) ∨ p3))) ∨ (p3 ∨ False)) := by
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
    -- One of the premise coincides with the conclusion.
    exact h2
  case inr h4 =>
    -- Conjunctions on the left can always be decomposed.
    let h5 := h4.left
    let h6 := h4.right
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h6



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_140500140634086252108927889197 : (((((((p4 → p2) ∨ (p3 → p1)) ∧ p1) ∧ p5) → ((p4 → (p2 → p2)) ∧ p4)) ∧ (p1 ∨ ((p4 ∧ p5) ∧ p2))) → ((p1 → False) → p5)) := by
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
    -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
    have h6 : p1 := by
      -- One of the premise coincides with the conclusion.
      exact h5
    -- We have shown the premise of h2, we can now drive its conclusion.
    let h7 := h2 h6
    -- False on the left can always be used.
    apply False.elim h7
  case inr h8 =>
    -- Conjunctions on the left can always be decomposed.
    let h9 := h8.left
    let h10 := h8.right
    -- Conjunctions on the left can always be decomposed.
    let h11 := h9.left
    let h12 := h9.right
    -- One of the premise coincides with the conclusion.
    exact h12



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_143266271972990088612533876333 : ((p3 → (((True ∧ ((p3 ∨ p1) → p3)) ∧ False) ∨ (p4 → (((True ∧ p3) ∧ p1) → (((p4 ∨ p4) ∧ p2) ∨ p4))))) → ((p2 → p4) ∨ True)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_656712651381901955509516670571 : (((((p3 → ((p3 ∧ (p1 ∨ p2)) ∧ False)) ∧ ((p3 → ((p1 ∧ p3) ∨ True)) ∧ (((p1 ∨ (p5 ∨ p4)) → p3) → p2))) ∨ (p4 ∧ p5)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_48461668827849255258663547717 : ((((((p2 → ((p4 ∧ p4) → ((True ∧ (p1 → p1)) ∨ ((p1 ∧ (p1 → False)) ∨ p4)))) ∧ p3) → p5) ∧ p2) ∧ ((p5 ∧ p4) ∨ False)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_57220603269163817230439821101 : ((((p3 → p4) ∨ p2) ∨ (p5 → (((p4 ∨ False) ∨ ((p4 ∧ ((True ∨ (p2 ∨ (p3 ∧ p1))) ∨ (p4 ∨ (False → p4)))) ∧ p4)) ∨ False))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_38133379847430957895433114984 : (((((p3 ∨ p3) ∨ (False ∨ (p1 ∧ (False ∧ ((p3 ∨ p2) ∧ (True ∧ (((p1 ∨ p4) ∧ False) → False))))))) ∧ ((p2 → p5) ∨ True)) ∧ p1) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_756319286285315903362221288293 : (((p1 ∧ ((True ∨ (False ∨ ((((p4 → p1) → (p3 ∧ True)) → True) ∨ ((p4 → ((p5 ∨ p2) ∧ False)) ∨ (p1 ∨ True))))) → (p1 ∨ False))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_628015424019953592560050825369 : (((((((p5 ∧ (p5 → (p2 → p5))) ∧ p1) → (p5 ∧ (p3 → (p2 → (p4 → (p1 ∧ (False ∨ ((p3 ∧ p2) → p4)))))))) ∧ True) → p2) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_347015152076826469440588921260 : (p3 → (((p5 ∨ (p1 → (False ∧ (p3 ∧ p5)))) ∧ (((p5 ∧ p5) ∨ True) ∨ (p5 → p5))) ∨ ((True ∨ p5) ∨ (p5 ∨ (p4 ∧ (p4 → p2)))))) := by
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
theorem thm_5_vars_707667253935824582688620236835 : (((((p2 ∨ p4) ∨ ((p1 → False) ∧ (p5 → p1))) ∨ (False ∧ ((p5 → ((((p2 → p2) ∧ p4) ∧ (p2 ∧ (p2 → p2))) ∨ p1)) → True))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_40743583470832324564520006787 : (((((p3 ∧ (p5 → True)) ∨ (p5 → ((p3 ∨ ((False ∧ (((False ∧ p2) ∨ (False ∨ (True → True))) ∨ p3)) ∨ p3)) → False))) → p3) ∨ p1) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_61920957741460467112834750729 : ((p2 ∧ ((((((False ∨ True) → p2) ∨ (p1 → p2)) ∨ (False ∧ (((p2 ∧ False) ∨ p1) ∧ p3))) ∨ (True → p5)) → (p1 → (p3 ∧ p4)))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_213682724433920685089816360963 : ((((p5 → p1) ∨ p5) ∨ p5) ∨ ((((p2 → p5) ∧ (p5 → (((p3 ∧ False) ∧ p2) ∨ (((p5 ∧ p4) ∨ True) → p2)))) ∨ True) ∧ (True ∨ p5))) := by
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
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_134267347557070703809037834623 : ((((p4 → (False → p5)) → (p2 ∨ ((p3 ∧ (False ∧ ((p3 ∨ p5) ∧ (p4 → (p4 → p3))))) ∧ (p4 ∧ True)))) ∨ p3) ∨ (p5 → (p3 → True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_746702724445975077282982018287 : ((((p3 ∨ p2) → (((p4 → ((p3 ∧ p1) ∧ (p5 ∧ p4))) ∨ (p2 ∨ ((p5 → (True → p1)) → False))) ∨ ((p2 ∨ True) ∨ (True → p2)))) ∨ p5) ∧ True) := by
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
    -- True on the right can always be proven directly.
    apply True.intro
  case inr h3 =>
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- One of the premise coincides with the conclusion.
    exact h3
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_655583462348246395685135904560 : ((((((p1 → (p5 ∧ p4)) → ((p4 ∨ (p5 → ((p2 ∧ p5) → (False ∨ (p2 ∧ p1))))) ∧ (p1 ∨ p1))) → (p5 ∧ False)) ∨ (p3 ∧ p5)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_190530914934875039132565539568 : ((((p1 ∨ ((p4 → p2) → (False ∨ False))) → p3) → False) ∨ (p4 ∨ ((True → (p2 ∨ (((p2 → (p3 → p2)) → True) ∨ p2))) → (False ∨ True)))) := by
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
theorem thm_5_vars_181650414052349348482833237148 : ((p3 → ((True → p5) ∧ (p1 ∨ ((p5 ∧ (p4 → (False ∨ p2))) ∨ p5)))) → ((True → (p5 ∧ (((p2 ∧ (p1 → False)) ∧ False) ∧ p4))) → p3)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
  have h3 : True := by
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h2, we can now drive its conclusion.
  let h4 := h2 h3
  -- We need to get the right conjuct of h4 based on <expert-advice>.
  let h5 := h4.right
  -- We need to get the left conjuct of h5 based on <expert-advice>.
  let h6 := h5.left
  -- We need to get the right conjuct of h6 based on <expert-advice>.
  let h7 := h6.right
  -- False on the left can always be used.
  apply False.elim h7



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_135699171638150955159166424373 : ((((p3 → (((p5 → p3) ∨ False) ∨ p4)) ∨ ((p3 → (False ∧ p3)) ∧ p1)) ∧ (((False ∧ False) ∨ p4) ∨ (p2 ∧ p1))) ∨ ((p2 ∨ False) → True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_307752667684450321287784304006 : (p1 ∨ (p3 → ((((False → p2) ∧ (p2 ∧ p3)) → (False ∧ p5)) → ((p1 ∧ ((False ∨ False) ∧ (p2 ∨ False))) ∨ ((p3 → (p5 ∨ True)) ∨ True))))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_1950811685029736077361478729 : (((p3 → ((((p1 ∧ p4) → ((p2 → p5) → p3)) → ((True ∨ p4) ∧ p1)) ∧ p4)) ∧ (p1 ∨ p2)) ∨ ((True → (p1 → False)) → True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_314024833023891111272126371886 : (p3 ∨ ((p5 ∨ ((False → ((p3 ∨ p3) → ((p3 ∧ p3) ∧ (p3 ∨ False)))) → ((p5 ∧ ((p2 → (True ∨ p5)) → False)) → p1))) ∨ (p2 ∧ False))) := by
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
  have h5 : (p2 → (True ∨ p5)) := by
    -- Implications on the right can always be decomposed.
    intro h6
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h4, we can now drive its conclusion.
  let h7 := h4 h5
  -- False on the left can always be used.
  apply False.elim h7



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_33431863808603284224123132818 : ((p4 ∨ ((p5 ∧ (((p1 → (False ∨ False)) ∧ (p5 → p3)) → (p3 → True))) → ((p3 ∨ ((p2 → p2) → (p3 ∨ p4))) → (p4 ∨ p3)))) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
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
    let h4 := h1.left
    let h5 := h1.right
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h3
  case inr h6 =>
    -- Conjunctions on the left can always be decomposed.
    let h7 := h1.left
    let h8 := h1.right
    -- We want to use the implication h6 based on <expert-advice>. So we show its premise.
    have h9 : (p2 → p2) := by
      -- Implications on the right can always be decomposed.
      intro h10
      -- One of the premise coincides with the conclusion.
      exact h10
    -- We have shown the premise of h6, we can now drive its conclusion.
    let h11 := h6 h9
    -- Disjunctions on the left can always be decomposed.
    cases h11
    case inl h12 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- One of the premise coincides with the conclusion.
      exact h12
    case inr h13 =>
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- One of the premise coincides with the conclusion.
      exact h13
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_246235929213713953941193600553 : ((p4 ∧ p3) ∨ (False ∨ ((((p5 ∨ ((p4 ∨ (p5 → ((True → (p1 ∨ p1)) ∨ (p2 ∨ ((p2 ∨ p2) → p5))))) ∨ p3)) ∨ p5) ∨ p4) ∨ p5))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
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
  -- Disjunctions on the left can always be decomposed.
  cases h2
  case inl h3 =>
    -- One of the premise coincides with the conclusion.
    exact h1
  case inr h4 =>
    -- One of the premise coincides with the conclusion.
    exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_165320757057415110128993394598 : (((p3 → (p5 → (((True → p4) ∨ p5) ∨ (p2 ∧ (False ∧ (False ∧ p4)))))) → (p3 ∧ True)) ∨ (p3 → (p2 → (p4 → (p2 → (True ∨ p1)))))) := by
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
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_127031734783391732040430050928 : ((False ∨ ((((((True ∨ (p2 → p4)) → p1) ∧ False) → (p4 ∧ p2)) → ((((True → (p4 ∨ False)) ∧ p3) → p2) ∧ False)) ∨ False)) → (False ∨ False)) := by
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
      -- We want to use the implication h4 based on <expert-advice>. So we show its premise.
      have h5 : ((((True ∨ (p2 → p4)) → p1) ∧ False) → (p4 ∧ p2)) := by
        -- Implications on the right can always be decomposed.
        intro h6
        -- Conjunctions on the right can always be decomposed.
        apply And.intro
        -- Conjunctions on the left can always be decomposed.
        let h7 := h6.left
        let h8 := h6.right
        -- False on the left can always be used.
        apply False.elim h8
        -- Conjunctions on the left can always be decomposed.
        let h9 := h6.left
        let h10 := h6.right
        -- False on the left can always be used.
        apply False.elim h10
      -- We have shown the premise of h4, we can now drive its conclusion.
      let h11 := h4 h5
      -- We need to get the right conjuct of h11 based on <expert-advice>.
      let h12 := h11.right
      -- False on the left can always be used.
      apply False.elim h12
    case inr h13 =>
      -- False on the left can always be used.
      apply False.elim h13



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_807695556528549752057893324902 : (((p4 → (((p5 ∧ p3) ∧ p5) ∨ (((((((p3 ∨ (True ∨ p5)) ∧ (p1 → p5)) ∧ p2) → p5) ∨ p5) ∨ True) ∧ ((True ∨ p3) → p4)))) ∨ False) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- Implications on the right can always be decomposed.
  intro h2
  -- Disjunctions on the left can always be decomposed.
  cases h2
  case inl h3 =>
    -- One of the premise coincides with the conclusion.
    exact h1
  case inr h4 =>
    -- One of the premise coincides with the conclusion.
    exact h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_140275878703293003788629735921 : (((((True ∧ p4) → (p1 ∧ (((p1 ∧ ((p5 → True) → False)) → p4) ∨ p4))) ∨ (p3 ∨ p3)) ∧ (p1 ∧ (False → True))) → (p1 ∧ (p4 → p4))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- Disjunctions on the left can always be decomposed.
  cases h2
  case inl h4 =>
    -- Conjunctions on the left can always be decomposed.
    let h5 := h3.left
    let h6 := h3.right
    -- One of the premise coincides with the conclusion.
    exact h5
  case inr h7 =>
    -- Disjunctions on the left can always be decomposed.
    cases h7
    case inl h8 =>
      -- Conjunctions on the left can always be decomposed.
      let h9 := h3.left
      let h10 := h3.right
      -- One of the premise coincides with the conclusion.
      exact h9
    case inr h11 =>
      -- Conjunctions on the left can always be decomposed.
      let h12 := h3.left
      let h13 := h3.right
      -- One of the premise coincides with the conclusion.
      exact h12
  -- Implications on the right can always be decomposed.
  intro h14
  -- Conjunctions on the left can always be decomposed.
  let h15 := h1.left
  let h16 := h1.right
  -- Disjunctions on the left can always be decomposed.
  cases h15
  case inl h17 =>
    -- Conjunctions on the left can always be decomposed.
    let h18 := h16.left
    let h19 := h16.right
    -- One of the premise coincides with the conclusion.
    exact h14
  case inr h20 =>
    -- Disjunctions on the left can always be decomposed.
    cases h20
    case inl h21 =>
      -- Conjunctions on the left can always be decomposed.
      let h22 := h16.left
      let h23 := h16.right
      -- One of the premise coincides with the conclusion.
      exact h14
    case inr h24 =>
      -- Conjunctions on the left can always be decomposed.
      let h25 := h16.left
      let h26 := h16.right
      -- One of the premise coincides with the conclusion.
      exact h14



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_652764809340254249634212558656 : ((((p2 ∨ ((p1 ∧ p5) ∨ ((((p5 ∨ (True → ((p2 → p2) → False))) → (True → (p4 ∨ p4))) ∨ p1) ∨ (True → p2)))) ∧ (p2 ∨ p1)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_158888496430308101985971896597 : ((False ∨ (p2 → (False ∨ ((((p2 → p2) ∨ p3) ∨ p3) ∧ (p4 ∧ (p5 → (True ∨ (False ∨ p2)))))))) ∨ (True → ((p2 → True) ∨ (p5 → p3)))) := by
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
theorem thm_5_vars_678937705519459838466776728708 : ((((p4 ∧ ((p2 ∧ ((p2 ∨ p2) → (p1 ∨ (((p1 ∨ p5) ∨ (p4 ∧ (p1 → False))) → p2)))) ∧ True)) ∨ (p3 ∨ (p1 → (p1 → p1)))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_114129324694437543877998664552 : (((p4 → ((p5 → p1) → ((p3 → (p5 ∨ (False → p3))) → ((((p5 → p3) ∨ p2) ∧ True) ∨ p5)))) ∨ ((p3 → False) → p2)) ∨ (False → p2)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_262268628856342290171579477146 : (True ∧ ((((p3 ∧ ((p1 → True) → (((p3 ∨ p1) ∨ p1) → p4))) → ((False ∧ p1) ∧ (p5 ∧ p1))) ∧ (False → ((p3 → p3) ∨ p2))) ∨ True)) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_593062024416842421571849755407 : ((((((((p2 ∨ False) ∧ (((p5 ∧ p3) → (True ∧ (True ∨ (p4 ∧ p4)))) → (p3 → p5))) → p4) → p4) ∨ (p2 ∨ (p4 ∨ True))) ∧ True) ∨ p3) ∧ True) := by
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
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_59489005822834699462434433049 : (((p1 → p4) ∨ (p2 ∧ (((((p3 → False) ∨ p5) ∨ ((False ∧ p2) ∧ False)) ∧ p1) ∧ (True ∨ (((p3 → (False ∨ p4)) ∨ p5) ∧ p5))))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_197829829276472830601193218373 : (((p3 ∧ (p3 ∧ p5)) ∨ (p4 → (p3 ∧ p5))) ∨ ((False → ((p5 → (p4 → (p3 ∨ p4))) ∨ (p4 → p3))) ∨ (p1 ∨ ((p5 ∨ p4) ∨ p1)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_151145451761211985594658434310 : ((((True ∨ (((p5 ∧ p3) → (p5 ∧ True)) ∧ (((p1 ∧ (p2 → p2)) ∨ p2) → p1))) → (True ∧ True)) → p1) → ((p3 ∨ p1) ∨ (p1 → p2))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h2 : ((True ∨ (((p5 ∧ p3) → (p5 ∧ True)) ∧ (((p1 ∧ (p2 → p2)) ∨ p2) → p1))) → (True ∧ True)) := by
    -- Implications on the right can always be decomposed.
    intro h3
    -- Conjunctions on the right can always be decomposed.
    apply And.intro
    -- True on the right can always be proven directly.
    apply True.intro
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h4 := h1 h2
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h4



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_179722771477802918868437227094 : ((((((p4 ∨ (False → (p2 → p2))) → p4) → (p3 → p4)) → False) ∧ p2) → (p4 ∧ (p1 → ((p3 → (True → (p5 ∨ (p5 ∨ p4)))) ∨ p3)))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
  have h4 : (((p4 ∨ (False → (p2 → p2))) → p4) → (p3 → p4)) := by
    -- Implications on the right can always be decomposed.
    intro h5
    -- Implications on the right can always be decomposed.
    intro h6
    -- We want to use the implication h5 based on <expert-advice>. So we show its premise.
    have h7 : (p4 ∨ (False → (p2 → p2))) := by
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Implications on the right can always be decomposed.
      intro h8
      -- Implications on the right can always be decomposed.
      intro h9
      -- False on the left can always be used.
      apply False.elim h8
    -- We have shown the premise of h5, we can now drive its conclusion.
    let h10 := h5 h7
    -- One of the premise coincides with the conclusion.
    exact h10
  -- We have shown the premise of h2, we can now drive its conclusion.
  let h11 := h2 h4
  -- False on the left can always be used.
  apply False.elim h11
  -- Implications on the right can always be decomposed.
  intro h12
  -- Conjunctions on the left can always be decomposed.
  let h13 := h1.left
  let h14 := h1.right
  -- We want to use the implication h13 based on <expert-advice>. So we show its premise.
  have h15 : (((p4 ∨ (False → (p2 → p2))) → p4) → (p3 → p4)) := by
    -- Implications on the right can always be decomposed.
    intro h16
    -- Implications on the right can always be decomposed.
    intro h17
    -- We want to use the implication h16 based on <expert-advice>. So we show its premise.
    have h18 : (p4 ∨ (False → (p2 → p2))) := by
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Implications on the right can always be decomposed.
      intro h19
      -- Implications on the right can always be decomposed.
      intro h20
      -- False on the left can always be used.
      apply False.elim h19
    -- We have shown the premise of h16, we can now drive its conclusion.
    let h21 := h16 h18
    -- One of the premise coincides with the conclusion.
    exact h21
  -- We have shown the premise of h13, we can now drive its conclusion.
  let h22 := h13 h15
  -- False on the left can always be used.
  apply False.elim h22



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_150022810322953988350335693211 : ((p5 ∨ ((p5 ∨ ((p3 ∧ ((False ∧ p3) → p4)) ∧ False)) → (((False ∨ p1) ∧ p2) ∧ (p2 ∨ (p3 ∨ p5))))) ∨ ((p2 ∧ (False ∧ p1)) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_65171921197852270661203838718 : ((p3 ∨ (((True ∧ ((True ∧ ((((False ∨ p5) ∧ False) ∧ ((p4 ∨ p4) → p2)) ∨ p3)) ∧ (p3 ∨ True))) → (p5 ∨ (p5 ∧ p2))) ∧ p1)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_158343778972588571950923588715 : (((p3 ∧ p4) ∧ ((True ∧ (((p4 ∨ p2) ∧ (p2 → True)) ∧ True)) → (p2 ∧ ((p4 ∨ True) → True)))) ∨ (((True → (p2 ∧ p3)) ∨ p4) → True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_40638549823705586098412126900 : ((((((((p4 ∨ p1) ∨ False) → p4) ∧ ((p2 → p4) ∨ (True → (((p3 → p4) → p2) ∨ (p5 ∧ (p2 ∨ p3)))))) → p4) → p5) ∨ True) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_677383755255189355505360351921 : (((((((((p1 ∧ (((p4 → ((p2 ∨ p3) ∨ p5)) ∧ p1) ∨ p2)) ∧ False) ∨ p4) ∧ p5) ∨ p2) ∨ p1) ∨ (((p5 → True) ∧ False) → p1)) ∨ p4) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
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
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_1399369289657956259566592053 : (((((p3 ∧ p1) ∨ ((p2 → p3) ∧ p5)) ∨ p5) → ((((True ∧ (p5 ∧ ((p3 ∨ p3) → p3))) ∨ p5) → p1) ∨ p5)) ∧ (True ∧ True)) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h1
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h2 =>
    -- Disjunctions on the left can always be decomposed.
    cases h2
    case inl h3 =>
      -- Conjunctions on the left can always be decomposed.
      let h4 := h3.left
      let h5 := h3.right
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- Implications on the right can always be decomposed.
      intro h6
      -- Disjunctions on the left can always be decomposed.
      cases h6
      case inl h7 =>
        -- Conjunctions on the left can always be decomposed.
        let h8 := h7.left
        let h9 := h7.right
        -- Conjunctions on the left can always be decomposed.
        let h10 := h9.left
        let h11 := h9.right
        -- One of the premise coincides with the conclusion.
        exact h5
      case inr h12 =>
        -- One of the premise coincides with the conclusion.
        exact h5
    case inr h13 =>
      -- Conjunctions on the left can always be decomposed.
      let h14 := h13.left
      let h15 := h13.right
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- One of the premise coincides with the conclusion.
      exact h15
  case inr h16 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h16
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_246600366513331245981468854658 : ((p5 ∧ p2) ∨ (False ∨ ((p5 ∨ (((p1 ∨ False) ∨ p1) → ((((p1 ∨ p1) ∨ (True ∧ (p3 → p1))) ∨ (p5 ∧ (p4 → p3))) ∧ p5))) ∨ True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_117125415666448653854600291317 : (((p4 → p1) → ((True ∨ (p1 ∨ True)) → (p3 ∧ ((p5 ∧ (True → p1)) ∧ ((p5 ∧ p4) ∨ (p5 → ((p2 ∧ p4) ∧ p3))))))) ∨ (p4 → p4)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_38601410191547293833874353040 : (((((p4 ∨ (False ∨ ((p3 → False) ∨ p4))) ∨ False) ∧ (p2 → ((((p5 → False) ∧ p3) → (p5 → (p5 → (True ∨ p1)))) ∨ True))) ∧ True) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_191774783656871978161972400034 : ((p1 ∨ ((p4 ∧ (p1 ∨ p1)) ∨ (p5 ∧ (p1 ∨ p1)))) ∨ (((p1 ∨ p1) → (p5 → (p5 → (p4 → p3)))) ∨ (p2 → ((p2 ∧ p4) ∨ True)))) := by
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
theorem thm_5_vars_44336180388354472630526813432 : (((((((p2 ∨ p5) → (p5 ∨ (p2 → (p1 → p1)))) ∧ (False ∨ (p4 ∨ p2))) → p1) → (((True ∨ p1) ∨ False) ∧ (p3 ∧ p1))) → p3) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_325656408626574912686553893090 : (p5 ∨ (False ∨ (p1 ∨ ((p4 → (p5 ∨ p3)) → (p4 → ((False ∨ (p1 ∨ p5)) ∨ ((p1 ∨ (((p4 ∧ (p3 ∨ p5)) ∧ p4) ∨ p5)) → True))))))) := by
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
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h3
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_57973961682081637411554517203 : (((p3 → (p5 ∨ True)) → ((((False ∧ ((p1 ∧ p1) → False)) ∨ (((p3 ∧ (True ∨ True)) ∨ (p4 ∧ p2)) → p5)) → (p4 ∨ p3)) ∨ p3)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_116971920909291598205421560386 : (((p4 ∧ p2) → ((((((True ∨ p4) ∧ p4) ∧ (p4 ∧ p3)) → p5) → (p5 → (p5 ∧ (False ∧ ((p4 ∨ False) ∧ p2))))) ∨ p2)) ∨ (False → p2)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_234279473484568065302831226438 : ((False → (p2 → p2)) → ((p1 → (p5 ∧ ((p4 ∧ p1) → (p2 ∨ ((False ∨ p3) ∨ (((p4 ∨ (p5 ∧ p4)) → (False ∧ p3)) → p5)))))) ∨ True)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_256139985482898734171165172343 : ((True ∨ p5) → (True → (((True → (p3 ∨ (p1 → ((p3 ∧ p2) → (p5 ∧ p5))))) → False) ∨ (False → ((p2 ∧ p3) ∨ ((p2 ∧ p4) ∧ p3)))))) := by
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
    -- False on the left can always be used.
    apply False.elim h4
  case inr h5 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h6
    -- False on the left can always be used.
    apply False.elim h6



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_323217838323409875983345001392 : (p5 ∨ ((((((p5 → p3) ∨ (True ∧ False)) ∧ True) → (((p4 ∧ p1) ∧ True) ∧ p2)) ∨ ((p5 ∨ True) ∨ ((p4 ∧ p1) ∨ p3))) ∨ (p5 ∧ p3))) := by
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
theorem thm_5_vars_612976246735649765623226291804 : (((((p5 → ((True → (p5 → (((p5 ∧ (p3 ∨ (p1 ∧ (p3 ∨ p3)))) ∨ p2) ∨ ((True ∧ p2) ∧ p2)))) → False)) ∨ (p3 ∨ True)) ∨ False) ∨ p3) ∧ True) := by
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
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_165123189125203062036748092677 : ((((((((p1 → False) ∧ p5) ∨ False) ∨ ((p5 ∧ True) → p2)) ∨ False) ∧ p2) ∧ (p1 ∧ p4)) ∨ ((True ∨ ((p1 ∨ p1) ∧ p5)) → (p5 ∨ True))) := by
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
    -- Conjunctions on the left can always be decomposed.
    let h4 := h3.left
    let h5 := h3.right
    -- Disjunctions on the left can always be decomposed.
    cases h4
    case inl h6 =>
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- One of the premise coincides with the conclusion.
      exact h5
    case inr h7 =>
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- One of the premise coincides with the conclusion.
      exact h5



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_609676780311011802083806404587 : (((((p1 ∨ (((False → ((p4 ∧ (p5 → p1)) → (False → True))) → False) → ((True ∧ p2) → ((p1 ∨ p3) ∧ (p3 ∧ p5))))) ∨ p1) ∨ True) ∨ p3) ∧ True) := by
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
theorem thm_5_vars_48224985231239322301622137185 : (((True ∧ ((((((p4 → ((p5 → p3) → (p1 ∨ True))) ∨ p1) ∧ p3) → ((p4 ∨ p2) → p4)) ∨ p4) ∨ (True → p4))) → (p5 ∨ False)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_113532178691215653508043337798 : (((((p4 ∧ (True → False)) ∨ (p2 ∧ p2)) ∨ ((True ∨ (p4 → ((p4 ∧ ((p1 ∧ p4) ∨ p3)) → False))) → p3)) ∨ (p3 → True)) ∨ (p4 → False)) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_245009478422962874946754029287 : ((p1 ∧ p4) ∨ (((p1 → p3) ∨ p3) → (((True ∧ ((True → False) ∧ (p2 ∨ p3))) ∧ (p5 ∧ (((p3 ∧ p1) → (True ∨ p4)) ∧ True))) → False))) := by
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
  let h5 := h3.left
  let h6 := h3.right
  -- Conjunctions on the left can always be decomposed.
  let h7 := h6.left
  let h8 := h6.right
  -- Disjunctions on the left can always be decomposed.
  cases h8
  case inl h9 =>
    -- Conjunctions on the left can always be decomposed.
    let h10 := h4.left
    let h11 := h4.right
    -- Conjunctions on the left can always be decomposed.
    let h12 := h11.left
    let h13 := h11.right
    -- Disjunctions on the left can always be decomposed.
    cases h1
    case inl h14 =>
      -- We want to use the implication h7 based on <expert-advice>. So we show its premise.
      have h15 : True := by
        -- True on the right can always be proven directly.
        apply True.intro
      -- We have shown the premise of h7, we can now drive its conclusion.
      let h16 := h7 h15
      -- False on the left can always be used.
      apply False.elim h16
    case inr h17 =>
      -- We want to use the implication h7 based on <expert-advice>. So we show its premise.
      have h18 : True := by
        -- True on the right can always be proven directly.
        apply True.intro
      -- We have shown the premise of h7, we can now drive its conclusion.
      let h19 := h7 h18
      -- False on the left can always be used.
      apply False.elim h19
  case inr h20 =>
    -- Conjunctions on the left can always be decomposed.
    let h21 := h4.left
    let h22 := h4.right
    -- Conjunctions on the left can always be decomposed.
    let h23 := h22.left
    let h24 := h22.right
    -- Disjunctions on the left can always be decomposed.
    cases h1
    case inl h25 =>
      -- We want to use the implication h7 based on <expert-advice>. So we show its premise.
      have h26 : True := by
        -- True on the right can always be proven directly.
        apply True.intro
      -- We have shown the premise of h7, we can now drive its conclusion.
      let h27 := h7 h26
      -- False on the left can always be used.
      apply False.elim h27
    case inr h28 =>
      -- We want to use the implication h7 based on <expert-advice>. So we show its premise.
      have h29 : True := by
        -- True on the right can always be proven directly.
        apply True.intro
      -- We have shown the premise of h7, we can now drive its conclusion.
      let h30 := h7 h29
      -- False on the left can always be used.
      apply False.elim h30



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_148532059008715616694902433978 : ((((p5 ∧ p1) ∨ (p5 ∨ (((p1 → (p2 ∨ p1)) ∨ p3) → p1))) → ((p3 ∨ p2) ∧ ((p5 → p2) ∨ p1))) ∨ (True → ((p3 ∧ False) ∨ True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_251003183394418934302185006013 : ((p1 → p5) ∨ ((p4 → (((p5 ∧ (True ∧ p3)) ∨ (((p4 ∨ (p3 → True)) → (p4 → (True → False))) ∧ (p1 ∨ p3))) ∨ p4)) ∨ (p5 ∨ p4))) := by
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
theorem thm_5_vars_585979904789391346093114827922 : (((((((False ∨ ((((p2 ∨ p5) → (True → (True ∨ p3))) ∧ ((True → p1) → p1)) → True)) ∧ False) ∧ ((p3 ∨ p5) → False)) ∧ True) ∧ p5) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_37063519260619502071394374716 : ((((((p1 → False) ∨ (((((p3 ∧ p4) ∨ (p4 ∨ ((p3 ∨ (p4 ∧ False)) ∨ p3))) ∨ True) ∧ (p1 ∧ p5)) → p4)) ∧ False) ∧ p1) ∧ False) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_66437402604605819483279885890 : ((True → (((((True → p2) ∧ False) ∨ ((((p4 ∧ True) → (((False → False) ∧ p2) → ((p5 ∧ p5) ∧ p1))) ∨ p3) ∨ p3)) ∨ p3) ∧ p3)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_345328484750549181862205335485 : (p3 → (((((p1 → ((p1 → (((p1 ∧ True) → (False → True)) → (True ∧ p1))) ∨ p1)) → p3) → ((p1 → (False → p4)) ∧ p1)) ∧ p5) ∨ p3)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_313065395343528338815123545901 : (p3 ∨ (((False → (((p3 ∨ (p1 ∧ ((False → True) ∧ (p2 ∨ False)))) ∨ ((p1 ∧ p5) ∧ (False → p2))) ∨ ((p5 ∨ True) ∨ p4))) → p2) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_266062732674138330246898181877 : (True ∧ (p2 → ((p2 → ((((True → p3) ∨ p2) → ((((((p1 → p4) ∧ p1) ∧ p4) ∨ False) ∧ p5) ∨ p2)) ∨ ((True → p5) ∧ p1))) ∨ p3))) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h2
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h3
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
    exact h5



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_244164143346231372423931337800 : ((True ∧ p4) ∨ ((True → p4) → (((((p2 → (True → p1)) → True) → (((p1 ∨ p4) ∧ True) ∨ p5)) ∨ False) ∧ (p2 → ((True ∨ p4) ∧ p2))))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h2
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h3 : True := by
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h4 := h1 h3
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h4
  -- True on the right can always be proven directly.
  apply True.intro
  -- Implications on the right can always be decomposed.
  intro h5
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro
  -- One of the premise coincides with the conclusion.
  exact h5



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_329272288814978979010206836149 : (True → (((p2 ∨ p5) ∨ p5) ∨ ((((True ∨ p2) → False) ∧ ((p4 → (p5 ∧ (p4 ∨ (p2 ∧ p4)))) ∨ ((p4 ∧ True) ∧ p5))) ∨ (p4 ∨ True)))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_152224056125202492757430506086 : (((p1 ∧ (p4 ∨ (p5 ∨ (p4 ∧ p1)))) ∧ (((p2 → ((True → (p3 ∨ p4)) ∨ p5)) ∨ (p2 ∧ p4)) ∨ p4)) → ((p1 ∧ (p4 → False)) → p5)) := by
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
  let h7 := h5.left
  let h8 := h5.right
  -- Disjunctions on the left can always be decomposed.
  cases h8
  case inl h9 =>
    -- Disjunctions on the left can always be decomposed.
    cases h6
    case inl h10 =>
      -- Disjunctions on the left can always be decomposed.
      cases h10
      case inl h11 =>
        -- We want to use the implication h4 based on <expert-advice>. So we show its premise.
        have h12 : p4 := by
          -- One of the premise coincides with the conclusion.
          exact h9
        -- We have shown the premise of h4, we can now drive its conclusion.
        let h13 := h4 h12
        -- False on the left can always be used.
        apply False.elim h13
      case inr h14 =>
        -- Conjunctions on the left can always be decomposed.
        let h15 := h14.left
        let h16 := h14.right
        -- We want to use the implication h4 based on <expert-advice>. So we show its premise.
        have h17 : p4 := by
          -- One of the premise coincides with the conclusion.
          exact h16
        -- We have shown the premise of h4, we can now drive its conclusion.
        let h18 := h4 h17
        -- False on the left can always be used.
        apply False.elim h18
    case inr h19 =>
      -- We want to use the implication h4 based on <expert-advice>. So we show its premise.
      have h20 : p4 := by
        -- One of the premise coincides with the conclusion.
        exact h19
      -- We have shown the premise of h4, we can now drive its conclusion.
      let h21 := h4 h20
      -- False on the left can always be used.
      apply False.elim h21
  case inr h22 =>
    -- Disjunctions on the left can always be decomposed.
    cases h22
    case inl h23 =>
      -- Disjunctions on the left can always be decomposed.
      cases h6
      case inl h24 =>
        -- Disjunctions on the left can always be decomposed.
        cases h24
        case inl h25 =>
          -- One of the premise coincides with the conclusion.
          exact h23
        case inr h26 =>
          -- Conjunctions on the left can always be decomposed.
          let h27 := h26.left
          let h28 := h26.right
          -- One of the premise coincides with the conclusion.
          exact h23
      case inr h29 =>
        -- One of the premise coincides with the conclusion.
        exact h23
    case inr h30 =>
      -- Conjunctions on the left can always be decomposed.
      let h31 := h30.left
      let h32 := h30.right
      -- Disjunctions on the left can always be decomposed.
      cases h6
      case inl h33 =>
        -- Disjunctions on the left can always be decomposed.
        cases h33
        case inl h34 =>
          -- We want to use the implication h4 based on <expert-advice>. So we show its premise.
          have h35 : p4 := by
            -- One of the premise coincides with the conclusion.
            exact h31
          -- We have shown the premise of h4, we can now drive its conclusion.
          let h36 := h4 h35
          -- False on the left can always be used.
          apply False.elim h36
        case inr h37 =>
          -- Conjunctions on the left can always be decomposed.
          let h38 := h37.left
          let h39 := h37.right
          -- We want to use the implication h4 based on <expert-advice>. So we show its premise.
          have h40 : p4 := by
            -- One of the premise coincides with the conclusion.
            exact h39
          -- We have shown the premise of h4, we can now drive its conclusion.
          let h41 := h4 h40
          -- False on the left can always be used.
          apply False.elim h41
      case inr h42 =>
        -- We want to use the implication h4 based on <expert-advice>. So we show its premise.
        have h43 : p4 := by
          -- One of the premise coincides with the conclusion.
          exact h42
        -- We have shown the premise of h4, we can now drive its conclusion.
        let h44 := h4 h43
        -- False on the left can always be used.
        apply False.elim h44



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_42326490065684992213322901751 : (((p2 ∧ (p2 → (((False ∧ p1) ∧ p3) ∧ (((p4 ∨ (p5 ∧ ((p4 ∧ (p2 → (p5 ∧ p3))) ∧ False))) ∨ (False → p5)) ∨ p3)))) ∨ p4) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_173045649764267902427578389189 : ((False ∨ ((((((True ∨ (p1 → False)) ∧ p5) ∧ True) → False) → (p2 ∧ p1)) ∧ True)) ∨ ((((((p2 → p3) ∧ p5) ∨ p1) ∧ p5) ∧ True) → p5)) := by
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
  cases h4
  case inl h6 =>
    -- Conjunctions on the left can always be decomposed.
    let h7 := h6.left
    let h8 := h6.right
    -- One of the premise coincides with the conclusion.
    exact h5
  case inr h9 =>
    -- One of the premise coincides with the conclusion.
    exact h5



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_193231998167780548186391201388 : ((((p1 ∨ True) ∨ p5) ∧ ((p5 → True) → (p2 ∧ False))) → ((p3 ∧ p4) ∧ (((True ∧ (p2 ∧ p4)) ∨ (p4 ∧ (p2 → p2))) → (True ∨ p3)))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- Disjunctions on the left can always be decomposed.
  cases h2
  case inl h4 =>
    -- Disjunctions on the left can always be decomposed.
    cases h4
    case inl h5 =>
      -- We want to use the implication h3 based on <expert-advice>. So we show its premise.
      have h6 : (p5 → True) := by
        -- Implications on the right can always be decomposed.
        intro h7
        -- True on the right can always be proven directly.
        apply True.intro
      -- We have shown the premise of h3, we can now drive its conclusion.
      let h8 := h3 h6
      -- We need to get the right conjuct of h8 based on <expert-advice>.
      let h9 := h8.right
      -- False on the left can always be used.
      apply False.elim h9
    case inr h10 =>
      -- We want to use the implication h3 based on <expert-advice>. So we show its premise.
      have h11 : (p5 → True) := by
        -- Implications on the right can always be decomposed.
        intro h12
        -- True on the right can always be proven directly.
        apply True.intro
      -- We have shown the premise of h3, we can now drive its conclusion.
      let h13 := h3 h11
      -- We need to get the right conjuct of h13 based on <expert-advice>.
      let h14 := h13.right
      -- False on the left can always be used.
      apply False.elim h14
  case inr h15 =>
    -- We want to use the implication h3 based on <expert-advice>. So we show its premise.
    have h16 : (p5 → True) := by
      -- Implications on the right can always be decomposed.
      intro h17
      -- True on the right can always be proven directly.
      apply True.intro
    -- We have shown the premise of h3, we can now drive its conclusion.
    let h18 := h3 h16
    -- We need to get the right conjuct of h18 based on <expert-advice>.
    let h19 := h18.right
    -- False on the left can always be used.
    apply False.elim h19
  -- Conjunctions on the left can always be decomposed.
  let h20 := h1.left
  let h21 := h1.right
  -- Disjunctions on the left can always be decomposed.
  cases h20
  case inl h22 =>
    -- Disjunctions on the left can always be decomposed.
    cases h22
    case inl h23 =>
      -- We want to use the implication h21 based on <expert-advice>. So we show its premise.
      have h24 : (p5 → True) := by
        -- Implications on the right can always be decomposed.
        intro h25
        -- True on the right can always be proven directly.
        apply True.intro
      -- We have shown the premise of h21, we can now drive its conclusion.
      let h26 := h21 h24
      -- We need to get the right conjuct of h26 based on <expert-advice>.
      let h27 := h26.right
      -- False on the left can always be used.
      apply False.elim h27
    case inr h28 =>
      -- We want to use the implication h21 based on <expert-advice>. So we show its premise.
      have h29 : (p5 → True) := by
        -- Implications on the right can always be decomposed.
        intro h30
        -- True on the right can always be proven directly.
        apply True.intro
      -- We have shown the premise of h21, we can now drive its conclusion.
      let h31 := h21 h29
      -- We need to get the right conjuct of h31 based on <expert-advice>.
      let h32 := h31.right
      -- False on the left can always be used.
      apply False.elim h32
  case inr h33 =>
    -- We want to use the implication h21 based on <expert-advice>. So we show its premise.
    have h34 : (p5 → True) := by
      -- Implications on the right can always be decomposed.
      intro h35
      -- True on the right can always be proven directly.
      apply True.intro
    -- We have shown the premise of h21, we can now drive its conclusion.
    let h36 := h21 h34
    -- We need to get the right conjuct of h36 based on <expert-advice>.
    let h37 := h36.right
    -- False on the left can always be used.
    apply False.elim h37
  -- Implications on the right can always be decomposed.
  intro h38
  -- Disjunctions on the left can always be decomposed.
  cases h38
  case inl h39 =>
    -- Conjunctions on the left can always be decomposed.
    let h40 := h39.left
    let h41 := h39.right
    -- Conjunctions on the left can always be decomposed.
    let h42 := h41.left
    let h43 := h41.right
    -- Conjunctions on the left can always be decomposed.
    let h44 := h1.left
    let h45 := h1.right
    -- Disjunctions on the left can always be decomposed.
    cases h44
    case inl h46 =>
      -- Disjunctions on the left can always be decomposed.
      cases h46
      case inl h47 =>
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- True on the right can always be proven directly.
        apply True.intro
      case inr h48 =>
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- True on the right can always be proven directly.
        apply True.intro
    case inr h49 =>
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- True on the right can always be proven directly.
      apply True.intro
  case inr h50 =>
    -- Conjunctions on the left can always be decomposed.
    let h51 := h50.left
    let h52 := h50.right
    -- Conjunctions on the left can always be decomposed.
    let h53 := h1.left
    let h54 := h1.right
    -- Disjunctions on the left can always be decomposed.
    cases h53
    case inl h55 =>
      -- Disjunctions on the left can always be decomposed.
      cases h55
      case inl h56 =>
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- True on the right can always be proven directly.
        apply True.intro
      case inr h57 =>
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- True on the right can always be proven directly.
        apply True.intro
    case inr h58 =>
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- True on the right can always be proven directly.
      apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_65134199839298108439828915644 : ((p2 ∨ (p2 → ((p5 → (((p1 → ((((p2 ∧ (p5 ∨ (p2 ∨ False))) ∨ ((True ∨ p1) → p1)) ∨ p5) → False)) ∧ True) ∧ False)) ∧ True))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_206067574877074078285221957040 : ((p3 ∧ (((p4 ∨ p3) ∧ p4) → p3)) ∨ ((((p4 ∧ ((p5 ∨ p2) ∧ (p3 ∧ p5))) ∨ p2) ∧ p5) → (p5 ∧ ((p5 ∧ (p1 ∨ p5)) ∨ p5)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- Disjunctions on the left can always be decomposed.
  cases h2
  case inl h4 =>
    -- Conjunctions on the left can always be decomposed.
    let h5 := h4.left
    let h6 := h4.right
    -- Conjunctions on the left can always be decomposed.
    let h7 := h6.left
    let h8 := h6.right
    -- Disjunctions on the left can always be decomposed.
    cases h7
    case inl h9 =>
      -- Conjunctions on the left can always be decomposed.
      let h10 := h8.left
      let h11 := h8.right
      -- One of the premise coincides with the conclusion.
      exact h3
    case inr h12 =>
      -- Conjunctions on the left can always be decomposed.
      let h13 := h8.left
      let h14 := h8.right
      -- One of the premise coincides with the conclusion.
      exact h3
  case inr h15 =>
    -- One of the premise coincides with the conclusion.
    exact h3
  -- Conjunctions on the left can always be decomposed.
  let h16 := h1.left
  let h17 := h1.right
  -- Disjunctions on the left can always be decomposed.
  cases h16
  case inl h18 =>
    -- Conjunctions on the left can always be decomposed.
    let h19 := h18.left
    let h20 := h18.right
    -- Conjunctions on the left can always be decomposed.
    let h21 := h20.left
    let h22 := h20.right
    -- Disjunctions on the left can always be decomposed.
    cases h21
    case inl h23 =>
      -- Conjunctions on the left can always be decomposed.
      let h24 := h22.left
      let h25 := h22.right
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- One of the premise coincides with the conclusion.
      exact h17
    case inr h26 =>
      -- Conjunctions on the left can always be decomposed.
      let h27 := h22.left
      let h28 := h22.right
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- One of the premise coincides with the conclusion.
      exact h17
  case inr h29 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h17



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_340851077557446247019356825270 : (p2 → (((False ∨ ((p5 ∨ (((True ∧ p2) ∨ p4) ∨ (((p2 ∨ p5) ∨ p2) ∧ (p2 ∨ p4)))) → (p4 ∧ True))) ∨ (True ∨ (p1 ∧ False))) ∨ True)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_135215168095786856650198709152 : (((((p3 → (p2 ∧ ((False ∧ p5) → (p2 ∧ (p2 ∨ True))))) ∨ False) ∧ (True → ((p5 ∨ p3) ∧ p5))) → (False ∨ p1)) ∨ (True ∨ (p4 ∨ p5))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_748272876748684099910558013455 : ((((p2 → False) → (((p1 ∨ (((p5 ∨ False) ∧ ((p4 ∧ True) ∧ p4)) ∧ (((p5 ∨ False) ∨ (p5 ∨ True)) ∧ p5))) ∨ p5) ∨ (p2 → p1))) ∨ p5) ∧ True) := by
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
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h3 : p2 := by
    -- One of the premise coincides with the conclusion.
    exact h2
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h4 := h1 h3
  -- False on the left can always be used.
  apply False.elim h4
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_710758413090175422640855563649 : (((((p1 ∧ (p3 ∧ False)) → (False → p1)) ∧ ((p1 ∨ False) → ((p4 ∧ ((p5 ∨ (p3 ∨ p5)) ∧ p1)) ∨ ((p5 ∧ (False → p1)) ∨ True)))) ∨ p3) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- False on the left can always be used.
  apply False.elim h2
  -- Implications on the right can always be decomposed.
  intro h3
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
    -- False on the left can always be used.
    apply False.elim h5
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_62641463513393427194230337919 : ((p4 ∧ ((True → ((p3 ∨ (((((True ∨ p4) ∨ p2) ∨ True) ∨ False) ∨ (True ∧ p5))) → ((p5 ∧ p4) ∧ ((p4 ∨ p3) → True)))) ∧ False)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_3918856142262726358904442851 : (False ∨ ((((p1 ∧ p2) → (p3 ∧ (False ∨ ((True ∧ True) → (p5 → p3))))) ∧ ((False ∨ p2) ∧ (p5 → p4))) → ((True ∧ p3) ∨ p2))) := by
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
  -- Disjunctions on the left can always be decomposed.
  cases h4
  case inl h6 =>
    -- False on the left can always be used.
    apply False.elim h6
  case inr h7 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h7



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_217387683254289163976203787356 : (((p5 ∨ (p5 → p1)) ∨ p5) → (((p3 ∨ ((p3 ∨ ((False ∨ p4) ∨ (False ∨ False))) → ((p5 ∨ ((p3 → p2) → p4)) → False))) → p2) ∨ True)) := by
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
      -- True on the right can always be proven directly.
      apply True.intro
    case inr h4 =>
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
theorem thm_5_vars_754202562280444451277288012324 : (((False ∧ ((True ∨ (p3 ∧ p3)) → (((p1 ∨ False) ∨ (p5 → p3)) ∨ ((p2 ∨ p5) ∧ (((True → p5) ∨ p2) ∧ (p4 → (p3 → p1))))))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_184512613707021696443758695032 : (((p2 ∧ ((p5 ∨ (p2 → (False → True))) ∧ p1)) ∨ (p3 ∧ p1)) ∨ ((False ∧ ((((True → False) → ((True → p1) ∧ p1)) ∧ p3) ∧ True)) → True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_161229769928039554833562550793 : (((False ∧ False) → (p5 ∨ (((((False ∧ (p2 ∧ p3)) ∨ True) ∧ False) ∨ p2) ∧ (p3 → (p4 ∨ p1))))) → ((p2 → (p1 ∨ (p4 ∧ p5))) ∨ True)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_745530406797710329114952727801 : ((((True ∨ False) → ((p4 ∨ (False ∧ p5)) → (((p2 → p5) → ((p5 ∨ p1) ∧ ((((p1 ∧ False) → False) ∧ p5) → p1))) ∨ (p3 ∨ True)))) ∨ p5) ∧ True) := by
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
    -- Disjunctions on the left can always be decomposed.
    cases h1
    case inl h4 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- True on the right can always be proven directly.
      apply True.intro
    case inr h5 =>
      -- False on the left can always be used.
      apply False.elim h5
  case inr h6 =>
    -- Conjunctions on the left can always be decomposed.
    let h7 := h6.left
    let h8 := h6.right
    -- False on the left can always be used.
    apply False.elim h7
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_135966374993923249039161188809 : (((True → ((p5 ∧ ((p2 ∧ (p4 ∨ p5)) ∨ p4)) ∨ p1)) ∧ ((True ∨ (((p4 ∧ False) ∨ False) ∧ (False → False))) ∧ p1)) ∨ (p5 → (p5 ∧ True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- One of the premise coincides with the conclusion.
  exact h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_46562267576839680100322190079 : ((((False → False) → ((p4 ∨ ((p2 ∧ (((p4 ∨ True) ∧ (False ∧ p2)) ∨ (((p5 ∧ True) ∨ p4) ∨ p2))) ∨ p3)) ∧ True)) ∧ (True ∨ p1)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_124709346345870024967502767637 : (((((p2 → p2) → p5) ∧ p3) ∧ (p5 → (((p1 ∧ ((p4 ∨ p2) ∨ p1)) ∧ ((p5 ∧ False) ∧ ((p5 ∧ p2) → p2))) ∧ p5))) → (p2 ∧ p3)) := by
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
  -- We want to use the implication h3 based on <expert-advice>. So we show its premise.
  have h6 : p5 := by
    -- We want to use the implication h4 based on <expert-advice>. So we show its premise.
    have h7 : (p2 → p2) := by
      -- Implications on the right can always be decomposed.
      intro h8
      -- One of the premise coincides with the conclusion.
      exact h8
    -- We have shown the premise of h4, we can now drive its conclusion.
    let h9 := h4 h7
    -- One of the premise coincides with the conclusion.
    exact h9
  -- We have shown the premise of h3, we can now drive its conclusion.
  let h10 := h3 h6
  -- We need to get the left conjuct of h10 based on <expert-advice>.
  let h11 := h10.left
  -- We need to get the right conjuct of h11 based on <expert-advice>.
  let h12 := h11.right
  -- We need to get the left conjuct of h12 based on <expert-advice>.
  let h13 := h12.left
  -- We need to get the right conjuct of h13 based on <expert-advice>.
  let h14 := h13.right
  -- False on the left can always be used.
  apply False.elim h14
  -- Conjunctions on the left can always be decomposed.
  let h15 := h1.left
  let h16 := h1.right
  -- Conjunctions on the left can always be decomposed.
  let h17 := h15.left
  let h18 := h15.right
  -- One of the premise coincides with the conclusion.
  exact h18



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_199292530981768882275778234550 : ((((((p1 ∧ p5) ∧ p3) ∧ False) ∨ p1) ∨ p2) → (((p1 ∧ ((p3 → ((p4 ∨ p3) ∧ p2)) ∧ (False ∨ (False ∧ (p4 → p4))))) ∨ p3) ∨ True)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h2 =>
    -- Disjunctions on the left can always be decomposed.
    cases h2
    case inl h3 =>
      -- Conjunctions on the left can always be decomposed.
      let h4 := h3.left
      let h5 := h3.right
      -- Conjunctions on the left can always be decomposed.
      let h6 := h4.left
      let h7 := h4.right
      -- Conjunctions on the left can always be decomposed.
      let h8 := h6.left
      let h9 := h6.right
      -- False on the left can always be used.
      apply False.elim h5
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



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_263134615501925507834934955697 : (True ∧ ((((p2 ∧ True) ∧ (p5 → p5)) → (p1 ∨ (((p3 → False) ∨ p3) ∨ (True ∧ (p5 ∨ ((p5 ∧ p4) ∨ (p4 ∧ p3))))))) ∨ (p5 ∨ True))) := by
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
theorem thm_5_vars_624758138862397943653843063072 : ((((p5 ∨ (((p1 → True) ∧ (((p3 ∨ p4) → True) → ((p1 → (p3 → (p2 → (False ∧ (True → (p2 ∧ p4)))))) ∧ p3))) ∧ p4)) ∨ True) ∨ False) ∧ True) := by
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



