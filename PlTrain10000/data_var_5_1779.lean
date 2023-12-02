variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_327086769752096118945526305871 : (True → (((p3 → (p4 ∨ p2)) ∨ ((p4 ∧ ((p5 ∧ (p5 ∧ p3)) → (((p4 ∧ (True ∨ (p5 → False))) → p3) → (p2 → p4)))) ∨ True)) ∨ p1)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_63311592301998313266951325760 : ((p5 ∧ ((p5 ∨ p1) ∧ ((((p2 ∧ p5) → (((p4 ∧ p3) → (True ∧ p1)) → ((p2 ∨ (p3 → p5)) ∨ p1))) → p1) → (p5 → p4)))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_56755009808187230044775602956 : ((((p3 → True) ∨ p1) ∧ (p5 → (p1 → ((((p2 ∧ p5) ∧ p1) ∨ p4) ∨ ((((True → False) ∧ False) ∧ p5) ∨ ((p2 ∧ p3) ∨ p5)))))) ∨ False) := by
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
  -- One of the premise coincides with the conclusion.
  exact h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_168221866983210844305809183216 : (((True → (p1 → p1)) ∨ (((p3 ∧ p1) ∨ (p5 → (p2 ∨ ((False ∧ p5) ∨ p3)))) ∧ p3)) → ((False ∧ p4) ∨ ((False → (p4 ∨ True)) ∨ p3))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h2 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Implications on the right can always be decomposed.
    intro h3
    -- False on the left can always be used.
    apply False.elim h3
  case inr h4 =>
    -- Conjunctions on the left can always be decomposed.
    let h5 := h4.left
    let h6 := h4.right
    -- Disjunctions on the left can always be decomposed.
    cases h5
    case inl h7 =>
      -- Conjunctions on the left can always be decomposed.
      let h8 := h7.left
      let h9 := h7.right
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- One of the premise coincides with the conclusion.
      exact h6
    case inr h10 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- One of the premise coincides with the conclusion.
      exact h6



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_190427165984345414217357670972 : (((p3 ∨ (p5 ∨ (p2 ∧ ((p3 ∨ p2) ∨ p4)))) ∨ True) ∨ ((True → ((p3 ∨ (p5 ∧ p2)) → (p5 ∧ (True ∧ ((True ∨ p4) ∧ True))))) ∨ p5)) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_803989099959967248799382171583 : (((p3 → ((((((p1 ∨ ((False ∨ p2) → p1)) → (p1 ∧ (p5 → (p5 ∨ (True ∨ True))))) ∨ p1) ∨ False) ∧ p1) ∨ (False ∨ (p5 ∧ p4)))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_52181041739639785952034772584 : (((((p5 ∧ (True → p2)) ∨ p2) ∧ (((p1 ∧ ((p4 ∨ p1) → p1)) → p5) ∧ p1)) → (False ∧ (p4 ∧ (((True ∧ True) ∨ p3) ∨ False)))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_134723344256666393192428614367 : (((((False ∧ p4) ∧ p2) → (((True → (p4 → (p1 ∧ (((p5 → p5) ∨ p3) ∧ (p2 → False))))) ∨ p2) ∨ p3)) → p3) ∨ ((p1 ∧ p3) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_136389656592506341649560860666 : (((False ∧ ((p3 ∧ p1) ∨ False)) ∨ (((p5 ∨ p3) ∨ (p2 ∧ ((p5 ∧ p3) ∨ (False ∧ p1)))) ∨ (p5 ∧ (True → p4)))) ∨ (p5 ∨ (p5 → True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_216606477015433270097693709400 : ((((p3 → False) ∧ p5) ∧ p1) → (((p3 → (p2 ∧ (p4 → False))) ∧ ((p2 ∧ p4) ∨ (((p1 ∨ ((p2 ∧ p3) ∨ p4)) → p3) ∨ p1))) ∨ p2)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- Conjunctions on the left can always be decomposed.
  let h4 := h2.left
  let h5 := h2.right
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h6
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- We want to use the implication h4 based on <expert-advice>. So we show its premise.
  have h7 : p3 := by
    -- One of the premise coincides with the conclusion.
    exact h6
  -- We have shown the premise of h4, we can now drive its conclusion.
  let h8 := h4 h7
  -- False on the left can always be used.
  apply False.elim h8
  -- Implications on the right can always be decomposed.
  intro h9
  -- We want to use the implication h4 based on <expert-advice>. So we show its premise.
  have h10 : p3 := by
    -- One of the premise coincides with the conclusion.
    exact h6
  -- We have shown the premise of h4, we can now drive its conclusion.
  let h11 := h4 h10
  -- False on the left can always be used.
  apply False.elim h11
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h3



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_261030913044287123131613106788 : ((p4 → p2) → ((((p3 → (((True → p5) ∧ (p3 → ((p5 → p2) → p1))) ∨ True)) ∨ True) → False) → (((p5 → p1) ∨ (True → True)) ∧ p4))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h3
  -- True on the right can always be proven directly.
  apply True.intro
  -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
  have h4 : ((p3 → (((True → p5) ∧ (p3 → ((p5 → p2) → p1))) ∨ True)) ∨ True) := by
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h2, we can now drive its conclusion.
  let h5 := h2 h4
  -- False on the left can always be used.
  apply False.elim h5



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_786835148569035133616253846480 : (((p4 ∨ (((p2 ∧ p3) → p2) ∧ (p1 → ((((p5 ∨ (p2 ∨ ((p2 → p4) ∨ ((p1 → False) → False)))) → (p4 → False)) ∧ p2) → p5)))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_346772740832305302745374064704 : (p3 → ((((p4 ∧ (p1 ∧ p5)) ∨ (True ∧ (False ∨ ((p1 ∧ p2) → (((p3 ∧ p5) ∨ False) ∧ p2))))) → False) ∨ (False → ((p1 ∨ p4) ∧ True)))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h2
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- False on the left can always be used.
  apply False.elim h2
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_322431354890240418132462061570 : (p5 ∨ ((((p3 ∧ (False ∨ (p3 ∨ p2))) ∧ p1) ∨ ((p2 ∧ (((p4 ∧ (p2 → ((p3 ∧ False) → False))) ∨ (p4 ∧ True)) ∨ p3)) ∨ True)) ∨ p2)) := by
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
theorem thm_5_vars_47333718745311674006568057618 : ((((p3 ∧ True) ∧ ((p1 ∨ (((p3 → (p5 ∨ (p2 ∨ (p2 ∨ False)))) ∧ ((p5 → p5) ∨ p3)) → (True ∧ p1))) → p2)) ∨ (p2 ∧ p4)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_225338302635921249729378956404 : (((p1 ∨ p1) ∧ p1) ∨ ((False ∧ False) ∨ (p1 → ((p1 → (((True ∨ p4) → False) ∨ (((p4 ∧ (p4 ∧ False)) ∧ (p4 → p1)) ∧ p3))) → p4)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
  have h3 : p1 := by
    -- One of the premise coincides with the conclusion.
    exact h1
  -- We have shown the premise of h2, we can now drive its conclusion.
  let h4 := h2 h3
  -- Disjunctions on the left can always be decomposed.
  cases h4
  case inl h5 =>
    -- We want to use the implication h5 based on <expert-advice>. So we show its premise.
    have h6 : (True ∨ p4) := by
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- True on the right can always be proven directly.
      apply True.intro
    -- We have shown the premise of h5, we can now drive its conclusion.
    let h7 := h5 h6
    -- False on the left can always be used.
    apply False.elim h7
  case inr h8 =>
    -- Conjunctions on the left can always be decomposed.
    let h9 := h8.left
    let h10 := h8.right
    -- Conjunctions on the left can always be decomposed.
    let h11 := h9.left
    let h12 := h9.right
    -- Conjunctions on the left can always be decomposed.
    let h13 := h11.left
    let h14 := h11.right
    -- Conjunctions on the left can always be decomposed.
    let h15 := h14.left
    let h16 := h14.right
    -- False on the left can always be used.
    apply False.elim h16



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_225958325562657099270504824003 : (((p3 ∧ True) ∨ p3) ∨ ((False → (((p2 ∨ (p5 ∧ p1)) ∨ (p3 → p2)) → p5)) → (p4 ∨ ((((p1 ∨ p2) → True) ∧ p4) ∨ (p5 ∨ True))))) := by
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
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_309777077878927841536058704676 : (p2 ∨ (((((p2 ∧ p1) → (p4 ∨ (((p5 ∧ (((True ∧ p1) → p2) → p3)) ∨ p5) ∧ False))) ∧ p3) ∧ p3) ∨ (False → ((p4 → p3) ∨ p4)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_113189380289314486060322260203 : (((((p2 → (p2 ∧ p3)) → ((p5 ∧ (p3 ∨ p4)) ∧ (p5 → (p1 → (p3 ∨ ((p3 ∧ False) ∧ False)))))) ∧ p2) ∧ (p1 ∧ p4)) ∨ (False → p4)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_668844119888389991184387237230 : (((((((True ∨ (p3 ∧ (p3 ∧ p3))) ∨ p2) → ((p5 ∨ (((p3 → True) ∧ False) ∧ (p2 ∨ p3))) ∨ True)) ∨ False) ∨ (p5 ∨ (p2 → p4))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_53245193043431965924720861213 : ((((True → (p2 ∧ False)) → (p4 ∨ ((False ∨ p5) ∧ (True → p1)))) ∨ ((((p3 ∨ False) → True) ∧ (False ∧ True)) ∨ (p1 ∧ (p2 ∨ False)))) ∨ p3) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
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
theorem thm_5_vars_114807608592017293599888735118 : ((((p1 ∨ (p1 ∨ p5)) ∧ (((((p2 ∧ p5) → False) ∧ p3) → p2) → p1)) ∧ (((False ∧ p5) ∧ p1) ∧ ((False → p5) ∨ False))) ∨ (p1 → p1)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_215907359852649783338236867328 : ((p3 ∨ ((p5 ∨ p4) → p3)) ∨ (((((((p2 ∨ (p4 → p5)) ∧ p3) ∨ p3) ∧ p3) → (p1 ∧ p4)) ∧ (True → p2)) ∨ (False → (p3 ∧ p5)))) := by
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
theorem thm_5_vars_136336165285391901998748627432 : (((False ∧ (p4 ∨ (p2 ∧ p1))) ∧ ((((True ∨ False) → (((p3 → ((True ∨ True) ∧ p1)) ∧ p5) → False)) ∧ True) ∧ p3)) ∨ ((p5 → p2) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_9189345227634730157450495324 : ((((p3 → ((((p1 ∨ (p1 ∨ p3)) ∨ p2) ∧ p1) → False)) ∨ (((True → (p5 → (p1 ∨ False))) ∨ p4) ∧ ((p4 → p3) ∧ p4))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_60815844572645410729251897749 : ((True ∧ (p4 ∧ ((((p3 → (p5 ∨ (p1 ∨ ((((p3 ∧ p2) ∨ p5) ∨ (p2 → p1)) → p3)))) → False) ∧ (p1 → (p5 → p2))) ∨ p1))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_986116244482515716262390437873 : (((p2 ∧ ((((((p2 ∧ (False ∨ p3)) ∨ p4) ∨ (False ∨ p1)) ∧ (p4 → (p5 ∨ p4))) ∨ p2) → (((True ∧ p5) ∨ False) ∧ (p2 → False)))) → p3) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- We want to use the implication h3 based on <expert-advice>. So we show its premise.
  have h4 : (((((p2 ∧ (False ∨ p3)) ∨ p4) ∨ (False ∨ p1)) ∧ (p4 → (p5 ∨ p4))) ∨ p2) := by
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h2
  -- We have shown the premise of h3, we can now drive its conclusion.
  let h5 := h3 h4
  -- We need to get the right conjuct of h5 based on <expert-advice>.
  let h6 := h5.right
  -- We want to use the implication h6 based on <expert-advice>. So we show its premise.
  have h7 : p2 := by
    -- One of the premise coincides with the conclusion.
    exact h2
  -- We have shown the premise of h6, we can now drive its conclusion.
  let h8 := h6 h7
  -- False on the left can always be used.
  apply False.elim h8
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_312978033865859293172906826966 : (p3 ∨ ((((p1 ∨ p3) → (((p4 ∧ (((p3 ∨ ((p1 ∧ False) → p1)) ∨ ((p1 ∨ p4) → p2)) → p2)) ∨ p1) ∨ (p3 → p5))) ∧ p4) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_936576765342551060089276816902 : (((((False ∨ ((p1 ∨ False) → p5)) ∧ p1) ∧ (True → ((False ∨ (((p4 → False) → (True → ((False ∨ p3) → True))) ∨ p4)) ∨ (p3 ∧ False)))) → p5) ∧ True) := by
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
  -- Disjunctions on the left can always be decomposed.
  cases h4
  case inl h6 =>
    -- False on the left can always be used.
    apply False.elim h6
  case inr h7 =>
    -- We want to use the implication h7 based on <expert-advice>. So we show its premise.
    have h8 : (p1 ∨ False) := by
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- One of the premise coincides with the conclusion.
      exact h5
    -- We have shown the premise of h7, we can now drive its conclusion.
    let h9 := h7 h8
    -- One of the premise coincides with the conclusion.
    exact h9
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_783444475754140615130244045615 : (((p3 ∨ ((((((p2 ∧ p5) ∧ ((p1 ∧ p1) → p2)) ∨ p1) ∨ True) ∨ (False ∧ p2)) ∨ ((((False ∧ (p2 ∧ False)) → False) → p2) → p3))) ∨ p1) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
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
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_239623044534505303272772482692 : ((p3 ∨ True) ∧ (p1 → ((((True ∧ p4) → p3) ∨ (((((False ∧ p3) → p2) ∧ (p3 ∧ True)) ∧ (p1 ∧ True)) → p4)) ∨ ((p2 ∨ True) ∨ p2)))) := by
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
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_597848116011767018024796916320 : ((((((False ∧ p3) ∨ p4) ∧ (((p1 ∨ (p4 → (False ∨ (((p5 ∨ p2) ∧ p1) ∨ p2)))) → False) ∧ (p2 → (p4 → (p4 → p2))))) ∧ p3) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_66736224500385981230224455669 : ((True → ((p1 → p3) → ((((((((False ∨ p2) → p1) ∨ p5) ∧ (True ∧ p5)) ∧ p1) ∧ (True ∧ False)) ∨ True) ∨ ((p1 → p3) ∧ True)))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_345671906242240098782942181059 : (p3 → ((p1 ∨ ((p3 ∧ (((p5 → p2) → ((p2 → p4) ∧ p4)) ∨ (p2 ∨ True))) ∨ ((False ∧ (p2 ∧ (p1 ∨ (False ∧ True)))) ∨ p2))) ∨ p5)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- One of the premise coincides with the conclusion.
  exact h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_166522134878434077862178288756 : ((p4 ∨ (((True ∧ p3) ∨ p1) ∨ ((p3 ∨ (p1 ∧ (False ∨ p1))) → (False ∧ (True ∨ True))))) ∨ (p4 → (p4 ∨ ((p5 → p4) ∨ (p3 ∨ p1))))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_664695212008315146151876530413 : ((((False → ((p1 → (p2 ∧ (p3 → ((p5 ∧ False) ∧ ((p3 ∧ (p5 → (p5 → p4))) → (p2 ∧ True)))))) ∧ (p2 ∨ True))) → (p4 → p4)) ∨ False) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- One of the premise coincides with the conclusion.
  exact h2
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_238751874798255168673752752514 : ((p1 ∨ True) ∧ (((p3 ∨ (p5 ∨ False)) → p3) → (((p5 → False) ∧ (p3 ∧ (p3 → ((True ∧ p1) ∧ p5)))) → (p4 ∧ ((p5 ∨ p1) ∧ p1))))) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
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
  let h5 := h4.left
  let h6 := h4.right
  -- We want to use the implication h6 based on <expert-advice>. So we show its premise.
  have h7 : p3 := by
    -- One of the premise coincides with the conclusion.
    exact h5
  -- We have shown the premise of h6, we can now drive its conclusion.
  let h8 := h6 h7
  -- We need to get the right conjuct of h8 based on <expert-advice>.
  let h9 := h8.right
  -- We want to use the implication h3 based on <expert-advice>. So we show its premise.
  have h10 : p5 := by
    -- One of the premise coincides with the conclusion.
    exact h9
  -- We have shown the premise of h3, we can now drive its conclusion.
  let h11 := h3 h10
  -- False on the left can always be used.
  apply False.elim h11
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Conjunctions on the left can always be decomposed.
  let h12 := h2.left
  let h13 := h2.right
  -- Conjunctions on the left can always be decomposed.
  let h14 := h13.left
  let h15 := h13.right
  -- We want to use the implication h15 based on <expert-advice>. So we show its premise.
  have h16 : p3 := by
    -- One of the premise coincides with the conclusion.
    exact h14
  -- We have shown the premise of h15, we can now drive its conclusion.
  let h17 := h15 h16
  -- We need to get the right conjuct of h17 based on <expert-advice>.
  let h18 := h17.right
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- One of the premise coincides with the conclusion.
  exact h18
  -- Conjunctions on the left can always be decomposed.
  let h19 := h2.left
  let h20 := h2.right
  -- Conjunctions on the left can always be decomposed.
  let h21 := h20.left
  let h22 := h20.right
  -- We want to use the implication h22 based on <expert-advice>. So we show its premise.
  have h23 : p3 := by
    -- One of the premise coincides with the conclusion.
    exact h21
  -- We have shown the premise of h22, we can now drive its conclusion.
  let h24 := h22 h23
  -- We need to get the left conjuct of h24 based on <expert-advice>.
  let h25 := h24.left
  -- We need to get the right conjuct of h25 based on <expert-advice>.
  let h26 := h25.right
  -- One of the premise coincides with the conclusion.
  exact h26



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_119935539743505209692119084660 : (((((((p3 → p4) → p5) ∨ ((True ∨ (False → p5)) ∨ ((p3 ∨ (p2 → True)) → p3))) → p4) ∨ ((p5 ∨ False) ∨ p5)) ∧ p4) → (p5 → p5)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Conjunctions on the left can always be decomposed.
  let h3 := h1.left
  let h4 := h1.right
  -- Disjunctions on the left can always be decomposed.
  cases h3
  case inl h5 =>
    -- One of the premise coincides with the conclusion.
    exact h2
  case inr h6 =>
    -- Disjunctions on the left can always be decomposed.
    cases h6
    case inl h7 =>
      -- Disjunctions on the left can always be decomposed.
      cases h7
      case inl h8 =>
        -- One of the premise coincides with the conclusion.
        exact h8
      case inr h9 =>
        -- False on the left can always be used.
        apply False.elim h9
    case inr h10 =>
      -- One of the premise coincides with the conclusion.
      exact h10



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_558934170056525328343617924893 : (((p4 ∨ ((((p4 → (p4 ∨ p2)) ∧ p1) ∧ (p1 ∧ (p2 ∨ (((p5 → (False ∨ (p4 ∧ p4))) ∧ p1) ∧ (p5 ∧ (True ∧ False)))))) ∨ True)) ∧ True) ∧ True) := by
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
theorem thm_5_vars_51424957445748163249842990941 : ((((((p3 ∧ p5) ∨ ((p1 ∧ (p5 ∨ p5)) ∧ p1)) ∨ (p2 ∨ (p5 ∨ p1))) ∧ (False → p3)) → (p2 ∨ (p2 → ((p2 ∨ False) → True)))) ∨ p1) := by
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
      -- Conjunctions on the left can always be decomposed.
      let h6 := h5.left
      let h7 := h5.right
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Implications on the right can always be decomposed.
      intro h8
      -- Implications on the right can always be decomposed.
      intro h9
      -- True on the right can always be proven directly.
      apply True.intro
    case inr h10 =>
      -- Conjunctions on the left can always be decomposed.
      let h11 := h10.left
      let h12 := h10.right
      -- Conjunctions on the left can always be decomposed.
      let h13 := h11.left
      let h14 := h11.right
      -- Disjunctions on the left can always be decomposed.
      cases h14
      case inl h15 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- Implications on the right can always be decomposed.
        intro h16
        -- Implications on the right can always be decomposed.
        intro h17
        -- True on the right can always be proven directly.
        apply True.intro
      case inr h18 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- Implications on the right can always be decomposed.
        intro h19
        -- Implications on the right can always be decomposed.
        intro h20
        -- True on the right can always be proven directly.
        apply True.intro
  case inr h21 =>
    -- Disjunctions on the left can always be decomposed.
    cases h21
    case inl h22 =>
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- One of the premise coincides with the conclusion.
      exact h22
    case inr h23 =>
      -- Disjunctions on the left can always be decomposed.
      cases h23
      case inl h24 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- Implications on the right can always be decomposed.
        intro h25
        -- Implications on the right can always be decomposed.
        intro h26
        -- True on the right can always be proven directly.
        apply True.intro
      case inr h27 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- Implications on the right can always be decomposed.
        intro h28
        -- Implications on the right can always be decomposed.
        intro h29
        -- True on the right can always be proven directly.
        apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_677933607027746842948052596607 : (((((((p1 ∧ (False ∨ (p3 ∨ ((True → p5) ∧ True)))) ∨ (p1 → (p1 ∧ p2))) ∨ p2) → (p3 → p1)) ∨ ((False ∧ (p3 ∧ False)) → p1)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_55449430270590179505811289398 : (((((p3 → True) → (p5 ∨ p3)) → p3) → (True → (p1 ∧ ((True ∧ (p1 ∨ (p2 → (p2 → p5)))) → (((p1 ∨ p2) ∧ p4) → p3))))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_45164476190029911337852539688 : (((True ∧ ((p1 → ((p3 → p2) → (p1 ∨ ((p2 ∨ ((True ∧ p4) ∧ p1)) ∨ p5)))) ∨ ((((p1 ∧ p2) ∧ p4) ∨ p4) ∨ p4))) → False) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_778763897477833266663414518614 : (((p1 ∨ (p4 ∨ (p1 → (p4 ∨ ((p3 ∨ False) → ((False ∨ (p4 ∧ (p1 → p3))) ∨ (True ∧ (p5 → (False → (False ∧ (p3 → p4))))))))))) ∨ False) ∧ True) := by
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
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h2
  -- Disjunctions on the left can always be decomposed.
  cases h2
  case inl h3 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Conjunctions on the right can always be decomposed.
    apply And.intro
    -- True on the right can always be proven directly.
    apply True.intro
    -- Implications on the right can always be decomposed.
    intro h4
    -- Implications on the right can always be decomposed.
    intro h5
    -- Conjunctions on the right can always be decomposed.
    apply And.intro
    -- False on the left can always be used.
    apply False.elim h5
    -- Implications on the right can always be decomposed.
    intro h6
    -- False on the left can always be used.
    apply False.elim h5
  case inr h7 =>
    -- False on the left can always be used.
    apply False.elim h7
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_613629832708115933928010868355 : (((((((p5 ∨ (p2 → (False → (p1 ∧ p4)))) ∨ ((p2 ∧ p2) → (p2 → (p1 ∧ p2)))) → (p1 ∨ True)) ∧ (p3 ∧ (p3 ∧ p3))) ∨ p5) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_66763429026072034199030411737 : ((True → (p3 ∧ ((((p3 → ((p5 ∧ ((p3 → p1) → (p5 ∨ p1))) ∧ False)) ∧ True) ∨ (p1 ∨ p3)) → (((p2 ∧ p2) ∨ p3) ∧ p1)))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_262338456884764967912278341975 : (True ∧ (((p2 → (p5 ∧ (p1 ∧ (p5 ∨ p4)))) → (p1 ∧ ((((True ∧ p5) ∧ (p4 → (False ∨ (p2 ∨ p4)))) ∨ (True → p3)) → p4))) ∨ True)) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_94765546786007053184284277045 : ((p3 ∧ ((p1 ∧ (((p2 ∨ True) ∨ p5) ∧ (p4 ∨ p4))) ∧ (((False ∨ ((p2 ∧ (True ∧ p2)) ∨ (p4 ∨ (p2 → p2)))) ∨ p3) → False))) → p5) := by
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
    -- Disjunctions on the left can always be decomposed.
    cases h10
    case inl h11 =>
      -- Disjunctions on the left can always be decomposed.
      cases h9
      case inl h12 =>
        -- We want to use the implication h5 based on <expert-advice>. So we show its premise.
        have h13 : ((False ∨ ((p2 ∧ (True ∧ p2)) ∨ (p4 ∨ (p2 → p2)))) ∨ p3) := by
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- One of the premise coincides with the conclusion.
          exact h2
        -- We have shown the premise of h5, we can now drive its conclusion.
        let h14 := h5 h13
        -- False on the left can always be used.
        apply False.elim h14
      case inr h15 =>
        -- We want to use the implication h5 based on <expert-advice>. So we show its premise.
        have h16 : ((False ∨ ((p2 ∧ (True ∧ p2)) ∨ (p4 ∨ (p2 → p2)))) ∨ p3) := by
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- One of the premise coincides with the conclusion.
          exact h2
        -- We have shown the premise of h5, we can now drive its conclusion.
        let h17 := h5 h16
        -- False on the left can always be used.
        apply False.elim h17
    case inr h18 =>
      -- Disjunctions on the left can always be decomposed.
      cases h9
      case inl h19 =>
        -- We want to use the implication h5 based on <expert-advice>. So we show its premise.
        have h20 : ((False ∨ ((p2 ∧ (True ∧ p2)) ∨ (p4 ∨ (p2 → p2)))) ∨ p3) := by
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- One of the premise coincides with the conclusion.
          exact h2
        -- We have shown the premise of h5, we can now drive its conclusion.
        let h21 := h5 h20
        -- False on the left can always be used.
        apply False.elim h21
      case inr h22 =>
        -- We want to use the implication h5 based on <expert-advice>. So we show its premise.
        have h23 : ((False ∨ ((p2 ∧ (True ∧ p2)) ∨ (p4 ∨ (p2 → p2)))) ∨ p3) := by
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- One of the premise coincides with the conclusion.
          exact h2
        -- We have shown the premise of h5, we can now drive its conclusion.
        let h24 := h5 h23
        -- False on the left can always be used.
        apply False.elim h24
  case inr h25 =>
    -- Disjunctions on the left can always be decomposed.
    cases h9
    case inl h26 =>
      -- One of the premise coincides with the conclusion.
      exact h25
    case inr h27 =>
      -- One of the premise coincides with the conclusion.
      exact h25



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_136109588531735731982936362534 : ((((False ∨ (p4 ∧ p1)) → ((p5 ∨ p5) ∨ p2)) ∨ (((p1 → p5) ∨ (False ∧ True)) → (p2 ∧ (p1 → (True ∨ p4))))) ∨ ((False ∧ p1) → p2)) := by
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
theorem thm_5_vars_117196071353176844719337240202 : ((True ∧ (((p5 ∧ (p5 ∧ (p4 → ((p1 ∧ p3) ∨ ((False ∧ p5) ∨ p3))))) ∧ False) ∨ (((True ∨ p4) ∧ False) → (p1 ∨ True)))) ∨ (p3 ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_147959766062142845507610536077 : (((False ∨ (p1 ∨ ((((((True ∧ p1) → p1) ∧ (p3 ∨ p2)) ∨ True) → (False → p2)) ∧ p2))) ∧ (p4 ∨ True)) ∨ ((p1 ∧ False) ∨ (False → True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_707456819848481491365009685420 : (((((p1 ∨ (False ∨ p2)) ∧ ((True → p3) ∧ p5)) ∨ (p4 ∧ (((True ∨ p2) ∧ False) → (p1 → ((True ∧ False) ∧ ((True ∧ p5) → p2)))))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_624038722892522607259675567286 : ((((p2 ∨ ((((p4 → False) → (p4 ∨ (True ∧ p5))) ∨ (p5 → ((p1 ∨ p1) ∨ p5))) ∨ ((((p1 ∧ p3) ∨ p1) ∨ False) → p2))) ∨ p5) ∨ False) ∧ True) := by
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
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_305320600158276765710644167278 : (p1 ∨ ((p3 → ((False ∧ (((p2 ∨ (p2 ∧ (True ∧ p4))) ∧ p5) ∨ p4)) ∨ ((p1 ∧ False) → p3))) ∨ ((False ∨ ((p4 ∨ p1) ∨ p2)) ∧ p1))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
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



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_42880969611740230673934585326 : (((p3 → (((p5 ∧ ((True ∧ p1) → (p4 ∨ (p5 ∧ (True ∧ ((True ∨ p4) → p5)))))) → (p4 ∧ ((False ∧ p2) ∧ False))) ∧ p1)) ∨ p5) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_38976416241341393873587550371 : ((((p2 ∧ p2) ∧ ((p3 → (((p5 ∨ p4) ∨ p3) ∧ (((p4 → (p2 ∨ p2)) ∧ p2) ∧ ((p4 ∨ p5) → p4)))) → (True → p2))) ∧ p3) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_197543464647033234826148021234 : ((((p4 ∧ (False ∧ p1)) ∨ p3) ∨ (p5 ∨ True)) ∨ (((False ∨ p1) ∨ (True ∨ p2)) → (p3 ∧ (((True ∨ ((p3 ∧ p1) ∧ p4)) → p1) → p5)))) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_65769645877382517662455398430 : ((p4 ∨ (((p1 → (False ∧ ((True ∧ False) ∨ (p3 ∨ (p2 ∧ p2))))) → ((True ∧ p5) → p3)) ∨ (p5 ∨ ((p3 ∨ p3) ∧ (p3 ∨ False))))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_664428007538253559745269385001 : ((((p3 ∨ (p1 ∨ (((((p3 ∧ False) → (p2 ∧ p2)) ∨ (p3 ∨ (p4 ∧ p2))) ∨ p1) → ((p1 ∨ p3) → (False ∨ False))))) → (p4 ∧ True)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_184833330977763055839035400174 : ((((p2 ∧ p4) → (p1 → False)) → (p3 ∧ ((p3 → p4) → p5))) ∨ (True ∨ (p2 → (False ∨ ((((False ∨ (p3 ∨ p2)) → p5) ∧ True) ∧ p5))))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_94263686505206047700982546870 : ((p2 ∧ ((((p1 ∨ p4) → p3) → (p5 ∨ ((p1 ∨ p4) ∨ (False → (((p3 → (p5 ∧ (p4 → False))) ∨ False) → True))))) → (p2 ∧ False))) → False) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- We want to use the implication h3 based on <expert-advice>. So we show its premise.
  have h4 : (((p1 ∨ p4) → p3) → (p5 ∨ ((p1 ∨ p4) ∨ (False → (((p3 → (p5 ∧ (p4 → False))) ∨ False) → True))))) := by
    -- Implications on the right can always be decomposed.
    intro h5
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h6
    -- Implications on the right can always be decomposed.
    intro h7
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h3, we can now drive its conclusion.
  let h8 := h3 h4
  -- We need to get the right conjuct of h8 based on <expert-advice>.
  let h9 := h8.right
  -- False on the left can always be used.
  apply False.elim h9



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_329158585993230908859461776307 : (True → (((p1 ∧ (False ∨ p5)) → False) → ((True ∧ (((p1 ∨ (False ∨ p1)) ∨ p5) ∧ (p3 → (p3 ∨ (p2 ∧ p1))))) → ((p5 → p4) ∨ p5)))) := by
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
  let h6 := h5.left
  let h7 := h5.right
  -- Disjunctions on the left can always be decomposed.
  cases h6
  case inl h8 =>
    -- Disjunctions on the left can always be decomposed.
    cases h8
    case inl h9 =>
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- Implications on the right can always be decomposed.
      intro h10
      -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
      have h11 : (p1 ∧ (False ∨ p5)) := by
        -- Conjunctions on the right can always be decomposed.
        apply And.intro
        -- One of the premise coincides with the conclusion.
        exact h9
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- One of the premise coincides with the conclusion.
        exact h10
      -- We have shown the premise of h2, we can now drive its conclusion.
      let h12 := h2 h11
      -- False on the left can always be used.
      apply False.elim h12
    case inr h13 =>
      -- Disjunctions on the left can always be decomposed.
      cases h13
      case inl h14 =>
        -- False on the left can always be used.
        apply False.elim h14
      case inr h15 =>
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- Implications on the right can always be decomposed.
        intro h16
        -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
        have h17 : (p1 ∧ (False ∨ p5)) := by
          -- Conjunctions on the right can always be decomposed.
          apply And.intro
          -- One of the premise coincides with the conclusion.
          exact h15
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- One of the premise coincides with the conclusion.
          exact h16
        -- We have shown the premise of h2, we can now drive its conclusion.
        let h18 := h2 h17
        -- False on the left can always be used.
        apply False.elim h18
  case inr h19 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h19



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_118345849714487810640063454812 : ((p2 ∨ ((p3 → ((False ∧ ((p5 → p1) → p5)) ∧ (p4 ∧ (p5 → ((((False ∨ p5) ∧ p3) ∨ (p1 → p4)) ∨ p4))))) ∨ p4)) ∨ (p3 ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_663129509569247535549752247377 : (((((p2 ∨ True) ∧ ((p5 ∨ (((True → False) → (p2 ∧ p2)) → (p1 ∧ False))) ∧ ((True → ((p4 ∧ False) ∧ p1)) → p5))) → (False ∧ p5)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_158285397506330051093950733467 : ((((p1 ∨ p3) ∧ p3) → (((True → ((p1 → p2) → False)) ∨ True) ∨ (True ∧ (p5 → (p3 ∧ p4))))) ∨ ((p2 → ((p2 ∧ p1) ∧ p1)) ∨ p1)) := by
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
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro
  case inr h5 =>
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_178482471153391903447001634564 : ((((p2 ∧ (p5 ∨ (p2 ∧ p3))) ∧ (True ∨ False)) ∨ (p2 → (p1 ∨ p2))) ∨ (p5 ∨ (((False → (p4 → False)) → True) ∧ ((p1 ∧ p2) → p2)))) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_258386940055890671701422320495 : ((p5 ∨ False) → (True → ((((((p5 → p1) ∨ p3) → (p3 ∧ False)) ∨ p5) ∧ (((p2 ∨ p4) → p3) → True)) ∨ (p4 → (p5 → (p3 ∨ p4)))))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h3 =>
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Conjunctions on the right can always be decomposed.
    apply And.intro
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h3
    -- Implications on the right can always be decomposed.
    intro h4
    -- True on the right can always be proven directly.
    apply True.intro
  case inr h5 =>
    -- False on the left can always be used.
    apply False.elim h5



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_340803411709691193626272904617 : (p2 → (((True → (p3 ∨ (p4 ∨ (((((p4 → True) → ((False ∧ p5) → (p1 ∨ (p4 → p3)))) → p3) ∧ p3) → (p1 → p5))))) → p1) ∨ True)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_488155331858987460235839504191 : (((((p4 ∨ True) → ((p5 ∧ p3) ∧ False)) → (((p3 ∧ p2) → p1) ∧ ((p4 ∨ True) → (((p5 ∧ True) ∨ (p1 ∧ p1)) ∧ (False ∧ p2))))) ∧ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h2
  -- Conjunctions on the left can always be decomposed.
  let h3 := h2.left
  let h4 := h2.right
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h5 : (p4 ∨ True) := by
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h6 := h1 h5
  -- We need to get the right conjuct of h6 based on <expert-advice>.
  let h7 := h6.right
  -- False on the left can always be used.
  apply False.elim h7
  -- Implications on the right can always be decomposed.
  intro h8
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Disjunctions on the left can always be decomposed.
  cases h8
  case inl h9 =>
    -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
    have h10 : (p4 ∨ True) := by
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- One of the premise coincides with the conclusion.
      exact h9
    -- We have shown the premise of h1, we can now drive its conclusion.
    let h11 := h1 h10
    -- We need to get the right conjuct of h11 based on <expert-advice>.
    let h12 := h11.right
    -- False on the left can always be used.
    apply False.elim h12
  case inr h13 =>
    -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
    have h14 : (p4 ∨ True) := by
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- True on the right can always be proven directly.
      apply True.intro
    -- We have shown the premise of h1, we can now drive its conclusion.
    let h15 := h1 h14
    -- We need to get the right conjuct of h15 based on <expert-advice>.
    let h16 := h15.right
    -- False on the left can always be used.
    apply False.elim h16
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Disjunctions on the left can always be decomposed.
  cases h8
  case inl h17 =>
    -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
    have h18 : (p4 ∨ True) := by
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- One of the premise coincides with the conclusion.
      exact h17
    -- We have shown the premise of h1, we can now drive its conclusion.
    let h19 := h1 h18
    -- We need to get the right conjuct of h19 based on <expert-advice>.
    let h20 := h19.right
    -- False on the left can always be used.
    apply False.elim h20
  case inr h21 =>
    -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
    have h22 : (p4 ∨ True) := by
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- True on the right can always be proven directly.
      apply True.intro
    -- We have shown the premise of h1, we can now drive its conclusion.
    let h23 := h1 h22
    -- We need to get the right conjuct of h23 based on <expert-advice>.
    let h24 := h23.right
    -- False on the left can always be used.
    apply False.elim h24
  -- Disjunctions on the left can always be decomposed.
  cases h8
  case inl h25 =>
    -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
    have h26 : (p4 ∨ True) := by
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- One of the premise coincides with the conclusion.
      exact h25
    -- We have shown the premise of h1, we can now drive its conclusion.
    let h27 := h1 h26
    -- We need to get the right conjuct of h27 based on <expert-advice>.
    let h28 := h27.right
    -- False on the left can always be used.
    apply False.elim h28
  case inr h29 =>
    -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
    have h30 : (p4 ∨ True) := by
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- True on the right can always be proven directly.
      apply True.intro
    -- We have shown the premise of h1, we can now drive its conclusion.
    let h31 := h1 h30
    -- We need to get the right conjuct of h31 based on <expert-advice>.
    let h32 := h31.right
    -- False on the left can always be used.
    apply False.elim h32
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_728201696261678411595184859196 : ((((True → (p3 ∧ p3)) ∨ ((p5 → True) → (((p4 ∧ (p1 ∧ True)) ∨ ((((p3 → p2) ∨ (p2 ∨ p4)) ∧ p4) ∨ (False ∨ True))) ∨ p3))) ∨ p1) ∧ True) := by
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
theorem thm_5_vars_43083540179062080893337701930 : (((((((((p2 → True) → (p5 ∧ False)) → ((p3 → True) ∧ p1)) ∨ ((p4 → (p5 → p1)) ∧ p2)) → p3) ∨ (p3 → p3)) ∧ True) → p2) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_157933462814149619746219918655 : (((((p5 ∧ p5) ∧ (p3 ∨ p1)) ∧ (True ∧ p5)) ∧ (p2 ∧ (((p5 → (p1 ∧ p1)) → True) → p3))) ∨ (p1 → (True ∨ (True → (p5 ∨ p2))))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_325794818882557243627891670767 : (p5 ∨ (p3 ∨ (((((p4 ∨ p5) ∨ (((p1 → (p5 ∨ (p1 ∧ p3))) ∨ p1) ∨ ((True ∧ True) → False))) ∨ True) → (False ∨ (False → p2))) ∨ p5))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h2 =>
    -- Disjunctions on the left can always be decomposed.
    cases h2
    case inl h3 =>
      -- Disjunctions on the left can always be decomposed.
      cases h3
      case inl h4 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- Implications on the right can always be decomposed.
        intro h5
        -- False on the left can always be used.
        apply False.elim h5
      case inr h6 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- Implications on the right can always be decomposed.
        intro h7
        -- False on the left can always be used.
        apply False.elim h7
    case inr h8 =>
      -- Disjunctions on the left can always be decomposed.
      cases h8
      case inl h9 =>
        -- Disjunctions on the left can always be decomposed.
        cases h9
        case inl h10 =>
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- Implications on the right can always be decomposed.
          intro h11
          -- False on the left can always be used.
          apply False.elim h11
        case inr h12 =>
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- Implications on the right can always be decomposed.
          intro h13
          -- False on the left can always be used.
          apply False.elim h13
      case inr h14 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- Implications on the right can always be decomposed.
        intro h15
        -- False on the left can always be used.
        apply False.elim h15
  case inr h16 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h17
    -- False on the left can always be used.
    apply False.elim h17



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_668041438557189441607120656650 : ((((p5 ∨ (((p3 → p1) ∨ ((p1 → True) → ((((p5 → p3) → (p1 ∨ p3)) ∧ p3) ∧ p4))) → (p4 → p3))) ∧ (p3 ∨ (False ∧ p2))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_221816169673470734813309057619 : (((p2 ∧ p5) → True) ∧ ((((((p4 → ((((p3 → False) ∨ p3) ∨ (p1 → (p2 ∧ p2))) ∨ (p3 ∧ p1))) ∧ p2) ∧ p3) → p4) ∨ p4) ∨ True)) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_161443295193648869559181010417 : ((p2 ∧ (True ∨ ((((p5 ∨ True) ∨ (p2 → True)) ∨ (((p4 ∨ p2) ∧ True) ∧ (p3 ∨ p5))) ∨ p5))) → (((p3 → p1) ∧ (p5 ∧ False)) ∨ p2)) := by
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
    -- One of the premise coincides with the conclusion.
    exact h2
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
          -- Disjunctions on the left can always be decomposed.
          cases h8
          case inl h9 =>
            -- Show the right disjunct based on <expert-advice>.
            apply Or.inr
            -- One of the premise coincides with the conclusion.
            exact h2
          case inr h10 =>
            -- Show the right disjunct based on <expert-advice>.
            apply Or.inr
            -- One of the premise coincides with the conclusion.
            exact h2
        case inr h11 =>
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- One of the premise coincides with the conclusion.
          exact h2
      case inr h12 =>
        -- Conjunctions on the left can always be decomposed.
        let h13 := h12.left
        let h14 := h12.right
        -- Conjunctions on the left can always be decomposed.
        let h15 := h13.left
        let h16 := h13.right
        -- Disjunctions on the left can always be decomposed.
        cases h15
        case inl h17 =>
          -- Disjunctions on the left can always be decomposed.
          cases h14
          case inl h18 =>
            -- Show the right disjunct based on <expert-advice>.
            apply Or.inr
            -- One of the premise coincides with the conclusion.
            exact h2
          case inr h19 =>
            -- Show the right disjunct based on <expert-advice>.
            apply Or.inr
            -- One of the premise coincides with the conclusion.
            exact h2
        case inr h20 =>
          -- Disjunctions on the left can always be decomposed.
          cases h14
          case inl h21 =>
            -- Show the right disjunct based on <expert-advice>.
            apply Or.inr
            -- One of the premise coincides with the conclusion.
            exact h20
          case inr h22 =>
            -- Show the right disjunct based on <expert-advice>.
            apply Or.inr
            -- One of the premise coincides with the conclusion.
            exact h20
    case inr h23 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- One of the premise coincides with the conclusion.
      exact h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_54575511345998094141467660744 : (((p1 ∨ (((p1 → (p4 ∨ p4)) ∨ False) ∨ p5)) ∨ (((True ∨ ((((True → p5) → p5) ∨ p5) ∨ p2)) ∨ False) → ((p3 ∨ p3) → True))) ∨ False) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_172432012475939466874683861703 : (((p3 ∨ (p2 ∨ (p3 ∨ p2))) ∧ (((((p2 → p4) ∨ p3) ∨ p4) → False) → p5)) ∨ (((p3 → (p1 ∨ ((p3 ∨ p2) ∨ p2))) ∧ False) → p5)) := by
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
theorem thm_5_vars_4682282477917017690123125555 : (p5 → (p3 → ((((p3 → ((p1 → False) ∧ False)) ∧ ((((p2 ∨ p1) ∧ False) ∨ True) → (True → (p5 ∨ p2)))) → (False ∨ False)) ∨ p3))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_230864050856713462908078808943 : (((p1 ∧ p4) ∨ True) → (((False → (((p4 ∨ (p1 ∨ p1)) ∨ p2) → (p3 ∧ (True ∨ p5)))) ∧ p5) → (p3 ∨ (p3 → (p3 ∧ (p1 ∨ p3)))))) := by
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
    -- Conjunctions on the left can always be decomposed.
    let h6 := h5.left
    let h7 := h5.right
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h8
    -- Conjunctions on the right can always be decomposed.
    apply And.intro
    -- One of the premise coincides with the conclusion.
    exact h8
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- One of the premise coincides with the conclusion.
    exact h6
  case inr h9 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h10
    -- Conjunctions on the right can always be decomposed.
    apply And.intro
    -- One of the premise coincides with the conclusion.
    exact h10
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h10



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_172499881941896373709243026296 : ((((p1 ∧ p2) ∧ True) ∧ ((p4 ∧ (p4 → (True ∨ (p1 ∧ p4)))) ∨ (p2 → p3))) ∨ (p2 → (p4 ∨ (p5 → (p1 ∨ ((p1 ∨ p5) ∨ p3)))))) := by
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
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_319307898329661685873381217761 : (p4 ∨ (((p5 ∧ ((True ∧ (p5 ∨ (False ∨ p4))) ∧ p5)) ∧ (p1 → (False ∨ (p1 ∧ True)))) → ((p1 ∨ (False ∨ p5)) ∧ ((p5 ∨ p1) ∨ p5)))) := by
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
  let h6 := h5.left
  let h7 := h5.right
  -- Conjunctions on the left can always be decomposed.
  let h8 := h6.left
  let h9 := h6.right
  -- Disjunctions on the left can always be decomposed.
  cases h9
  case inl h10 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h7
  case inr h11 =>
    -- Disjunctions on the left can always be decomposed.
    cases h11
    case inl h12 =>
      -- False on the left can always be used.
      apply False.elim h12
    case inr h13 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- One of the premise coincides with the conclusion.
      exact h7
  -- Conjunctions on the left can always be decomposed.
  let h14 := h1.left
  let h15 := h1.right
  -- Conjunctions on the left can always be decomposed.
  let h16 := h14.left
  let h17 := h14.right
  -- Conjunctions on the left can always be decomposed.
  let h18 := h17.left
  let h19 := h17.right
  -- Conjunctions on the left can always be decomposed.
  let h20 := h18.left
  let h21 := h18.right
  -- Disjunctions on the left can always be decomposed.
  cases h21
  case inl h22 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h19
  case inr h23 =>
    -- Disjunctions on the left can always be decomposed.
    cases h23
    case inl h24 =>
      -- False on the left can always be used.
      apply False.elim h24
    case inr h25 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- One of the premise coincides with the conclusion.
      exact h19



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_81886021859843471216928245102 : (((((((((p4 ∨ ((p5 ∧ (True → p1)) → p4)) → (p4 ∧ p2)) → p3) ∧ p4) → False) → p2) ∨ (True ∨ p4)) → ((p2 ∧ False) ∧ p2)) → p5) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h2 : (((((((p4 ∨ ((p5 ∧ (True → p1)) → p4)) → (p4 ∧ p2)) → p3) ∧ p4) → False) → p2) ∨ (True ∨ p4)) := by
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h3 := h1 h2
  -- We need to get the left conjuct of h3 based on <expert-advice>.
  let h4 := h3.left
  -- We need to get the right conjuct of h4 based on <expert-advice>.
  let h5 := h4.right
  -- False on the left can always be used.
  apply False.elim h5



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_202983946087485960760673398306 : (((p5 → True) ∨ (p4 ∧ (p4 → True))) ∧ ((p3 ∧ False) ∨ (((((p1 → p3) ∨ p3) ∧ ((True ∧ p5) → False)) ∨ True) ∨ (p4 ∧ (p5 → False))))) := by
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
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_52238955054733724427951675959 : (((p4 ∧ (((p3 → p4) ∨ (((False ∧ p2) ∨ ((p4 ∧ True) → p3)) ∧ p1)) ∨ p2)) → (p2 ∧ (False ∧ (((p3 ∨ p2) → p4) ∧ True)))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_149428376685327052860773660091 : ((True ∧ (p4 ∧ (((p3 ∧ p3) ∨ p3) → (((((False ∨ p5) ∧ False) ∨ (p3 ∨ (False → p1))) → p5) ∧ p5)))) ∨ ((p1 ∧ (False → p1)) → True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_160273939956016246755407071971 : (((p4 → (p3 → (p3 ∧ (((p4 ∧ p1) → p4) → ((p1 → (p2 ∧ p5)) ∨ p4))))) ∨ (p2 ∨ p2)) → (p5 ∨ (p5 → (False ∨ (False → p1))))) := by
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
    -- Implications on the right can always be decomposed.
    intro h4
    -- False on the left can always be used.
    apply False.elim h4
  case inr h5 =>
    -- Disjunctions on the left can always be decomposed.
    cases h5
    case inl h6 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Implications on the right can always be decomposed.
      intro h7
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Implications on the right can always be decomposed.
      intro h8
      -- False on the left can always be used.
      apply False.elim h8
    case inr h9 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Implications on the right can always be decomposed.
      intro h10
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Implications on the right can always be decomposed.
      intro h11
      -- False on the left can always be used.
      apply False.elim h11



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_248304735693423130777551346221 : ((p2 ∨ p2) ∨ (p5 ∨ ((p2 ∨ (((((p2 → p5) → ((p1 ∧ p2) ∧ p1)) → ((p5 → p2) ∨ (True ∨ p4))) ∧ (p2 → p2)) ∨ p5)) ∧ True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro
  -- Implications on the right can always be decomposed.
  intro h2
  -- One of the premise coincides with the conclusion.
  exact h2
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_616657045289761756912148315477 : (((((p3 ∨ (p4 ∨ (p5 → ((False → (False ∨ True)) ∧ p5)))) ∧ (p1 ∧ ((p3 → p3) → (((True → p5) ∨ p5) → (p5 ∧ True))))) ∨ False) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_672616975207000884076575505562 : (((((p5 → (((p5 ∨ ((p5 ∧ True) ∧ (p3 ∧ (p2 → (True ∨ True))))) ∧ True) ∧ (p2 → True))) ∧ (p2 ∨ p1)) → ((p2 ∨ p4) ∨ p3)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_699394523947352793648616556686 : (((((p4 ∨ ((p4 ∧ p5) ∧ (p4 ∨ (p5 → (p1 ∧ False))))) ∧ p1) → ((((p1 ∧ ((p2 ∨ False) → False)) → p1) ∨ p2) ∨ (p1 → True))) ∨ p4) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
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
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h5
    -- True on the right can always be proven directly.
    apply True.intro
  case inr h6 =>
    -- Conjunctions on the left can always be decomposed.
    let h7 := h6.left
    let h8 := h6.right
    -- Conjunctions on the left can always be decomposed.
    let h9 := h7.left
    let h10 := h7.right
    -- Disjunctions on the left can always be decomposed.
    cases h8
    case inl h11 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Implications on the right can always be decomposed.
      intro h12
      -- True on the right can always be proven directly.
      apply True.intro
    case inr h13 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Implications on the right can always be decomposed.
      intro h14
      -- True on the right can always be proven directly.
      apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_617243124557385291484650677364 : (((((p3 ∧ (False ∨ (((True ∨ False) ∨ p4) ∧ p5))) ∨ ((((p1 → p2) ∧ True) → (p4 ∧ (p5 ∨ (True ∧ p1)))) ∨ (p2 → p4))) ∨ False) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_190122271244839418440235801315 : ((((p2 → (p3 ∨ p1)) ∨ ((p4 ∨ False) → p5)) ∧ p2) ∨ (p5 → (p1 → ((p1 → p3) ∨ (((p5 ∧ p2) ∨ p1) ∨ ((p5 → False) ∨ p3)))))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_613624139667596775308321526614 : ((((((False ∨ (p3 ∧ ((p1 ∧ ((True → ((p2 ∧ p5) ∨ (False → p1))) ∧ False)) → p1))) ∨ (False ∨ p1)) ∧ (p2 ∧ (p5 ∨ False))) ∨ True) ∨ p1) ∧ True) := by
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
theorem thm_5_vars_54666928482239595119503941451 : ((((p1 → (p1 ∨ ((p1 → p3) ∧ p3))) ∨ False) → (False ∨ (p4 ∨ ((((((p4 ∨ False) → p4) ∨ False) → (p4 ∨ p2)) ∨ p5) ∨ True)))) ∨ p2) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h2 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro
  case inr h3 =>
    -- False on the left can always be used.
    apply False.elim h3



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_350161827161835389123754322291 : (p4 → (((p5 ∧ ((p3 ∨ True) → ((False ∧ p5) ∧ p5))) ∨ ((False ∨ p5) ∨ (((((p5 ∨ False) → p4) → (p2 → p5)) ∨ p4) → p4))) ∨ p5)) := by
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
  -- Disjunctions on the left can always be decomposed.
  cases h2
  case inl h3 =>
    -- One of the premise coincides with the conclusion.
    exact h1
  case inr h4 =>
    -- One of the premise coincides with the conclusion.
    exact h4



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_193099187580209765029898569336 : (((p1 ∨ (True ∨ (False ∧ False))) ∧ ((p1 ∨ p5) ∨ p5)) → ((p4 → (p2 ∨ p1)) ∨ ((((p4 → p5) ∨ p5) ∨ (True ∨ (True ∨ p4))) ∧ True))) := by
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
      -- Disjunctions on the left can always be decomposed.
      cases h5
      case inl h6 =>
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
        -- True on the right can always be proven directly.
        apply True.intro
      case inr h7 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- Conjunctions on the right can always be decomposed.
        apply And.intro
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- One of the premise coincides with the conclusion.
        exact h7
        -- True on the right can always be proven directly.
        apply True.intro
    case inr h8 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Conjunctions on the right can always be decomposed.
      apply And.intro
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- One of the premise coincides with the conclusion.
      exact h8
      -- True on the right can always be proven directly.
      apply True.intro
  case inr h9 =>
    -- Disjunctions on the left can always be decomposed.
    cases h9
    case inl h10 =>
      -- Disjunctions on the left can always be decomposed.
      cases h3
      case inl h11 =>
        -- Disjunctions on the left can always be decomposed.
        cases h11
        case inl h12 =>
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
          -- True on the right can always be proven directly.
          apply True.intro
        case inr h13 =>
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- Conjunctions on the right can always be decomposed.
          apply And.intro
          -- Show the left disjunct based on <expert-advice>.
          apply Or.inl
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- One of the premise coincides with the conclusion.
          exact h13
          -- True on the right can always be proven directly.
          apply True.intro
      case inr h14 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- Conjunctions on the right can always be decomposed.
        apply And.intro
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- One of the premise coincides with the conclusion.
        exact h14
        -- True on the right can always be proven directly.
        apply True.intro
    case inr h15 =>
      -- Conjunctions on the left can always be decomposed.
      let h16 := h15.left
      let h17 := h15.right
      -- False on the left can always be used.
      apply False.elim h16



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_46962998651195861180435362854 : ((((((((((p4 ∧ p5) → (p1 → p3)) → p3) ∨ ((False → p4) → p3)) ∧ ((p1 ∨ p5) → p3)) → p4) ∨ p1) → p5) ∨ (True ∨ True)) ∨ False) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_180959417567778557739797940448 : (((True → False) ∧ (((p5 ∧ p3) → p2) ∨ (p4 → ((p1 ∨ p4) ∧ p5)))) → (((p4 ∨ True) → ((p4 ∧ (p5 ∧ (p4 ∨ p1))) → p5)) ∧ False)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
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
  -- Disjunctions on the left can always be decomposed.
  cases h7
  case inl h8 =>
    -- Disjunctions on the left can always be decomposed.
    cases h2
    case inl h9 =>
      -- Conjunctions on the left can always be decomposed.
      let h10 := h1.left
      let h11 := h1.right
      -- Disjunctions on the left can always be decomposed.
      cases h11
      case inl h12 =>
        -- One of the premise coincides with the conclusion.
        exact h6
      case inr h13 =>
        -- One of the premise coincides with the conclusion.
        exact h6
    case inr h14 =>
      -- Conjunctions on the left can always be decomposed.
      let h15 := h1.left
      let h16 := h1.right
      -- Disjunctions on the left can always be decomposed.
      cases h16
      case inl h17 =>
        -- One of the premise coincides with the conclusion.
        exact h6
      case inr h18 =>
        -- One of the premise coincides with the conclusion.
        exact h6
  case inr h19 =>
    -- Disjunctions on the left can always be decomposed.
    cases h2
    case inl h20 =>
      -- Conjunctions on the left can always be decomposed.
      let h21 := h1.left
      let h22 := h1.right
      -- Disjunctions on the left can always be decomposed.
      cases h22
      case inl h23 =>
        -- One of the premise coincides with the conclusion.
        exact h6
      case inr h24 =>
        -- One of the premise coincides with the conclusion.
        exact h6
    case inr h25 =>
      -- Conjunctions on the left can always be decomposed.
      let h26 := h1.left
      let h27 := h1.right
      -- Disjunctions on the left can always be decomposed.
      cases h27
      case inl h28 =>
        -- One of the premise coincides with the conclusion.
        exact h6
      case inr h29 =>
        -- One of the premise coincides with the conclusion.
        exact h6
  -- Conjunctions on the left can always be decomposed.
  let h30 := h1.left
  let h31 := h1.right
  -- Disjunctions on the left can always be decomposed.
  cases h31
  case inl h32 =>
    -- We want to use the implication h30 based on <expert-advice>. So we show its premise.
    have h33 : True := by
      -- True on the right can always be proven directly.
      apply True.intro
    -- We have shown the premise of h30, we can now drive its conclusion.
    let h34 := h30 h33
    -- False on the left can always be used.
    apply False.elim h34
  case inr h35 =>
    -- We want to use the implication h30 based on <expert-advice>. So we show its premise.
    have h36 : True := by
      -- True on the right can always be proven directly.
      apply True.intro
    -- We have shown the premise of h30, we can now drive its conclusion.
    let h37 := h30 h36
    -- False on the left can always be used.
    apply False.elim h37



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_717961021239153384285028418255 : (((((p4 → (True → False)) ∧ p1) ∨ ((p5 ∨ (p1 ∨ (p5 ∨ p4))) ∨ (((p3 ∧ (p1 → ((p4 ∨ p4) ∧ p5))) → p2) → (False ∨ True)))) ∨ p4) ∧ True) := by
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
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



