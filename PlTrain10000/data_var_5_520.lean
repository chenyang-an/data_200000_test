variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_262285228109424071258737727688 : (True ∧ ((((((p2 → (p3 ∨ p5)) ∨ p3) ∨ (p3 → p5)) → (((p3 → p4) → p4) → p3)) ∨ ((False → p1) ∧ ((p3 ∧ False) → False))) ∨ p4)) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h1
  -- False on the left can always be used.
  apply False.elim h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Conjunctions on the left can always be decomposed.
  let h3 := h2.left
  let h4 := h2.right
  -- False on the left can always be used.
  apply False.elim h4



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_59790459324953042005850968680 : (((p2 ∧ p2) → (((((((p3 → p3) ∧ p2) ∨ (((False → False) ∨ (p1 ∧ False)) ∧ True)) → True) → p3) ∨ p1) ∨ (p1 → (p5 ∨ p2)))) ∨ p3) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h4
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h3



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_263118184294975167080029998625 : (True ∧ ((((False ∨ (((p4 → p5) → (p4 ∧ True)) ∨ p2)) → (False ∨ (False ∨ p3))) ∨ ((p3 ∧ (False ∨ (p2 ∨ False))) ∧ p5)) ∨ (p3 → True))) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_652368532872320696855051440693 : ((((p4 ∧ (((True ∧ (p3 → p1)) ∨ (True ∧ p2)) ∧ ((((p3 ∧ p2) → p1) ∨ p4) ∧ (p2 → (False ∧ (False ∨ p4)))))) ∧ (False ∧ p4)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_51025096778885741793460756528 : (((p3 ∧ ((p1 ∨ ((p5 → p2) → p5)) ∨ ((p5 ∨ (False → True)) → (p4 → (p1 → p2))))) ∧ (p4 → (p5 ∨ (p4 ∧ (p2 ∨ p4))))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_42564219569201949034238935995 : (((p1 ∨ (p5 → (((False ∨ (p5 ∧ p5)) → True) ∧ ((False ∧ p3) ∨ (((p4 ∧ p3) ∨ (p2 → True)) ∨ (False ∧ (False ∨ True))))))) ∨ p4) ∨ False) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
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
  -- True on the right can always be proven directly.
  apply True.intro
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



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_346916066921835691221975035700 : (p3 → (((True → True) ∧ (((p5 ∨ (p2 ∧ p3)) ∧ (True ∨ p1)) ∨ (((p2 ∨ p1) ∨ p2) ∨ p5))) ∨ (p3 → (p1 → ((True ∨ p4) ∨ p4))))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h2
  -- Implications on the right can always be decomposed.
  intro h3
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_157128888947452684651868594344 : (((((p2 ∨ ((p2 ∨ True) ∧ p3)) → ((True ∧ (p4 ∨ p1)) → (True ∨ (p3 ∧ False)))) ∧ True) → p2) ∨ ((False → (False → p2)) ∨ (p3 ∧ p4))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- False on the left can always be used.
  apply False.elim h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_114290902559484003552421487717 : (((((((p2 → True) ∨ p2) ∧ p5) → (p1 ∨ (p3 → ((True → p5) → p3)))) ∧ (True ∧ True)) ∧ (p3 → ((p2 ∧ p1) ∨ False))) ∨ (False → p3)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_345819119552726364448521645151 : (p3 → ((((((p1 ∨ (((False → (False ∧ (p4 ∨ p3))) ∧ ((p3 → True) ∧ ((p1 ∨ p5) → p1))) ∧ True)) ∧ p5) ∧ p5) ∨ p3) → False) → p4)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
  have h3 : ((((p1 ∨ (((False → (False ∧ (p4 ∨ p3))) ∧ ((p3 → True) ∧ ((p1 ∨ p5) → p1))) ∧ True)) ∧ p5) ∧ p5) ∨ p3) := by
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h1
  -- We have shown the premise of h2, we can now drive its conclusion.
  let h4 := h2 h3
  -- False on the left can always be used.
  apply False.elim h4



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_234070707961799232276683022647 : ((True → (False ∧ p1)) → (((True ∧ False) ∨ (p4 ∧ (False ∧ ((((False ∧ p5) ∧ p4) ∨ p2) → ((p3 ∧ p4) → (p5 ∧ p4)))))) ∧ (p5 → p1))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h2 : True := by
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h3 := h1 h2
  -- We need to get the left conjuct of h3 based on <expert-advice>.
  let h4 := h3.left
  -- False on the left can always be used.
  apply False.elim h4
  -- Implications on the right can always be decomposed.
  intro h5
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h6 : True := by
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h7 := h1 h6
  -- We need to get the right conjuct of h7 based on <expert-advice>.
  let h8 := h7.right
  -- One of the premise coincides with the conclusion.
  exact h8



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_690418189055973129218911211894 : ((((((((p1 ∧ False) ∨ (p4 ∧ ((False → (p3 ∧ True)) ∧ p5))) → p2) ∨ p4) ∧ p5) → ((((p3 → p2) ∧ p1) ∧ (p3 ∧ p4)) ∧ False)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_320055458690685821608800847762 : (p4 ∨ ((False ∨ (p4 ∧ False)) ∨ ((p5 → (True ∧ (True ∧ p1))) ∨ ((p2 ∨ ((((p4 ∧ p3) ∧ p5) → p4) ∧ p5)) ∨ (p3 ∨ (True ∧ True)))))) := by
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
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_66275190197806999014187825444 : ((p5 ∨ (((True ∧ p3) ∨ p3) → ((False ∨ p5) ∨ ((False ∨ False) → (True ∧ (((p1 ∧ ((p3 ∧ p5) ∨ True)) ∨ (p4 ∨ p3)) ∨ p5)))))) ∨ p4) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
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
    -- Conjunctions on the right can always be decomposed.
    apply And.intro
    -- True on the right can always be proven directly.
    apply True.intro
    -- Disjunctions on the left can always be decomposed.
    cases h5
    case inl h6 =>
      -- False on the left can always be used.
      apply False.elim h6
    case inr h7 =>
      -- False on the left can always be used.
      apply False.elim h7
  case inr h8 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h9
    -- Conjunctions on the right can always be decomposed.
    apply And.intro
    -- True on the right can always be proven directly.
    apply True.intro
    -- Disjunctions on the left can always be decomposed.
    cases h9
    case inl h10 =>
      -- False on the left can always be used.
      apply False.elim h10
    case inr h11 =>
      -- False on the left can always be used.
      apply False.elim h11



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_160476483261218423624729992025 : (((False ∨ ((False ∧ (p1 → (p4 ∨ p4))) → ((False → p1) ∧ (p3 ∧ p3)))) → (False ∧ (True ∧ p4))) → ((p4 ∧ (p3 → p1)) ∨ (p5 ∧ p3))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h2 : (False ∨ ((False ∧ (p1 → (p4 ∨ p4))) → ((False → p1) ∧ (p3 ∧ p3)))) := by
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h3
    -- Conjunctions on the right can always be decomposed.
    apply And.intro
    -- Implications on the right can always be decomposed.
    intro h4
    -- False on the left can always be used.
    apply False.elim h4
    -- Conjunctions on the right can always be decomposed.
    apply And.intro
    -- Conjunctions on the left can always be decomposed.
    let h5 := h3.left
    let h6 := h3.right
    -- False on the left can always be used.
    apply False.elim h5
    -- Conjunctions on the left can always be decomposed.
    let h7 := h3.left
    let h8 := h3.right
    -- False on the left can always be used.
    apply False.elim h7
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h9 := h1 h2
  -- We need to get the left conjuct of h9 based on <expert-advice>.
  let h10 := h9.left
  -- False on the left can always be used.
  apply False.elim h10



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_313920139953159503949021882837 : (p3 ∨ (((((False → ((True ∧ (p5 ∧ True)) ∨ p5)) ∧ ((False ∨ p4) ∧ (((p4 ∧ p4) ∨ (True ∨ p5)) ∨ True))) ∨ p3) ∧ p3) ∨ (True ∨ False))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_63336759937028847490810142631 : ((p5 ∧ ((p4 → p1) → ((((p4 ∧ False) → ((p1 ∨ (((True → p4) ∧ (p5 ∨ p2)) → (False ∨ p1))) ∨ (p5 → p2))) → p5) ∧ p2))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_731383087467774255082094369851 : ((((p5 ∨ (p1 ∨ p3)) → ((p4 → ((p4 → False) → (p1 → p5))) ∧ ((p5 → (((((p4 ∧ True) → True) ∨ p3) ∧ p5) → p2)) ∨ True))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_259892998351609471841956940753 : ((p1 → p4) → ((p4 ∨ p5) → (p3 → (((p2 ∨ p2) ∧ (((p2 ∨ p4) ∧ False) → p1)) → ((((False → True) ∨ (False → p1)) → p4) ∨ True))))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Implications on the right can always be decomposed.
  intro h3
  -- Implications on the right can always be decomposed.
  intro h4
  -- Conjunctions on the left can always be decomposed.
  let h5 := h4.left
  let h6 := h4.right
  -- Disjunctions on the left can always be decomposed.
  cases h5
  case inl h7 =>
    -- Disjunctions on the left can always be decomposed.
    cases h2
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
    -- Disjunctions on the left can always be decomposed.
    cases h2
    case inl h11 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- True on the right can always be proven directly.
      apply True.intro
    case inr h12 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- True on the right can always be proven directly.
      apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_135994671886152996667744363796 : ((((p1 ∨ False) ∨ (p2 ∧ ((p1 ∧ (p2 ∧ p4)) ∨ p1))) ∨ ((((p3 ∧ ((True ∧ False) ∧ p4)) ∨ False) → p3) ∨ p1)) ∨ ((p1 → p2) ∨ p5)) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
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
    -- Conjunctions on the left can always be decomposed.
    let h5 := h4.left
    let h6 := h4.right
    -- Conjunctions on the left can always be decomposed.
    let h7 := h5.left
    let h8 := h5.right
    -- False on the left can always be used.
    apply False.elim h8
  case inr h9 =>
    -- False on the left can always be used.
    apply False.elim h9



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_115203866066332362326756206629 : (((False ∧ (((p1 ∧ p2) → p5) ∨ ((True ∧ False) ∨ p1))) ∧ ((p4 ∨ (True → (p4 → p2))) → ((False ∧ (p2 → p1)) ∨ p2))) ∨ (p2 → p2)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_305757210319064458499043780241 : (p1 ∨ ((((p2 ∧ ((False ∧ p4) ∧ p3)) ∧ True) ∧ p3) ∨ ((p4 → (((((True ∨ p3) ∨ (False ∧ p2)) ∨ p3) ∧ p4) ∨ True)) ∨ (p4 → p1)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_738748015234365269187699514198 : ((((p2 ∧ p3) ∨ ((p2 ∨ ((p3 ∨ ((False → (p3 ∧ p3)) → (p2 ∧ ((((p5 → p5) → p5) → p1) → p2)))) ∧ True)) ∨ (True ∨ p4))) ∨ p2) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
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
theorem thm_5_vars_152647444033951969473096964036 : (((True → p2) ∧ ((True ∧ p4) ∨ (((p3 → False) ∧ p3) ∧ (((p1 ∨ (p4 ∨ (p1 → True))) ∨ p3) → p2)))) → (((True → p4) → False) → False)) := by
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
    have h8 : (True → p4) := by
      -- Implications on the right can always be decomposed.
      intro h9
      -- One of the premise coincides with the conclusion.
      exact h7
    -- We have shown the premise of h2, we can now drive its conclusion.
    let h10 := h2 h8
    -- False on the left can always be used.
    apply False.elim h10
  case inr h11 =>
    -- Conjunctions on the left can always be decomposed.
    let h12 := h11.left
    let h13 := h11.right
    -- Conjunctions on the left can always be decomposed.
    let h14 := h12.left
    let h15 := h12.right
    -- We want to use the implication h14 based on <expert-advice>. So we show its premise.
    have h16 : p3 := by
      -- One of the premise coincides with the conclusion.
      exact h15
    -- We have shown the premise of h14, we can now drive its conclusion.
    let h17 := h14 h16
    -- False on the left can always be used.
    apply False.elim h17



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_310188199150880052043773678472 : (p2 ∨ (((p1 ∧ p2) ∨ ((p5 ∨ ((p5 ∧ p1) ∧ (p1 → p4))) ∨ True)) ∧ ((p3 ∧ ((p4 ∨ True) ∧ False)) → ((p1 ∨ (False ∨ p2)) ∨ False)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
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
    apply False.elim h5
  case inr h7 =>
    -- False on the left can always be used.
    apply False.elim h5



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_46342726171190259423412188349 : (((((((p2 ∨ ((((False ∧ p3) ∨ p3) ∨ p2) ∨ p1)) ∨ True) ∨ False) ∨ p2) ∨ ((((p4 ∨ p3) ∨ p1) → True) ∧ p2)) ∧ (False → p3)) ∨ p1) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- Implications on the right can always be decomposed.
  intro h1
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_729111948829789686175048908503 : (((((False → True) ∧ p2) → (((False ∨ ((((p4 → True) ∧ ((p5 ∧ p3) ∨ ((p4 → (p5 → p3)) ∨ p5))) ∨ False) ∨ False)) ∨ p2) ∨ p3)) ∨ False) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h3
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_168991156683780514473807198625 : ((p1 → (((p5 ∧ ((False ∧ p2) → (((p4 → p3) ∧ (p4 ∧ False)) ∨ p4))) ∧ p4) ∨ True)) → (p3 → (((p5 ∧ p3) → p1) ∨ (True → p3)))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h3
  -- One of the premise coincides with the conclusion.
  exact h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_322473612197241266507599743064 : (p5 ∨ (((p5 ∧ p1) ∧ (((p4 → (False ∨ p5)) ∨ (((((p4 → p2) ∧ (p4 → p2)) ∨ (p5 ∨ False)) → (p2 → False)) → True)) ∧ True)) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_355422962632572601348277273991 : (p5 → ((((((((False ∨ ((True ∨ (p1 ∨ p5)) ∧ p2)) ∨ p4) ∨ True) → (p5 → p5)) → p1) ∧ (p3 ∨ (p4 ∨ p4))) ∨ p5) ∧ (True → True))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_158550358124740328829099418214 : (((p5 → True) → ((True ∧ (((p1 ∧ True) ∧ (p5 → (True → p3))) ∨ p4)) → ((True ∨ p2) → p2))) ∨ ((p1 ∨ ((p2 → p2) → True)) ∨ p1)) := by
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
theorem thm_5_vars_244535991624153868893111611718 : ((False ∧ p3) ∨ (False ∨ ((p4 → p2) → ((False ∨ p2) ∨ ((p3 ∧ ((p2 → ((p2 ∨ True) ∧ p3)) ∧ (p3 ∨ p4))) → ((False ∨ True) ∨ p5)))))) := by
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
  let h5 := h4.left
  let h6 := h4.right
  -- Disjunctions on the left can always be decomposed.
  cases h6
  case inl h7 =>
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro
  case inr h8 =>
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_476319054671374641962093300540 : ((((((p1 ∧ p1) ∨ (p1 ∨ p4)) ∨ (p3 ∨ (False ∨ p1))) ∨ ((True ∨ (((True → True) → (((p4 ∨ False) ∧ False) ∨ p5)) ∧ p4)) ∨ True)) ∧ True) ∧ True) := by
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
theorem thm_5_vars_149348384404587414280203219012 : (((p3 ∨ p1) → ((p5 ∧ ((False ∨ (True ∨ (True ∧ p1))) ∨ ((p5 ∧ False) → (p1 → (p3 → p5))))) → False)) ∨ (((p3 ∧ p4) → p4) ∧ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- One of the premise coincides with the conclusion.
  exact h3
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_908353441118761575891956861936 : (((((((False → p5) → False) ∧ ((True ∧ p5) ∧ ((p3 ∨ True) ∨ ((True → True) ∨ p1)))) ∧ p2) ∧ (p1 ∨ ((True → (p2 → True)) ∧ p5))) → p4) ∧ True) := by
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
  -- Conjunctions on the left can always be decomposed.
  let h10 := h8.left
  let h11 := h8.right
  -- Disjunctions on the left can always be decomposed.
  cases h9
  case inl h12 =>
    -- Disjunctions on the left can always be decomposed.
    cases h12
    case inl h13 =>
      -- Disjunctions on the left can always be decomposed.
      cases h3
      case inl h14 =>
        -- We want to use the implication h6 based on <expert-advice>. So we show its premise.
        have h15 : (False → p5) := by
          -- Implications on the right can always be decomposed.
          intro h16
          -- False on the left can always be used.
          apply False.elim h16
        -- We have shown the premise of h6, we can now drive its conclusion.
        let h17 := h6 h15
        -- False on the left can always be used.
        apply False.elim h17
      case inr h18 =>
        -- Conjunctions on the left can always be decomposed.
        let h19 := h18.left
        let h20 := h18.right
        -- We want to use the implication h6 based on <expert-advice>. So we show its premise.
        have h21 : (False → p5) := by
          -- Implications on the right can always be decomposed.
          intro h22
          -- False on the left can always be used.
          apply False.elim h22
        -- We have shown the premise of h6, we can now drive its conclusion.
        let h23 := h6 h21
        -- False on the left can always be used.
        apply False.elim h23
    case inr h24 =>
      -- Disjunctions on the left can always be decomposed.
      cases h3
      case inl h25 =>
        -- We want to use the implication h6 based on <expert-advice>. So we show its premise.
        have h26 : (False → p5) := by
          -- Implications on the right can always be decomposed.
          intro h27
          -- False on the left can always be used.
          apply False.elim h27
        -- We have shown the premise of h6, we can now drive its conclusion.
        let h28 := h6 h26
        -- False on the left can always be used.
        apply False.elim h28
      case inr h29 =>
        -- Conjunctions on the left can always be decomposed.
        let h30 := h29.left
        let h31 := h29.right
        -- We want to use the implication h6 based on <expert-advice>. So we show its premise.
        have h32 : (False → p5) := by
          -- Implications on the right can always be decomposed.
          intro h33
          -- False on the left can always be used.
          apply False.elim h33
        -- We have shown the premise of h6, we can now drive its conclusion.
        let h34 := h6 h32
        -- False on the left can always be used.
        apply False.elim h34
  case inr h35 =>
    -- Disjunctions on the left can always be decomposed.
    cases h35
    case inl h36 =>
      -- Disjunctions on the left can always be decomposed.
      cases h3
      case inl h37 =>
        -- We want to use the implication h6 based on <expert-advice>. So we show its premise.
        have h38 : (False → p5) := by
          -- Implications on the right can always be decomposed.
          intro h39
          -- False on the left can always be used.
          apply False.elim h39
        -- We have shown the premise of h6, we can now drive its conclusion.
        let h40 := h6 h38
        -- False on the left can always be used.
        apply False.elim h40
      case inr h41 =>
        -- Conjunctions on the left can always be decomposed.
        let h42 := h41.left
        let h43 := h41.right
        -- We want to use the implication h6 based on <expert-advice>. So we show its premise.
        have h44 : (False → p5) := by
          -- Implications on the right can always be decomposed.
          intro h45
          -- False on the left can always be used.
          apply False.elim h45
        -- We have shown the premise of h6, we can now drive its conclusion.
        let h46 := h6 h44
        -- False on the left can always be used.
        apply False.elim h46
    case inr h47 =>
      -- Disjunctions on the left can always be decomposed.
      cases h3
      case inl h48 =>
        -- We want to use the implication h6 based on <expert-advice>. So we show its premise.
        have h49 : (False → p5) := by
          -- Implications on the right can always be decomposed.
          intro h50
          -- False on the left can always be used.
          apply False.elim h50
        -- We have shown the premise of h6, we can now drive its conclusion.
        let h51 := h6 h49
        -- False on the left can always be used.
        apply False.elim h51
      case inr h52 =>
        -- Conjunctions on the left can always be decomposed.
        let h53 := h52.left
        let h54 := h52.right
        -- We want to use the implication h6 based on <expert-advice>. So we show its premise.
        have h55 : (False → p5) := by
          -- Implications on the right can always be decomposed.
          intro h56
          -- False on the left can always be used.
          apply False.elim h56
        -- We have shown the premise of h6, we can now drive its conclusion.
        let h57 := h6 h55
        -- False on the left can always be used.
        apply False.elim h57
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_670267154824037030195924954497 : ((((((True ∨ p4) ∨ (p2 ∧ True)) → (((p2 ∨ p3) ∧ p4) ∧ ((False → (p4 ∨ (p1 ∨ (False ∧ p5)))) ∨ False))) ∨ (False → (True ∧ p1))) ∨ False) ∧ True) := by
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
  -- True on the right can always be proven directly.
  apply True.intro
  -- False on the left can always be used.
  apply False.elim h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_116840480739171760430953558833 : (((True → p2) ∨ ((p3 → False) ∧ ((p5 → False) → (((((p5 → p2) ∧ (p2 → p3)) ∨ p4) ∨ p3) → (p2 → (p4 ∨ False)))))) ∨ (True ∨ p3)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_697782309485578832704294742126 : ((((p3 → ((p1 ∨ p4) ∧ (True → (((True ∨ p3) ∨ False) ∨ False)))) ∧ (((p5 ∨ p2) ∨ (p4 ∧ (p3 ∨ (p1 → (p5 → p5))))) ∨ p1)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_317703465067525539183339812865 : (p4 ∨ ((((((p1 ∧ (True ∨ (((p2 ∨ (p1 ∧ (p2 → p5))) → p1) ∧ ((p4 ∧ p3) ∨ p5)))) ∨ p1) ∧ False) ∨ p1) ∨ (True ∨ True)) ∨ False)) := by
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
theorem thm_5_vars_179034262324056233289053406976 : (((p5 ∨ True) → ((p3 → (p4 ∧ p4)) → (p4 ∨ ((p4 ∨ p3) ∨ p4)))) ∨ (False → (((True → (((p2 ∧ True) → True) ∧ p4)) ∨ True) → False))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
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



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_348966756602304929217790188563 : (p3 → (p4 ∨ (((p5 ∧ p2) ∨ (((p1 → (False ∧ ((p4 → p5) ∨ ((p5 ∧ False) ∧ ((p3 → (p4 ∧ True)) ∨ False))))) ∨ p3) ∨ True)) ∧ True))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
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
theorem thm_5_vars_65114290926733199168276769090 : ((p2 ∨ (p5 ∨ ((p4 ∧ ((p4 → (p4 ∧ p1)) ∨ False)) ∨ (False ∧ (((False ∧ (p3 ∧ p3)) ∨ p5) ∧ (p4 ∧ (p3 ∨ (p2 ∨ p3)))))))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_254879323572304394925863601021 : ((p4 ∧ True) → (((p5 ∧ p1) ∨ (((((p1 → p5) ∨ p1) ∧ ((p2 ∨ ((p5 ∨ (p4 ∨ p4)) ∨ (p5 ∧ p5))) ∨ p3)) ∧ p4) ∧ p4)) ∨ True)) := by
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
theorem thm_5_vars_116073886820871574405467166685 : ((((p1 → p4) ∧ True) ∧ (p1 ∧ ((p3 ∨ ((((p2 → (p2 ∨ p1)) → p5) ∨ ((p2 ∧ p1) → p3)) ∧ p2)) ∨ (p4 ∨ True)))) ∨ (True ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_309956704220303302196635663202 : (p2 ∨ (((p2 ∨ ((p2 → p2) → ((p2 ∧ ((p5 ∨ p1) ∨ False)) ∨ (p1 ∧ p3)))) ∧ (p3 → True)) → (p2 ∨ (p3 ∨ (p4 ∧ (p3 ∧ True)))))) := by
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
    -- One of the premise coincides with the conclusion.
    exact h4
  case inr h5 =>
    -- We want to use the implication h5 based on <expert-advice>. So we show its premise.
    have h6 : (p2 → p2) := by
      -- Implications on the right can always be decomposed.
      intro h7
      -- One of the premise coincides with the conclusion.
      exact h7
    -- We have shown the premise of h5, we can now drive its conclusion.
    let h8 := h5 h6
    -- Disjunctions on the left can always be decomposed.
    cases h8
    case inl h9 =>
      -- Conjunctions on the left can always be decomposed.
      let h10 := h9.left
      let h11 := h9.right
      -- Disjunctions on the left can always be decomposed.
      cases h11
      case inl h12 =>
        -- Disjunctions on the left can always be decomposed.
        cases h12
        case inl h13 =>
          -- Show the left disjunct based on <expert-advice>.
          apply Or.inl
          -- One of the premise coincides with the conclusion.
          exact h10
        case inr h14 =>
          -- Show the left disjunct based on <expert-advice>.
          apply Or.inl
          -- One of the premise coincides with the conclusion.
          exact h10
      case inr h15 =>
        -- False on the left can always be used.
        apply False.elim h15
    case inr h16 =>
      -- Conjunctions on the left can always be decomposed.
      let h17 := h16.left
      let h18 := h16.right
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- One of the premise coincides with the conclusion.
      exact h18



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_26976407489913947429455986923 : (((p4 ∨ p5) ∨ (p2 ∨ (p5 ∨ ((p4 ∨ (((True → ((p1 ∨ p3) ∧ False)) → (p3 → (p1 ∧ (p2 → p1)))) → True)) ∨ (p2 ∧ p3))))) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
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
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_228452715307720057237474157397 : ((False ∨ (p2 ∨ False)) ∨ ((p1 ∨ False) ∨ (p5 → (p2 ∨ ((p3 ∧ False) → (((p3 ∨ (True → (p1 ∨ (True → (True ∧ p3))))) ∧ p2) ∧ False)))))) := by
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
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Conjunctions on the left can always be decomposed.
  let h3 := h2.left
  let h4 := h2.right
  -- False on the left can always be used.
  apply False.elim h4
  -- Conjunctions on the left can always be decomposed.
  let h5 := h2.left
  let h6 := h2.right
  -- False on the left can always be used.
  apply False.elim h6
  -- Conjunctions on the left can always be decomposed.
  let h7 := h2.left
  let h8 := h2.right
  -- False on the left can always be used.
  apply False.elim h8



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_53478233844045274387236036812 : (((p1 ∧ ((True → ((p2 ∧ p4) ∧ p5)) → ((p1 ∨ True) → p5))) → (((False ∨ p2) ∧ p3) ∧ (((False ∨ False) ∧ (p1 → p1)) ∨ False))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_755246830669781044197956360980 : (((False ∧ (p5 → ((((p2 ∨ (p2 ∨ False)) ∨ ((p3 → False) → (p5 ∧ ((p4 → p2) ∨ ((p4 → p5) ∧ True))))) → p4) ∧ (p4 ∧ p3)))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_113780616945767901479476719172 : ((((False ∧ (p5 ∨ True)) ∨ ((((p1 ∨ p5) ∧ (p4 → p2)) ∨ ((True ∧ p1) ∨ (p5 → False))) → (p4 ∨ False))) → (p2 → p2)) ∨ (False → p5)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_725257158043695195249011629242 : ((((p3 → (False ∧ False)) ∧ (((True ∨ (((p2 ∧ (p5 ∧ False)) ∨ (p1 ∨ ((p2 → p2) → p3))) ∨ (p4 → (p4 ∧ True)))) ∧ True) → p2)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_49563754901566611358368168484 : (((((((p4 ∧ ((p2 ∨ p2) → (p3 ∧ p1))) ∧ (p3 ∨ p3)) ∨ p4) ∨ (p3 → p5)) → ((p1 → p1) ∨ p3)) → (p5 → (p5 ∧ True))) ∨ p2) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- One of the premise coincides with the conclusion.
  exact h2
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_673764651740423798055906144124 : (((((p5 → p5) ∧ ((True ∧ (((p2 ∧ p3) ∧ (False ∧ (p3 → p3))) ∧ (p1 ∧ p3))) → (p1 → (p2 ∧ p2)))) → ((True ∧ p5) ∨ p2)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_166077026596312035728358134352 : (((p1 ∨ p2) → (((p2 ∧ p5) ∧ (p2 ∧ ((p1 ∧ False) ∨ False))) ∨ ((p2 ∧ False) → p5))) ∨ ((p2 → ((p1 ∨ (p3 → True)) → p4)) → p2)) := by
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
    -- Conjunctions on the left can always be decomposed.
    let h4 := h3.left
    let h5 := h3.right
    -- False on the left can always be used.
    apply False.elim h5
  case inr h6 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h7
    -- Conjunctions on the left can always be decomposed.
    let h8 := h7.left
    let h9 := h7.right
    -- False on the left can always be used.
    apply False.elim h9



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_177857321429419449550616190618 : (((((((p2 ∧ p5) ∨ p5) ∧ (p4 ∨ p3)) ∧ (False ∧ p1)) ∨ p1) ∨ p1) ∨ (True ∨ ((p4 ∨ (p5 → ((p4 ∨ (p1 ∧ p4)) ∨ p3))) → p2))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_308836347933600648979483615468 : (p2 ∨ (((((((((p4 ∧ (p5 ∧ p2)) → p2) ∨ (True ∧ p1)) → False) ∧ True) ∧ (False ∧ (((p3 ∧ p4) ∨ p1) ∨ p1))) ∨ True) → False) → False)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h2 : (((((((p4 ∧ (p5 ∧ p2)) → p2) ∨ (True ∧ p1)) → False) ∧ True) ∧ (False ∧ (((p3 ∧ p4) ∨ p1) ∨ p1))) ∨ True) := by
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h3 := h1 h2
  -- False on the left can always be used.
  apply False.elim h3



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_616238695011755309164619647195 : (((((((((False ∧ p2) ∧ False) ∨ (p2 ∧ (False → p4))) ∨ p3) ∧ False) ∨ (((p1 ∧ (((p4 → True) ∨ p1) ∨ False)) ∨ False) ∧ p5)) ∨ True) ∨ p3) ∧ True) := by
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
theorem thm_5_vars_46716274389561981972628866507 : (((p5 ∨ ((((p3 ∧ ((p1 ∧ p2) → ((True ∨ p5) ∧ (False ∨ False)))) ∨ p1) ∨ True) ∨ (p2 ∨ (p1 → (p5 ∧ p1))))) ∧ (True ∨ p1)) ∨ p4) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_38470143216332791102728034145 : ((((p3 → (p3 → (((p2 ∨ p2) ∨ p2) → ((p4 ∨ (p1 → True)) ∨ p2)))) → (p2 ∨ (((True → p4) ∨ False) ∨ (p1 ∧ p1)))) ∧ p2) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_47066963063907321222061022229 : (((((p4 ∧ p2) ∧ ((p3 → p3) → ((p4 ∨ True) ∧ ((p5 ∧ (p2 ∧ (p2 ∨ False))) → (True ∧ p3))))) ∨ (p4 → p1)) ∨ (p2 ∧ p4)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_114963657241984700572737223201 : (((p5 ∨ (p4 ∨ (True ∨ (p1 ∧ (p1 ∨ (((True ∨ True) → p1) → False)))))) → ((p2 ∨ True) ∨ (((p5 ∨ False) → p4) ∨ True))) ∨ (p5 ∨ p4)) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h2 =>
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro
  case inr h3 =>
    -- Disjunctions on the left can always be decomposed.
    cases h3
    case inl h4 =>
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- True on the right can always be proven directly.
      apply True.intro
    case inr h5 =>
      -- Disjunctions on the left can always be decomposed.
      cases h5
      case inl h6 =>
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
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
          -- Show the left disjunct based on <expert-advice>.
          apply Or.inl
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- True on the right can always be proven directly.
          apply True.intro
        case inr h11 =>
          -- Show the left disjunct based on <expert-advice>.
          apply Or.inl
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- True on the right can always be proven directly.
          apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_183845505637994443184219251722 : ((((((p2 ∨ p3) ∧ p4) → (False ∨ p2)) ∨ (p3 ∨ True)) ∧ p3) ∨ (((False ∧ (p1 ∨ (False ∧ p5))) ∨ (p5 ∧ False)) → ((p3 ∨ p5) ∧ True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h2 =>
    -- Conjunctions on the left can always be decomposed.
    let h3 := h2.left
    let h4 := h2.right
    -- False on the left can always be used.
    apply False.elim h3
  case inr h5 =>
    -- Conjunctions on the left can always be decomposed.
    let h6 := h5.left
    let h7 := h5.right
    -- False on the left can always be used.
    apply False.elim h7
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_225648257894056140545772944166 : (((p2 → False) ∧ p2) ∨ (((((p2 → p1) → (p3 ∧ False)) ∨ p3) ∧ True) ∨ (True ∨ ((((p3 ∨ p4) ∨ p1) ∧ (p4 ∧ p1)) → (p4 ∨ p4))))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_327054305345197728314515131563 : (True → (((((p5 → False) ∧ (p2 ∨ p2)) ∧ False) ∨ ((p5 ∨ (p1 ∨ ((p2 → ((p4 → p3) ∨ p2)) ∧ (True ∧ (p2 ∨ True))))) ∨ p2)) ∨ True)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_117626156801542306644336134266 : ((p3 ∧ ((p2 → ((p4 → (((p1 → ((p5 ∨ p5) ∧ False)) → p1) ∧ False)) → ((p4 ∨ (p5 → p3)) ∧ (p3 ∧ p4)))) ∧ p3)) ∨ (p3 → True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_317623794549132531968578154350 : (p4 ∨ ((((((p3 → (((p4 ∧ (p1 ∧ ((p3 ∧ (p1 → (p1 → False))) → p2))) → False) ∨ True)) ∧ p5) ∨ False) ∧ (p2 → p3)) ∨ True) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_191471886173430545792882654449 : ((True ∧ (((False ∧ p2) ∨ ((p5 ∨ True) ∧ p4)) ∨ p5)) ∨ ((True ∧ ((p1 ∧ ((p2 ∧ p3) → (p1 ∨ p3))) → ((False ∧ p4) → p4))) ∨ False)) := by
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
  -- Implications on the right can always be decomposed.
  intro h2
  -- Conjunctions on the left can always be decomposed.
  let h3 := h2.left
  let h4 := h2.right
  -- False on the left can always be used.
  apply False.elim h3



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_148644256080432179712681621612 : (((((p3 ∧ ((p2 → p1) ∧ p5)) ∨ p2) → p4) ∧ ((((p1 ∧ p5) ∧ p3) ∧ (True ∧ (False → p3))) ∧ p3)) ∨ ((p1 → p1) ∨ (False ∨ p5))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_258160885504991996217419658658 : ((p4 ∨ p4) → ((((p3 ∨ (True ∨ p4)) → (p5 → ((p5 ∧ (p5 ∧ False)) ∧ (((p5 ∨ (p1 → (True ∨ p3))) ∨ True) ∨ True)))) ∧ p5) → False)) := by
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
    -- We want to use the implication h3 based on <expert-advice>. So we show its premise.
    have h6 : (p3 ∨ (True ∨ p4)) := by
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- True on the right can always be proven directly.
      apply True.intro
    -- We have shown the premise of h3, we can now drive its conclusion.
    let h7 := h3 h6
    -- We want to use the implication h7 based on <expert-advice>. So we show its premise.
    have h8 : p5 := by
      -- One of the premise coincides with the conclusion.
      exact h4
    -- We have shown the premise of h7, we can now drive its conclusion.
    let h9 := h7 h8
    -- We need to get the left conjuct of h9 based on <expert-advice>.
    let h10 := h9.left
    -- We need to get the right conjuct of h10 based on <expert-advice>.
    let h11 := h10.right
    -- We need to get the right conjuct of h11 based on <expert-advice>.
    let h12 := h11.right
    -- False on the left can always be used.
    apply False.elim h12
  case inr h13 =>
    -- We want to use the implication h3 based on <expert-advice>. So we show its premise.
    have h14 : (p3 ∨ (True ∨ p4)) := by
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- True on the right can always be proven directly.
      apply True.intro
    -- We have shown the premise of h3, we can now drive its conclusion.
    let h15 := h3 h14
    -- We want to use the implication h15 based on <expert-advice>. So we show its premise.
    have h16 : p5 := by
      -- One of the premise coincides with the conclusion.
      exact h4
    -- We have shown the premise of h15, we can now drive its conclusion.
    let h17 := h15 h16
    -- We need to get the left conjuct of h17 based on <expert-advice>.
    let h18 := h17.left
    -- We need to get the right conjuct of h18 based on <expert-advice>.
    let h19 := h18.right
    -- We need to get the right conjuct of h19 based on <expert-advice>.
    let h20 := h19.right
    -- False on the left can always be used.
    apply False.elim h20



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_615885259514218727181554491393 : ((((((False → False) → ((p1 ∨ ((((p4 ∨ p4) ∨ p2) ∨ True) → p1)) ∧ p2)) ∨ ((True ∧ (False ∨ (p5 ∨ (p3 → p3)))) ∨ p2)) ∨ p1) ∨ p5) ∧ True) := by
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
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- One of the premise coincides with the conclusion.
  exact h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_788753155972846702547754768476 : (((p5 ∨ (((True ∨ p5) → (p1 ∨ ((True ∧ ((True ∧ ((p2 → (p1 ∧ ((p3 ∧ (False → p4)) ∧ p5))) → False)) → False)) ∨ p3))) → p1)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_62457961709216544166097569363 : ((p3 ∧ ((p5 ∧ p4) ∧ (p4 ∧ (p1 ∧ (((True ∨ ((((False → p2) ∨ False) → (p5 ∧ p4)) ∧ (p4 → p5))) ∧ p4) → (True ∧ p2)))))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_262221346871702900827864601743 : (True ∧ (((((p2 → False) ∧ False) ∧ ((((((p3 ∧ p3) → False) ∧ p1) → p3) ∧ (p3 → p3)) ∨ ((p4 ∧ p2) → False))) ∧ (p4 → p1)) ∨ True)) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_125111953353693100526776905719 : (((p5 → (p2 ∧ False)) ∧ ((((p4 → (p4 ∨ p5)) ∧ (p3 ∨ ((True ∧ p2) → ((p4 ∨ p4) → (p2 ∧ p1))))) → p4) ∨ True)) → (p5 → p4)) := by
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
    -- We want to use the implication h3 based on <expert-advice>. So we show its premise.
    have h6 : p5 := by
      -- One of the premise coincides with the conclusion.
      exact h2
    -- We have shown the premise of h3, we can now drive its conclusion.
    let h7 := h3 h6
    -- We need to get the right conjuct of h7 based on <expert-advice>.
    let h8 := h7.right
    -- False on the left can always be used.
    apply False.elim h8
  case inr h9 =>
    -- We want to use the implication h3 based on <expert-advice>. So we show its premise.
    have h10 : p5 := by
      -- One of the premise coincides with the conclusion.
      exact h2
    -- We have shown the premise of h3, we can now drive its conclusion.
    let h11 := h3 h10
    -- We need to get the right conjuct of h11 based on <expert-advice>.
    let h12 := h11.right
    -- False on the left can always be used.
    apply False.elim h12



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_166111492098510812134879805375 : (((p5 → p1) → (((p5 → ((p1 ∨ p5) ∨ ((True ∨ True) ∨ p4))) ∨ (p3 ∨ False)) → p3)) ∨ (True → (((False → (p2 → True)) ∨ p4) ∨ True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_41954011878911593158071912594 : ((((p2 ∧ p5) ∧ (p3 ∨ ((((True ∨ ((p4 ∨ p2) → True)) → (True ∨ p5)) ∧ (p5 ∨ (p2 → p2))) ∧ (False ∧ (p3 ∧ False))))) ∨ p4) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_137950487997917288782934189160 : ((p5 ∨ (((p3 → (p4 ∧ p5)) ∧ (p2 ∧ (((p3 ∨ (p4 ∨ ((True → (False ∧ p5)) → p2))) → p5) ∧ p1))) ∨ p3)) ∨ (p3 ∨ (False → p4))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_345365074025759398308593765426 : (p3 → ((((p5 → (((p4 → ((True ∨ p2) ∨ p3)) → (((((p4 ∨ p3) → p2) ∨ p1) → p4) → p4)) → p5)) → (p1 ∨ p5)) ∨ p2) ∨ p3)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_64688968343283129155458577982 : ((p1 ∨ (p5 ∨ (((p1 ∨ ((p4 ∨ (False ∨ p1)) ∨ p4)) ∨ False) ∧ ((((p1 ∧ ((p5 → True) → False)) ∧ (p3 ∧ False)) → p5) → p2)))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_98815716592533365525635290611 : ((True → (((p4 ∧ ((True → p1) ∨ p1)) ∨ (((p3 ∨ p1) ∨ ((p4 ∧ ((((False ∨ p4) → p5) ∨ p4) ∨ True)) ∧ p5)) ∧ p3)) ∧ False)) → p1) := by
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
theorem thm_5_vars_174262517677889152090329925986 : ((((((True ∧ (p2 ∧ p4)) ∧ (p2 → p3)) ∨ True) → p1) ∧ ((True ∨ False) ∧ True)) → (True → ((False ∧ p4) ∨ ((p2 ∧ p2) ∨ (p3 ∨ True))))) := by
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
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro
  case inr h8 =>
    -- False on the left can always be used.
    apply False.elim h8



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_149673149229423744527470695387 : ((p5 ∧ (((p4 ∧ (p4 ∨ ((False → (False ∨ (((True ∧ p3) ∧ True) ∨ p2))) ∧ p2))) ∧ (False ∧ True)) ∧ p2)) ∨ (((True ∨ p4) ∨ p1) ∧ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_187123547382861872846714053022 : (((True ∨ p2) ∨ ((p2 ∨ p4) ∧ (p1 ∨ ((p2 → p2) ∨ False)))) → (p2 ∨ ((False ∨ (((False → False) → ((p1 → p3) ∧ p3)) ∧ p5)) → p3))) := by
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
      -- Disjunctions on the left can always be decomposed.
      cases h4
      case inl h5 =>
        -- False on the left can always be used.
        apply False.elim h5
      case inr h6 =>
        -- Conjunctions on the left can always be decomposed.
        let h7 := h6.left
        let h8 := h6.right
        -- We want to use the implication h7 based on <expert-advice>. So we show its premise.
        have h9 : (False → False) := by
          -- Implications on the right can always be decomposed.
          intro h10
          -- False on the left can always be used.
          apply False.elim h10
        -- We have shown the premise of h7, we can now drive its conclusion.
        let h11 := h7 h9
        -- We need to get the right conjuct of h11 based on <expert-advice>.
        let h12 := h11.right
        -- One of the premise coincides with the conclusion.
        exact h12
    case inr h13 =>
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- One of the premise coincides with the conclusion.
      exact h13
  case inr h14 =>
    -- Conjunctions on the left can always be decomposed.
    let h15 := h14.left
    let h16 := h14.right
    -- Disjunctions on the left can always be decomposed.
    cases h15
    case inl h17 =>
      -- Disjunctions on the left can always be decomposed.
      cases h16
      case inl h18 =>
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- One of the premise coincides with the conclusion.
        exact h17
      case inr h19 =>
        -- Disjunctions on the left can always be decomposed.
        cases h19
        case inl h20 =>
          -- Show the left disjunct based on <expert-advice>.
          apply Or.inl
          -- One of the premise coincides with the conclusion.
          exact h17
        case inr h21 =>
          -- False on the left can always be used.
          apply False.elim h21
    case inr h22 =>
      -- Disjunctions on the left can always be decomposed.
      cases h16
      case inl h23 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- Implications on the right can always be decomposed.
        intro h24
        -- Disjunctions on the left can always be decomposed.
        cases h24
        case inl h25 =>
          -- False on the left can always be used.
          apply False.elim h25
        case inr h26 =>
          -- Conjunctions on the left can always be decomposed.
          let h27 := h26.left
          let h28 := h26.right
          -- We want to use the implication h27 based on <expert-advice>. So we show its premise.
          have h29 : (False → False) := by
            -- Implications on the right can always be decomposed.
            intro h30
            -- False on the left can always be used.
            apply False.elim h30
          -- We have shown the premise of h27, we can now drive its conclusion.
          let h31 := h27 h29
          -- We need to get the right conjuct of h31 based on <expert-advice>.
          let h32 := h31.right
          -- One of the premise coincides with the conclusion.
          exact h32
      case inr h33 =>
        -- Disjunctions on the left can always be decomposed.
        cases h33
        case inl h34 =>
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- Implications on the right can always be decomposed.
          intro h35
          -- Disjunctions on the left can always be decomposed.
          cases h35
          case inl h36 =>
            -- False on the left can always be used.
            apply False.elim h36
          case inr h37 =>
            -- Conjunctions on the left can always be decomposed.
            let h38 := h37.left
            let h39 := h37.right
            -- We want to use the implication h38 based on <expert-advice>. So we show its premise.
            have h40 : (False → False) := by
              -- Implications on the right can always be decomposed.
              intro h41
              -- False on the left can always be used.
              apply False.elim h41
            -- We have shown the premise of h38, we can now drive its conclusion.
            let h42 := h38 h40
            -- We need to get the right conjuct of h42 based on <expert-advice>.
            let h43 := h42.right
            -- One of the premise coincides with the conclusion.
            exact h43
        case inr h44 =>
          -- False on the left can always be used.
          apply False.elim h44



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_53374807608725309726591355931 : (((((p2 ∧ ((((p5 → p5) ∨ p1) ∧ p5) → p1)) ∨ p2) → p1) → (((((p5 → False) ∨ p2) → ((p4 ∧ p5) ∨ False)) → True) ∧ p2)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_673731570490537872723508746669 : (((((p4 ∨ p5) ∧ ((p4 ∧ True) ∨ (((p1 → ((False → (True ∨ (True ∧ p3))) → p4)) ∧ p5) → (p3 ∨ True)))) → ((p1 ∧ p1) ∨ True)) ∨ p3) ∧ True) := by
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
    -- Disjunctions on the left can always be decomposed.
    cases h3
    case inl h5 =>
      -- Conjunctions on the left can always be decomposed.
      let h6 := h5.left
      let h7 := h5.right
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- True on the right can always be proven directly.
      apply True.intro
    case inr h8 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- True on the right can always be proven directly.
      apply True.intro
  case inr h9 =>
    -- Disjunctions on the left can always be decomposed.
    cases h3
    case inl h10 =>
      -- Conjunctions on the left can always be decomposed.
      let h11 := h10.left
      let h12 := h10.right
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- True on the right can always be proven directly.
      apply True.intro
    case inr h13 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- True on the right can always be proven directly.
      apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_154940777672698191000217179697 : (((p5 ∨ ((p5 ∧ (p5 ∨ p5)) ∨ (True ∨ ((p1 → (p3 ∧ p4)) ∨ p4)))) ∨ (p5 ∧ (False ∨ p4))) ∧ (p2 ∨ (True ∨ ((p2 ∧ p2) ∨ p5)))) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
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
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_40732578365710013819160907140 : ((((((p4 ∨ p4) → (p5 → p4)) ∨ ((p2 → ((((p1 → p2) ∧ (p3 → (p3 ∧ p1))) ∨ (p3 ∧ p5)) → True)) → p1)) → False) ∨ True) ∨ False) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_228138833520132965373024779327 : ((p4 ∧ (p2 → p1)) ∨ (p1 → ((((p5 ∧ p5) ∧ ((p1 ∨ (p5 ∧ p4)) ∨ p4)) → False) ∨ ((p4 ∨ ((p1 → p5) → (p3 ∧ p5))) ∨ True)))) := by
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



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_135345137499608147499667875820 : (((True ∧ (p5 ∨ (((((True ∧ p5) ∨ p5) ∨ ((p4 ∨ p4) ∧ p3)) → (p1 ∧ p1)) → p4))) ∧ ((p5 ∧ True) ∨ p2)) ∨ ((False → p5) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_152596056846139504599206061520 : (((p1 ∧ p5) ∧ (True ∨ ((p3 ∧ (True ∧ (False → (p2 → p1)))) ∧ (True ∨ (True ∨ (p3 → (True ∧ p5))))))) → (p5 ∧ ((p3 ∧ p4) ∨ p5))) := by
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
  -- Disjunctions on the left can always be decomposed.
  cases h3
  case inl h6 =>
    -- One of the premise coincides with the conclusion.
    exact h5
  case inr h7 =>
    -- Conjunctions on the left can always be decomposed.
    let h8 := h7.left
    let h9 := h7.right
    -- Conjunctions on the left can always be decomposed.
    let h10 := h8.left
    let h11 := h8.right
    -- Conjunctions on the left can always be decomposed.
    let h12 := h11.left
    let h13 := h11.right
    -- Disjunctions on the left can always be decomposed.
    cases h9
    case inl h14 =>
      -- One of the premise coincides with the conclusion.
      exact h5
    case inr h15 =>
      -- Disjunctions on the left can always be decomposed.
      cases h15
      case inl h16 =>
        -- One of the premise coincides with the conclusion.
        exact h5
      case inr h17 =>
        -- One of the premise coincides with the conclusion.
        exact h5
  -- Conjunctions on the left can always be decomposed.
  let h18 := h1.left
  let h19 := h1.right
  -- Conjunctions on the left can always be decomposed.
  let h20 := h18.left
  let h21 := h18.right
  -- Disjunctions on the left can always be decomposed.
  cases h19
  case inl h22 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h21
  case inr h23 =>
    -- Conjunctions on the left can always be decomposed.
    let h24 := h23.left
    let h25 := h23.right
    -- Conjunctions on the left can always be decomposed.
    let h26 := h24.left
    let h27 := h24.right
    -- Conjunctions on the left can always be decomposed.
    let h28 := h27.left
    let h29 := h27.right
    -- Disjunctions on the left can always be decomposed.
    cases h25
    case inl h30 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- One of the premise coincides with the conclusion.
      exact h21
    case inr h31 =>
      -- Disjunctions on the left can always be decomposed.
      cases h31
      case inl h32 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- One of the premise coincides with the conclusion.
        exact h21
      case inr h33 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- One of the premise coincides with the conclusion.
        exact h21



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_148457199443004308236002823934 : ((((p2 ∧ ((p2 ∨ p3) → (p2 ∧ (False ∨ False)))) → (p4 ∧ False)) ∧ (p3 → ((p2 → p2) → (p2 ∧ p4)))) ∨ (False → ((True ∧ p3) ∧ p5))) := by
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
theorem thm_5_vars_162540460643377297080747776646 : ((((((True → ((((True ∧ p1) ∨ p5) ∧ p2) → (p3 → p4))) ∧ p5) ∧ p1) ∧ p4) → p1) ∧ ((p4 → (p1 ∧ (p1 ∧ p2))) ∨ (p2 → p2))) := by
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
  -- One of the premise coincides with the conclusion.
  exact h5
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h8
  -- One of the premise coincides with the conclusion.
  exact h8



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_799507300825545385287592075943 : (((p1 → (p2 ∨ (False ∧ (((False → (False → (p2 ∧ (p5 ∧ p2)))) ∧ ((p2 ∨ (True ∧ ((p5 ∨ False) ∨ p4))) ∨ p5)) → (p2 ∨ p5))))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_46376071763692519586854783975 : ((((p5 ∨ ((p3 ∧ False) → ((False ∨ (False → p3)) ∨ (p5 ∧ p5)))) → ((p4 ∧ ((p5 → False) → (p2 ∨ p2))) → p1)) ∧ (p2 ∧ True)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_53849877799651348771312585734 : (((((p3 ∧ p4) ∨ p4) ∧ ((p4 ∧ p1) ∧ (p2 → p4))) ∨ ((((True ∧ p3) → True) → (True ∨ (((p2 ∧ p2) → p1) → p5))) ∧ True)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_199737780620659146336050357110 : (((p2 ∨ ((p5 ∧ p1) ∨ (True → True))) → p3) → (((p4 ∧ ((((p2 ∨ p2) ∨ False) ∨ (p2 ∧ p4)) ∨ (p4 ∨ p5))) → p1) ∨ (p3 ∨ p3))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h2 : (p2 ∨ ((p5 ∧ p1) ∨ (True → True))) := by
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
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
theorem thm_5_vars_797848229425948800864493581055 : (((p1 → (((((False ∨ ((p5 ∨ p1) ∨ (False ∨ p2))) ∧ ((True ∧ p3) ∨ ((p5 ∨ (p1 → p4)) → False))) → p3) ∨ p2) ∨ (True → p1))) ∨ p4) ∧ True) := by
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
  exact h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_104686734591165086158998418126 : (((p5 ∨ (((p3 ∨ (((((p1 ∨ (p4 ∨ p2)) ∨ True) → True) → True) ∧ ((True → p4) → False))) → p5) ∨ True)) ∨ (p1 ∧ p4)) ∧ (p4 → p4)) := by
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
  -- Implications on the right can always be decomposed.
  intro h1
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_662526018363252182293260993 : ((((((True → ((True ∧ (p1 ∨ (True → p3))) ∨ False)) ∨ p5) → (False ∨ True)) → (p5 ∨ p2)) ∨ (((p3 ∨ p2) ∧ p3) → True)) ∨ p4) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_149785368621161670399875184900 : ((False ∨ (((True → ((p2 ∨ (True ∧ (p2 → (p5 → False)))) → p5)) ∨ p3) ∨ ((p1 → (p1 ∨ p2)) ∧ p4))) ∨ (False → ((p4 ∧ p2) ∨ True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- False on the left can always be used.
  apply False.elim h1



