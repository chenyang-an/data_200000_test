variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_27163422830143273817549355537 : (((p2 → p4) ∨ (((((True → p2) → (p2 ∧ False)) ∧ ((p3 → ((p4 ∨ ((True ∧ p4) → False)) → False)) ∧ p3)) ∨ (p1 ∨ True)) ∨ p1)) ∧ True) := by
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
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_157879259321096824340334240153 : (((((True ∧ (p1 → p3)) ∧ p4) ∨ ((p1 → False) ∨ p4)) ∨ ((p4 ∨ ((p2 → True) → p1)) ∧ p2)) ∨ (p4 → ((p2 → p2) → (True ∧ p4)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_37707268361252306131852683510 : (((((False ∧ (((p2 → p5) ∧ (p5 → (((p4 ∧ (p5 → p5)) ∧ p2) → (False → p1)))) → p4)) → (True ∧ (p5 → p3))) → p1) ∧ p2) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_680923865628578072534507652290 : (((((True → p3) ∧ (p1 → ((p4 → (p4 ∨ p5)) → ((p2 ∧ p2) ∧ ((p2 ∨ p1) ∨ (p3 → p1)))))) → (((p1 → p4) ∧ p4) ∨ True)) ∨ p4) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
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
theorem thm_5_vars_115189558216936945493790990420 : (((((p4 ∨ (True ∧ p2)) ∧ p4) → ((p4 ∨ p3) → p4)) ∧ (((p1 ∧ (p2 ∨ (p1 → p4))) ∨ (p5 ∧ p1)) ∨ (False ∨ p4))) ∨ (p5 → True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_936164585462992618366173945454 : ((((p3 ∨ ((p5 → (p3 → (p5 → p5))) ∨ p4)) → (((p5 ∧ True) → ((((p1 ∨ True) ∧ p2) ∨ p5) ∧ p3)) ∧ (p3 ∧ (p1 ∧ True)))) → p3) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h1
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h2 : (p3 ∨ ((p5 → (p3 → (p5 → p5))) ∨ p4)) := by
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Implications on the right can always be decomposed.
    intro h3
    -- Implications on the right can always be decomposed.
    intro h4
    -- Implications on the right can always be decomposed.
    intro h5
    -- One of the premise coincides with the conclusion.
    exact h3
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h6 := h1 h2
  -- We need to get the right conjuct of h6 based on <expert-advice>.
  let h7 := h6.right
  -- We need to get the left conjuct of h7 based on <expert-advice>.
  let h8 := h7.left
  -- One of the premise coincides with the conclusion.
  exact h8
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_148036883219028111291304330068 : ((((p1 ∧ p4) ∨ (False ∧ (p4 ∨ (p4 → (p1 → (((p2 ∨ p1) ∨ p1) ∨ (False ∧ p3))))))) ∨ (p1 → True)) ∨ (False ∧ ((p2 ∨ p3) → p2))) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_305606572352727212781484803831 : (p1 ∨ (((((p2 → (p2 ∨ p5)) ∨ p5) ∨ (p2 → (p1 ∧ False))) ∧ p3) → (((((p3 ∧ p4) → p5) ∨ (p3 ∧ (False ∧ p5))) ∨ p5) ∨ p3))) := by
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
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- One of the premise coincides with the conclusion.
      exact h3
    case inr h6 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- One of the premise coincides with the conclusion.
      exact h3
  case inr h7 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h3



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_166271710512973267484292369494 : ((p3 ∧ (p3 ∨ ((p1 ∧ p4) → ((((p5 ∨ p4) → (False ∧ (False ∨ False))) → p3) ∧ False)))) ∨ ((((True ∨ (True → True)) → p1) ∨ False) → p1)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h2 =>
    -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
    have h3 : (True ∨ (True → True)) := by
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- True on the right can always be proven directly.
      apply True.intro
    -- We have shown the premise of h2, we can now drive its conclusion.
    let h4 := h2 h3
    -- One of the premise coincides with the conclusion.
    exact h4
  case inr h5 =>
    -- False on the left can always be used.
    apply False.elim h5



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_775445056863661691210989059698 : (((False ∨ (p3 ∧ (((True → ((p1 ∨ p2) → (p4 ∨ (p4 → (p2 ∨ (p2 ∧ False)))))) ∧ (p1 ∧ (((p5 → p3) → p3) ∨ p5))) → p5))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_314527510054622486352279418541 : (p3 ∨ ((True → (True → (((p5 → (((False ∧ p1) ∧ False) ∨ p2)) ∨ ((p2 ∧ True) → p1)) ∨ True))) ∧ (p5 → (False → (p5 → (p5 ∨ True)))))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- Implications on the right can always be decomposed.
  intro h3
  -- Implications on the right can always be decomposed.
  intro h4
  -- Implications on the right can always be decomposed.
  intro h5
  -- False on the left can always be used.
  apply False.elim h4



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_183094508083456302428662750396 : (((True ∨ p1) → (False ∨ ((p2 ∧ False) ∨ (True ∨ (p1 → p5))))) ∧ (p2 ∨ (p3 ∨ (p1 → ((p5 ∨ (p3 → p2)) → (p2 → (p3 → p2))))))) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h1
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h2 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- True on the right can always be proven directly.
    apply True.intro
  case inr h3 =>
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
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h4
  -- Implications on the right can always be decomposed.
  intro h5
  -- Implications on the right can always be decomposed.
  intro h6
  -- Implications on the right can always be decomposed.
  intro h7
  -- Disjunctions on the left can always be decomposed.
  cases h5
  case inl h8 =>
    -- One of the premise coincides with the conclusion.
    exact h6
  case inr h9 =>
    -- One of the premise coincides with the conclusion.
    exact h6



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_52047767587323220480160035433 : (((p1 → (((((p3 ∧ p5) → False) ∧ p2) ∨ False) → (((False ∧ p5) ∧ p4) ∨ p3))) ∨ (p3 ∧ (p3 ∧ (p4 ∨ (p3 ∧ (p4 ∨ p3)))))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_322421284635830701481149864041 : (p5 ∨ (((((p2 ∧ p5) ∨ (True ∧ (True ∧ False))) ∧ p4) ∨ (((((p2 ∧ True) ∧ (p4 ∧ p5)) ∧ False) ∧ (p3 ∧ (True ∨ p1))) → p1)) ∨ p5)) := by
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
  -- Conjunctions on the left can always be decomposed.
  let h4 := h2.left
  let h5 := h2.right
  -- Conjunctions on the left can always be decomposed.
  let h6 := h4.left
  let h7 := h4.right
  -- Conjunctions on the left can always be decomposed.
  let h8 := h6.left
  let h9 := h6.right
  -- Conjunctions on the left can always be decomposed.
  let h10 := h7.left
  let h11 := h7.right
  -- False on the left can always be used.
  apply False.elim h5



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_200855797106185012929108443852 : ((True ∨ (False ∧ (((True ∧ p1) → p1) ∧ p2))) → (((((p3 ∧ (p5 ∧ p5)) ∨ (p3 ∧ (p4 ∧ False))) ∨ (p1 ∨ True)) ∨ p5) ∨ (False ∨ p1))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h2 =>
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
  case inr h3 =>
    -- Conjunctions on the left can always be decomposed.
    let h4 := h3.left
    let h5 := h3.right
    -- False on the left can always be used.
    apply False.elim h4



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_63050420439475760566873915261 : ((p5 ∧ (((p2 ∨ ((p3 ∧ (p5 → ((p1 → p4) → p2))) → p5)) ∨ (((True ∧ True) ∨ True) → ((p1 ∨ (p2 ∧ False)) → p4))) ∧ True)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_113562555432428834568386067030 : ((((p5 ∧ p1) ∨ (((p4 ∨ p4) → (p5 ∧ (p1 ∨ p3))) ∧ (False ∨ ((((p4 → True) ∨ p3) ∧ p5) ∧ p4)))) ∨ (p5 ∨ True)) ∨ (True ∧ p1)) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_304064160172336509898291763945 : (p1 ∨ ((p1 ∨ ((((False → (p3 ∧ p2)) → p3) ∨ ((p3 → (p1 → (p2 ∧ True))) ∧ (p1 → True))) ∨ ((p5 ∨ False) ∨ (True ∨ p2)))) ∨ p2)) := by
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
theorem thm_5_vars_696006234330748190971696924279 : ((((p1 ∧ ((False ∧ (True → (p3 ∧ ((True ∧ p2) ∧ (p5 ∨ p5))))) → p5)) → (((p2 ∧ (False ∨ (p4 ∨ (True ∧ p2)))) ∧ False) ∨ p4)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_113472643904143824783857038955 : (((((((True ∧ ((False ∨ p1) → (p2 → p4))) ∧ (p4 → (True → (p2 → p2)))) → False) ∧ False) ∧ (p3 ∨ p1)) ∨ (p2 ∨ True)) ∨ (p5 ∨ p2)) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_663005286443915482859947974 : ((((p2 → (False → ((p3 → p3) ∨ ((False ∨ p2) → p5)))) → (p4 → (p3 ∧ (True → p4)))) ∨ ((p1 ∨ p1) ∧ (p4 ∧ p2))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_347033838130294588435207807235 : (p3 → ((((p4 ∨ True) → (p3 ∧ (((False → True) → False) ∧ ((p4 → p5) ∧ p3)))) ∧ p2) → ((False → (p2 → (p1 ∨ (False → p1)))) → p4))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Implications on the right can always be decomposed.
  intro h3
  -- Conjunctions on the left can always be decomposed.
  let h4 := h2.left
  let h5 := h2.right
  -- We want to use the implication h4 based on <expert-advice>. So we show its premise.
  have h6 : (p4 ∨ True) := by
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h4, we can now drive its conclusion.
  let h7 := h4 h6
  -- We need to get the right conjuct of h7 based on <expert-advice>.
  let h8 := h7.right
  -- We need to get the left conjuct of h8 based on <expert-advice>.
  let h9 := h8.left
  -- We want to use the implication h9 based on <expert-advice>. So we show its premise.
  have h10 : (False → True) := by
    -- Implications on the right can always be decomposed.
    intro h11
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h9, we can now drive its conclusion.
  let h12 := h9 h10
  -- False on the left can always be used.
  apply False.elim h12



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_232897694843364477714463556787 : ((p3 ∧ (p1 ∧ p4)) → (((p5 → (p4 → p2)) → ((True ∨ (p3 ∨ p5)) → ((p2 → (p5 ∧ (p5 ∧ p1))) ∨ (p3 ∧ (p5 → p4))))) ∧ p3)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
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
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Conjunctions on the right can always be decomposed.
    apply And.intro
    -- One of the premise coincides with the conclusion.
    exact h5
    -- Implications on the right can always be decomposed.
    intro h9
    -- One of the premise coincides with the conclusion.
    exact h8
  case inr h10 =>
    -- Disjunctions on the left can always be decomposed.
    cases h10
    case inl h11 =>
      -- Conjunctions on the left can always be decomposed.
      let h12 := h1.left
      let h13 := h1.right
      -- Conjunctions on the left can always be decomposed.
      let h14 := h13.left
      let h15 := h13.right
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Conjunctions on the right can always be decomposed.
      apply And.intro
      -- One of the premise coincides with the conclusion.
      exact h12
      -- Implications on the right can always be decomposed.
      intro h16
      -- One of the premise coincides with the conclusion.
      exact h15
    case inr h17 =>
      -- Conjunctions on the left can always be decomposed.
      let h18 := h1.left
      let h19 := h1.right
      -- Conjunctions on the left can always be decomposed.
      let h20 := h19.left
      let h21 := h19.right
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Conjunctions on the right can always be decomposed.
      apply And.intro
      -- One of the premise coincides with the conclusion.
      exact h18
      -- Implications on the right can always be decomposed.
      intro h22
      -- One of the premise coincides with the conclusion.
      exact h21
  -- Conjunctions on the left can always be decomposed.
  let h23 := h1.left
  let h24 := h1.right
  -- Conjunctions on the left can always be decomposed.
  let h25 := h24.left
  let h26 := h24.right
  -- One of the premise coincides with the conclusion.
  exact h23



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_161327382830137964917094751581 : ((True ∧ ((p4 → True) → ((p3 ∨ (False ∨ (p4 ∨ (True → (((p5 ∧ p5) ∨ p2) ∧ p5))))) → p1))) → ((p4 ∨ p2) ∨ ((p4 → p5) ∨ True))) := by
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
theorem thm_5_vars_472664654441420302034699870169 : ((((p2 → (((p3 ∧ p5) ∨ p4) → (False ∧ ((p5 → p5) ∧ p5)))) ∨ (p4 ∨ (((True ∧ p4) ∨ (p3 → True)) ∨ ((p2 ∧ False) → p3)))) ∧ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
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
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_156335378851447431541951065370 : ((True → ((((p3 ∧ (True → p1)) ∨ p3) ∨ ((p1 → p4) ∨ (((p1 ∧ False) → p2) → p1))) ∨ True)) ∧ (False → (((p3 ∨ p2) ∧ p3) ∧ True))) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- Implications on the right can always be decomposed.
  intro h2
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- False on the left can always be used.
  apply False.elim h2
  -- False on the left can always be used.
  apply False.elim h2
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_308416080111492753204656391141 : (p2 ∨ ((((p2 ∧ ((((p4 ∧ ((p3 ∨ p5) ∧ False)) ∧ p1) ∨ (p1 → ((p3 → (p5 → p3)) ∧ True))) ∨ (p3 ∧ False))) → True) → p2) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_134017733278570732352741193557 : ((((((((p1 → p5) ∧ p3) ∧ ((p4 ∧ ((p2 ∨ True) → (p1 → p4))) → p1)) ∧ (True → False)) ∧ p1) ∨ p4) ∨ True) ∨ (True ∧ (p1 → True))) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_343160995090062893382449247342 : (p2 → ((p1 ∧ (False ∧ p4)) ∨ (p3 → (((p4 ∨ p1) ∧ ((p2 ∧ (True → ((p2 ∧ p1) ∨ p2))) ∧ (p4 ∧ (True ∨ (p2 → True))))) ∨ p2)))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h2
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_50168784706991492950589965162 : (((((((((False ∨ (p2 ∧ False)) ∨ p5) ∧ ((p5 ∧ p3) ∨ (p1 ∧ p4))) → p1) ∧ p5) ∧ p3) ∧ False) ∨ ((p5 ∨ True) ∨ (p5 → p2))) ∨ False) := by
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
theorem thm_5_vars_178909397967302223235720026433 : (((p5 ∨ p2) ∧ ((((p4 ∧ True) ∨ False) ∧ ((p3 ∨ True) ∨ p3)) → p1)) ∨ (((True ∧ ((False ∧ True) ∨ p2)) ∨ False) ∨ ((p5 ∧ p2) → True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_61617103538666917079702136049 : ((p1 ∧ ((p2 ∧ p3) ∨ ((p3 ∨ (p3 ∨ p1)) ∧ ((((p3 ∨ (True ∧ p1)) ∨ ((True → p1) ∧ ((p1 ∧ p5) ∧ False))) → p2) → p5)))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_204291951657782471605643014843 : ((((False → p1) → (p5 ∨ p4)) ∧ False) ∨ (p5 → (p2 → (p3 → (((p3 ∧ p3) → (p2 ∧ (((False ∨ p1) → (True → True)) ∧ p3))) ∧ p5))))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Implications on the right can always be decomposed.
  intro h3
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h4
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Conjunctions on the left can always be decomposed.
  let h5 := h4.left
  let h6 := h4.right
  -- One of the premise coincides with the conclusion.
  exact h2
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h7
  -- Implications on the right can always be decomposed.
  intro h8
  -- True on the right can always be proven directly.
  apply True.intro
  -- Conjunctions on the left can always be decomposed.
  let h9 := h4.left
  let h10 := h4.right
  -- One of the premise coincides with the conclusion.
  exact h3
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_468696551414918488422871962607 : ((((((((p2 ∨ True) ∨ ((p5 ∧ True) → (False ∧ p1))) ∨ p4) ∧ p2) → p3) → (((p1 ∨ p3) ∨ (((p5 → False) ∧ False) → p4)) ∨ p5)) ∧ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
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
theorem thm_5_vars_326231054076106879891039135781 : (p5 ∨ (p3 → ((((((p2 ∨ p5) ∨ True) → (p2 ∧ False)) ∨ (False → (((p2 → True) ∨ (False ∧ p5)) ∨ p3))) ∨ (p2 → p2)) ∨ (False → p3)))) := by
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
theorem thm_5_vars_232839427305410446410464303589 : ((p2 ∧ (p5 ∨ p1)) → (((p5 ∨ p3) ∧ (False ∧ (p2 ∧ (p3 ∨ p3)))) ∨ (p4 → (True → ((True ∨ ((p3 → (p3 → p5)) → p4)) ∧ True))))) := by
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
    -- Implications on the right can always be decomposed.
    intro h5
    -- Implications on the right can always be decomposed.
    intro h6
    -- Conjunctions on the right can always be decomposed.
    apply And.intro
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- True on the right can always be proven directly.
    apply True.intro
    -- True on the right can always be proven directly.
    apply True.intro
  case inr h7 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h8
    -- Implications on the right can always be decomposed.
    intro h9
    -- Conjunctions on the right can always be decomposed.
    apply And.intro
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- True on the right can always be proven directly.
    apply True.intro
    -- True on the right can always be proven directly.
    apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_300998532197897047997894884069 : (False ∨ ((((p1 ∨ p1) → p2) ∨ (p2 ∧ ((False ∨ (p3 ∨ p2)) ∨ p5))) → (p2 ∨ ((((p5 ∧ True) → ((False → p1) ∧ p1)) ∨ True) ∨ p1)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
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
    -- Conjunctions on the left can always be decomposed.
    let h4 := h3.left
    let h5 := h3.right
    -- Disjunctions on the left can always be decomposed.
    cases h5
    case inl h6 =>
      -- Disjunctions on the left can always be decomposed.
      cases h6
      case inl h7 =>
        -- False on the left can always be used.
        apply False.elim h7
      case inr h8 =>
        -- Disjunctions on the left can always be decomposed.
        cases h8
        case inl h9 =>
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- Show the left disjunct based on <expert-advice>.
          apply Or.inl
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- True on the right can always be proven directly.
          apply True.intro
        case inr h10 =>
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- Show the left disjunct based on <expert-advice>.
          apply Or.inl
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- True on the right can always be proven directly.
          apply True.intro
    case inr h11 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- True on the right can always be proven directly.
      apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_673382445248873451432971203623 : (((((p3 → ((p3 ∧ p1) → (p4 ∧ p5))) ∨ (p2 → (((p4 ∨ p2) ∨ (False ∨ p5)) → ((p1 → p2) ∧ p4)))) → ((p2 → p4) ∨ p3)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_204092544984845895455781552852 : ((p5 → (p2 ∨ (False → (p3 ∨ False)))) ∧ ((True ∧ (p3 → (False ∧ (p1 ∨ ((p2 → ((p2 → p4) ∨ p1)) ∨ False))))) ∨ ((False ∨ True) ∨ p2))) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h2
  -- False on the left can always be used.
  apply False.elim h2
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_669547507859659277741174255820 : (((((p2 → ((p3 ∨ ((False ∨ p2) ∧ (p2 ∧ ((((p5 ∧ p5) ∧ p3) ∨ False) → p3)))) → p4)) → (False ∨ p5)) ∨ ((True → p3) → p1)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_653974755591548998251190109515 : (((((p2 ∧ (((True ∨ (p5 ∨ False)) ∧ (p3 ∧ (p2 ∨ p4))) ∧ ((p3 → (p1 ∧ p1)) ∧ ((p2 ∨ True) ∧ p1)))) ∧ p5) ∨ (False → True)) ∨ p5) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
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
theorem thm_5_vars_612508887748157562068519181772 : (((((((((p2 ∧ False) → ((True → (p4 → p3)) → p2)) ∧ (False ∧ ((False ∧ p3) ∧ p1))) ∨ (p1 ∧ p2)) ∨ p4) ∨ (p2 ∨ p3)) ∨ False) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_330358042288256086639051737655 : (True → (p2 ∨ (((p5 ∨ ((p4 ∨ p4) ∧ (p3 ∧ p4))) ∨ ((((p5 ∧ p2) ∧ (p4 ∧ (p2 ∧ p4))) → (p3 → (p2 → p2))) ∧ True)) ∨ False))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h2
  -- Implications on the right can always be decomposed.
  intro h3
  -- Implications on the right can always be decomposed.
  intro h4
  -- Conjunctions on the left can always be decomposed.
  let h5 := h2.left
  let h6 := h2.right
  -- Conjunctions on the left can always be decomposed.
  let h7 := h5.left
  let h8 := h5.right
  -- Conjunctions on the left can always be decomposed.
  let h9 := h6.left
  let h10 := h6.right
  -- Conjunctions on the left can always be decomposed.
  let h11 := h10.left
  let h12 := h10.right
  -- One of the premise coincides with the conclusion.
  exact h11
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_658241811369232487579942536105 : ((((p5 ∧ ((p2 → p5) ∧ (((((p4 ∨ False) → p1) → p1) ∧ p5) ∨ (((False ∧ (p5 ∨ p3)) → (False → True)) → p1)))) ∨ (p4 → p4)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_191519682250279023003203943634 : ((False ∧ ((p1 ∨ p2) → (((p1 ∧ True) ∨ p5) ∨ p1))) ∨ (((((True ∨ (p1 ∧ (True → ((p1 → p2) → False)))) ∧ p1) ∨ False) ∧ False) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_112741624495265905992106750391 : ((((((p4 ∧ ((False → (True ∧ p1)) ∧ p2)) → p4) ∨ (False ∨ p2)) ∨ (((p2 ∨ (p1 → p3)) ∧ (p2 → True)) ∨ False)) → p5) ∨ (p4 → True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_175223025873547340808550381209 : ((p1 ∨ (((p5 ∧ (False ∨ (p4 → ((p4 ∨ p3) ∧ (False ∨ p4))))) ∧ p1) → p2)) → (((p5 ∨ (((p3 ∨ p4) ∨ p3) ∨ False)) → p4) ∨ True)) := by
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
theorem thm_5_vars_158290551372442179903814512171 : ((((p2 ∧ False) ∨ p3) → (True ∧ (((p3 → (p4 → (False ∨ p3))) → p4) → (False ∨ (p1 ∧ False))))) ∨ ((p5 → (True → p5)) ∨ (p1 ∨ p1))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_234291724989286902816437737990 : ((False → (p4 → p3)) → (((p1 ∧ (p3 → p2)) → ((p4 ∧ ((p5 → p2) ∨ False)) → ((p4 → p4) ∨ p5))) → (p2 ∨ (p1 ∨ (False → True))))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h3
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_44682535264463416143437166497 : ((((False ∧ ((p2 ∨ True) → (p3 ∧ True))) → ((((p5 ∨ p1) ∨ (p2 → ((False → True) → True))) ∨ (p1 ∨ (False → p5))) ∧ True)) → False) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_254879324298011525636155984947 : ((p4 ∧ True) → (((p5 ∧ p1) ∨ (True ∧ (p1 ∧ (p4 ∧ (p2 → (((p2 ∧ p5) → ((p2 ∧ (p2 → p1)) → (p3 ∨ p5))) ∧ p5)))))) ∨ True)) := by
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
theorem thm_5_vars_178000348830047662017121201805 : (((p1 ∨ (p2 ∧ (False ∧ ((False → True) → ((p2 ∧ False) ∧ True))))) ∨ p2) ∨ (True ∨ (p1 → (((p4 ∧ (p1 → (p3 → False))) ∨ p2) ∨ p2)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_51469784236403254488405555365 : ((((True ∧ (((p1 → p2) ∨ (p4 ∨ p1)) → False)) ∧ (p1 ∨ ((False → (True → True)) → False))) → ((p3 → ((p2 ∧ p4) → p1)) → p4)) ∨ False) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
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
  -- Disjunctions on the left can always be decomposed.
  cases h4
  case inl h7 =>
    -- We want to use the implication h6 based on <expert-advice>. So we show its premise.
    have h8 : ((p1 → p2) ∨ (p4 ∨ p1)) := by
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- One of the premise coincides with the conclusion.
      exact h7
    -- We have shown the premise of h6, we can now drive its conclusion.
    let h9 := h6 h8
    -- False on the left can always be used.
    apply False.elim h9
  case inr h10 =>
    -- We want to use the implication h10 based on <expert-advice>. So we show its premise.
    have h11 : (False → (True → True)) := by
      -- Implications on the right can always be decomposed.
      intro h12
      -- Implications on the right can always be decomposed.
      intro h13
      -- True on the right can always be proven directly.
      apply True.intro
    -- We have shown the premise of h10, we can now drive its conclusion.
    let h14 := h10 h11
    -- False on the left can always be used.
    apply False.elim h14



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_314836867641093612257523109610 : (p3 ∨ (((p4 ∨ (p5 ∨ (p2 → False))) ∨ (p3 ∨ ((True ∧ p2) → p2))) ∨ ((p5 → (((((p3 ∧ False) ∧ p3) ∧ p2) → p1) ∧ p4)) → True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_157004395103456501295877013427 : (((((False ∨ True) ∨ p5) ∧ (p5 ∨ (((True → False) → (p2 ∧ (p5 → p3))) → (p5 ∨ p1)))) ∨ True) ∨ (((p5 ∨ p2) ∨ p3) ∨ (p2 ∨ False))) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_124715670185904254612431575901 : ((((p5 → (p2 ∧ p3)) ∧ p2) ∧ ((((p3 ∨ p4) ∨ ((p1 → (p2 ∨ p2)) ∧ p4)) ∨ p3) → (p5 ∧ ((p3 ∨ p4) → True)))) → (p2 ∧ True)) := by
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
  -- One of the premise coincides with the conclusion.
  exact h5
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_147193221467034366202873521755 : (((p5 ∨ ((((p4 ∧ ((True ∧ ((p4 ∨ p2) ∨ (p4 ∨ (p4 ∨ p2)))) ∨ p3)) → True) ∨ False) → p3)) ∧ p2) ∨ (True ∨ ((p3 → p3) ∨ p2))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_711903850948217229391547903158 : (((((True → ((p2 ∨ True) → p4)) ∧ p4) ∨ (((((p2 ∨ True) ∨ (False ∨ True)) ∨ (p5 ∧ (p4 ∧ (True ∧ True)))) → (True → p2)) ∧ False)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_135761370393363969213702327142 : (((p4 ∨ (((p5 ∨ p4) ∧ p3) ∧ (((False → p3) → (p1 ∨ p3)) → True))) ∨ (p4 → (((True ∨ p1) ∨ True) ∧ p3))) ∨ ((p3 → p3) ∨ p4)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_157912894668490363015137414565 : ((((p4 ∧ True) ∨ ((p1 → p2) ∨ (p2 → (p1 ∧ p1)))) → ((False ∨ p2) ∧ ((p4 ∨ p4) → p4))) ∨ (True ∧ ((p2 ∧ p3) → (p3 → p2)))) := by
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
  let h3 := h1.left
  let h4 := h1.right
  -- One of the premise coincides with the conclusion.
  exact h3



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_158656219277520902413943989447 : ((p1 ∧ (p1 ∧ (((True → p2) → (((p4 ∨ (p5 ∧ p1)) → (p2 → p1)) ∧ (p4 → p4))) → p4))) ∨ (p5 → ((p1 → (p2 → p1)) ∨ p1))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h2
  -- Implications on the right can always be decomposed.
  intro h3
  -- One of the premise coincides with the conclusion.
  exact h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_315901865938303116261811682750 : (p3 ∨ (True ∧ ((True ∨ (p4 ∨ ((p1 → p1) ∧ ((p5 → (False → (p2 ∧ p2))) ∨ True)))) → ((p2 → (((True ∧ p1) ∨ True) ∨ True)) ∨ p4)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- True on the right can always be proven directly.
  apply True.intro
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
    -- True on the right can always be proven directly.
    apply True.intro
  case inr h4 =>
    -- Disjunctions on the left can always be decomposed.
    cases h4
    case inl h5 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- One of the premise coincides with the conclusion.
      exact h5
    case inr h6 =>
      -- Conjunctions on the left can always be decomposed.
      let h7 := h6.left
      let h8 := h6.right
      -- Disjunctions on the left can always be decomposed.
      cases h8
      case inl h9 =>
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- Implications on the right can always be decomposed.
        intro h10
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- True on the right can always be proven directly.
        apply True.intro
      case inr h11 =>
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- Implications on the right can always be decomposed.
        intro h12
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- True on the right can always be proven directly.
        apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_356670928236797405077057501121 : (p5 → ((p4 ∨ ((p5 ∧ (False → p2)) ∧ (False → p4))) → ((p1 ∨ ((p1 ∨ ((p5 → (p3 ∨ (p4 ∨ True))) → p4)) ∧ (True ∨ p2))) ∨ p5))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Disjunctions on the left can always be decomposed.
  cases h2
  case inl h3 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h1
  case inr h4 =>
    -- Conjunctions on the left can always be decomposed.
    let h5 := h4.left
    let h6 := h4.right
    -- Conjunctions on the left can always be decomposed.
    let h7 := h5.left
    let h8 := h5.right
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_355547111698408547251879658252 : (p5 → (((True → (p1 ∨ ((False → (((False ∧ (p5 ∧ (p2 ∨ (p1 ∨ False)))) ∨ p5) → p4)) → ((p2 ∨ p2) ∨ p2)))) ∨ p1) ∨ (p5 ∨ p5))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_134694398902654025552579554178 : ((((((True → True) ∧ p5) → True) ∧ (p3 ∧ ((p5 ∨ (True ∧ (True ∧ ((True → (p1 ∨ p5)) → p3)))) → p3))) → p4) ∨ ((p1 ∧ True) → p1)) := by
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
theorem thm_5_vars_52594037328183563544371857916 : ((((p5 → ((((p5 ∧ True) ∨ p2) ∧ p5) ∧ p1)) → ((p5 → p2) → p1)) ∨ ((((p1 → True) ∧ ((True ∧ False) ∧ True)) → p1) ∧ p3)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_55021257940221481121261619802 : (((False ∧ (p4 ∧ (True ∨ (p4 ∨ p5)))) ∧ ((p2 ∧ p3) ∧ (((((p4 → p4) ∨ p2) ∧ (p4 ∨ (p3 ∧ (p2 ∨ p2)))) ∨ False) → False))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_655879134587205203409296762389 : (((((p1 ∧ ((((p3 ∧ True) → p2) ∧ ((True → p1) ∨ ((p2 ∨ False) ∧ p1))) ∧ (p1 ∧ True))) → ((True → p5) → p3)) ∨ (p4 → p1)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_207871219562873592450945701733 : ((((p3 → p4) ∨ p4) ∧ (p1 ∧ True)) → ((p2 ∧ (True → p5)) ∨ ((p1 ∧ True) → (p2 → (((False → ((True ∨ False) ∧ False)) ∧ p1) → True))))) := by
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
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h7
    -- Implications on the right can always be decomposed.
    intro h8
    -- Implications on the right can always be decomposed.
    intro h9
    -- True on the right can always be proven directly.
    apply True.intro
  case inr h10 =>
    -- Conjunctions on the left can always be decomposed.
    let h11 := h3.left
    let h12 := h3.right
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h13
    -- Implications on the right can always be decomposed.
    intro h14
    -- Implications on the right can always be decomposed.
    intro h15
    -- True on the right can always be proven directly.
    apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_301255659431452609044042118336 : (False ∨ (((p1 ∨ p1) ∧ (p3 ∨ (p2 ∨ False))) ∨ ((p5 ∨ (False → ((False ∨ p1) → p5))) ∨ (p1 → (((p1 ∧ p5) → p2) ∧ (True → False)))))) := by
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
  -- Disjunctions on the left can always be decomposed.
  cases h2
  case inl h3 =>
    -- False on the left can always be used.
    apply False.elim h3
  case inr h4 =>
    -- False on the left can always be used.
    apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_603280616588502818821578748298 : ((((p2 ∨ ((True → p5) → ((((p2 ∧ p5) ∨ p1) ∨ ((False ∧ False) ∧ (((True ∨ p5) → p2) → ((p5 → p3) ∨ True)))) ∧ False))) ∧ p5) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_56436108623312265722850072600 : ((((p5 → True) ∧ (False ∨ p5)) → ((p5 → p2) ∨ (True ∧ ((((p2 ∨ (p1 → False)) ∨ (((p1 ∧ False) ∨ False) ∨ p3)) ∨ True) ∨ p2)))) ∨ p5) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- Disjunctions on the left can always be decomposed.
  cases h3
  case inl h4 =>
    -- False on the left can always be used.
    apply False.elim h4
  case inr h5 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Conjunctions on the right can always be decomposed.
    apply And.intro
    -- True on the right can always be proven directly.
    apply True.intro
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_178885647459119123604764050578 : (((p4 ∧ p2) ∧ (p3 ∨ ((p5 ∨ ((p2 ∨ True) ∧ (False ∧ True))) ∧ p1))) ∨ (((p1 → p4) → (p5 ∧ (p4 → (False → (p1 ∧ p5))))) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_53563335935542731337212412505 : (((((p3 → ((p1 → (False ∧ p4)) ∨ True)) → p1) ∨ p3) ∧ ((True ∨ (p5 ∧ ((((p5 ∨ p2) ∨ (False → p1)) → True) → p4))) → True)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_193005667593121204560196587530 : ((((p5 ∧ (p4 → (True ∨ False))) → True) → (p4 ∧ False)) → (False ∨ (((False → (p1 ∨ (p1 ∨ (p2 ∧ ((p1 ∧ p1) ∨ True))))) → False) ∨ p1))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h2 : ((p5 ∧ (p4 → (True ∨ False))) → True) := by
    -- Implications on the right can always be decomposed.
    intro h3
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h4 := h1 h2
  -- We need to get the right conjuct of h4 based on <expert-advice>.
  let h5 := h4.right
  -- False on the left can always be used.
  apply False.elim h5



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_158068395539011592618866657553 : ((((((p5 ∨ p5) → False) → p1) ∨ p4) → ((p1 ∧ (p2 ∧ p2)) ∨ ((p1 → p1) ∧ (p5 ∨ True)))) ∨ (((p4 ∨ True) ∧ (p3 ∧ p3)) ∨ p1)) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h2 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Conjunctions on the right can always be decomposed.
    apply And.intro
    -- Implications on the right can always be decomposed.
    intro h3
    -- One of the premise coincides with the conclusion.
    exact h3
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro
  case inr h4 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Conjunctions on the right can always be decomposed.
    apply And.intro
    -- Implications on the right can always be decomposed.
    intro h5
    -- One of the premise coincides with the conclusion.
    exact h5
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_164552869908107957339901764149 : (((((False ∧ (False ∨ (p3 ∧ p4))) ∧ True) ∨ ((p3 ∨ (p5 ∨ (p3 ∨ p3))) → p4)) ∧ p3) ∨ ((True ∨ p4) ∨ ((True ∨ p3) → (p3 → p5)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_44313700342179488708262737557 : (((((p2 ∧ (((True ∨ p2) ∨ (p4 ∨ (p4 ∨ p2))) ∧ (p5 → p2))) ∨ (p3 ∧ p2)) ∨ ((p4 ∧ (p4 ∨ p5)) ∧ (p3 ∨ p4))) → p1) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_61582907167887083531026018384 : ((p1 ∧ (((True ∨ False) ∧ (p1 → p5)) → (((p5 → ((((p5 ∧ (p5 → False)) → (p5 ∧ p5)) ∧ True) ∧ (p2 → False))) ∨ p1) → False))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_187216429401222106789180786460 : (((False → p3) → (p5 ∨ ((p4 ∧ p5) → ((p2 → p2) ∨ p3)))) → (((p2 ∧ p5) ∨ (p2 ∧ (p4 → p1))) → (p3 ∨ (True ∧ (True ∨ True))))) := by
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
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Conjunctions on the right can always be decomposed.
    apply And.intro
    -- True on the right can always be proven directly.
    apply True.intro
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- True on the right can always be proven directly.
    apply True.intro
  case inr h6 =>
    -- Conjunctions on the left can always be decomposed.
    let h7 := h6.left
    let h8 := h6.right
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Conjunctions on the right can always be decomposed.
    apply And.intro
    -- True on the right can always be proven directly.
    apply True.intro
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- True on the right can always be proven directly.
    apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_302523688879985804625753626491 : (False ∨ (False ∨ ((((p4 ∨ (p1 ∧ True)) ∨ True) ∨ p5) → (p2 → (((((p1 ∨ True) ∨ p1) → (((False → True) ∨ p4) ∨ p4)) → p4) ∨ True))))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
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
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- True on the right can always be proven directly.
        apply True.intro
      case inr h6 =>
        -- Conjunctions on the left can always be decomposed.
        let h7 := h6.left
        let h8 := h6.right
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



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_64010094792670317603076827291 : ((False ∨ (((((((p3 ∨ p3) → False) ∨ (((p1 → (True ∨ True)) ∧ True) → p4)) ∧ (p3 ∧ (p4 ∨ p4))) ∨ p4) ∧ p4) ∨ (False → p5))) ∨ p4) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_118460602533304273770939329666 : ((p3 ∨ (((True ∧ p5) ∨ ((((p3 ∨ (((p2 → (True ∧ (False ∨ True))) ∨ p3) ∨ True)) ∧ (False ∧ p1)) → False) → False)) ∨ p5)) ∨ (True ∨ p5)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_65107364386234541787942799780 : ((p2 ∨ (p4 ∨ (((((False → p2) → (p4 → (p5 → True))) ∨ True) → (False ∨ ((p4 ∧ ((p2 ∨ p1) ∧ False)) ∧ p4))) ∨ (p1 → p1)))) ∨ p2) := by
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
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_647452993191979001743919852817 : ((((p4 → (False ∨ (((((p5 → ((p4 → p2) → p1)) → p3) ∧ (p1 → p3)) ∧ ((p5 → p4) → (False ∨ (p4 → p5)))) ∨ p3))) → p2) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_230693026648880647153259563671 : (((p4 → p1) ∧ p3) → ((((True ∨ True) → (p5 ∧ p1)) ∧ p5) → (((p5 ∧ ((p2 → p3) ∧ (True → p2))) → p2) → ((p5 ∧ True) ∧ p1)))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Implications on the right can always be decomposed.
  intro h3
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Conjunctions on the left can always be decomposed.
  let h4 := h2.left
  let h5 := h2.right
  -- Conjunctions on the left can always be decomposed.
  let h6 := h1.left
  let h7 := h1.right
  -- One of the premise coincides with the conclusion.
  exact h5
  -- True on the right can always be proven directly.
  apply True.intro
  -- Conjunctions on the left can always be decomposed.
  let h8 := h2.left
  let h9 := h2.right
  -- Conjunctions on the left can always be decomposed.
  let h10 := h1.left
  let h11 := h1.right
  -- We want to use the implication h8 based on <expert-advice>. So we show its premise.
  have h12 : (True ∨ True) := by
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h8, we can now drive its conclusion.
  let h13 := h8 h12
  -- We need to get the right conjuct of h13 based on <expert-advice>.
  let h14 := h13.right
  -- One of the premise coincides with the conclusion.
  exact h14



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_315661941847313381499809148227 : (p3 ∨ ((p3 ∧ p2) ∨ (((((False ∨ True) ∧ False) ∧ True) ∨ (p2 ∨ (((p1 → (p4 → p1)) ∨ p2) ∨ p3))) ∨ ((True → p5) → (False ∨ p1))))) := by
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
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_53208786212158898323122223397 : (((((False → ((True ∨ p4) ∧ p3)) → False) ∧ (True ∨ (p1 → p5))) ∨ (p2 ∧ (((False → p1) ∨ (p3 → (False ∨ (p1 ∧ p4)))) ∧ p2))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_244911981606553661889254106103 : ((p1 ∧ p3) ∨ (((((p2 ∧ p5) ∧ (True ∨ ((p2 ∧ (p2 ∨ (p1 → (True → (p5 ∨ True))))) → (p2 ∨ p1)))) ∨ p5) ∨ (False → True)) ∧ True)) := by
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
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_304678459522894678723681076254 : (p1 ∨ ((((p2 ∨ (((p1 ∧ False) → p4) ∧ p5)) ∨ (((False → ((p4 ∧ p4) → (p4 ∨ (p3 ∧ p1)))) ∧ p3) ∨ p3)) ∧ p3) ∨ (p4 ∨ True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_249759920228046203003998350472 : ((p5 ∨ p5) ∨ (p2 ∨ ((p2 → ((((p3 → ((((False ∨ p5) → p3) → False) ∧ p4)) → ((p1 → p4) ∧ (p2 → p1))) ∧ p4) ∨ True)) ∨ True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_347653309505720941318512087160 : (p3 → (((p4 → (p2 ∨ p4)) → False) → ((((p1 → p3) ∨ (False → (p4 ∨ True))) ∨ ((p2 ∨ False) ∨ p2)) → (p2 ∧ (p5 ∨ (True ∧ p2)))))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Implications on the right can always be decomposed.
  intro h3
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Disjunctions on the left can always be decomposed.
  cases h3
  case inl h4 =>
    -- Disjunctions on the left can always be decomposed.
    cases h4
    case inl h5 =>
      -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
      have h6 : (p4 → (p2 ∨ p4)) := by
        -- Implications on the right can always be decomposed.
        intro h7
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- One of the premise coincides with the conclusion.
        exact h7
      -- We have shown the premise of h2, we can now drive its conclusion.
      let h8 := h2 h6
      -- False on the left can always be used.
      apply False.elim h8
    case inr h9 =>
      -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
      have h10 : (p4 → (p2 ∨ p4)) := by
        -- Implications on the right can always be decomposed.
        intro h11
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- One of the premise coincides with the conclusion.
        exact h11
      -- We have shown the premise of h2, we can now drive its conclusion.
      let h12 := h2 h10
      -- False on the left can always be used.
      apply False.elim h12
  case inr h13 =>
    -- Disjunctions on the left can always be decomposed.
    cases h13
    case inl h14 =>
      -- Disjunctions on the left can always be decomposed.
      cases h14
      case inl h15 =>
        -- One of the premise coincides with the conclusion.
        exact h15
      case inr h16 =>
        -- False on the left can always be used.
        apply False.elim h16
    case inr h17 =>
      -- One of the premise coincides with the conclusion.
      exact h17
  -- Disjunctions on the left can always be decomposed.
  cases h3
  case inl h18 =>
    -- Disjunctions on the left can always be decomposed.
    cases h18
    case inl h19 =>
      -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
      have h20 : (p4 → (p2 ∨ p4)) := by
        -- Implications on the right can always be decomposed.
        intro h21
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- One of the premise coincides with the conclusion.
        exact h21
      -- We have shown the premise of h2, we can now drive its conclusion.
      let h22 := h2 h20
      -- False on the left can always be used.
      apply False.elim h22
    case inr h23 =>
      -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
      have h24 : (p4 → (p2 ∨ p4)) := by
        -- Implications on the right can always be decomposed.
        intro h25
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- One of the premise coincides with the conclusion.
        exact h25
      -- We have shown the premise of h2, we can now drive its conclusion.
      let h26 := h2 h24
      -- False on the left can always be used.
      apply False.elim h26
  case inr h27 =>
    -- Disjunctions on the left can always be decomposed.
    cases h27
    case inl h28 =>
      -- Disjunctions on the left can always be decomposed.
      cases h28
      case inl h29 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- Conjunctions on the right can always be decomposed.
        apply And.intro
        -- True on the right can always be proven directly.
        apply True.intro
        -- One of the premise coincides with the conclusion.
        exact h29
      case inr h30 =>
        -- False on the left can always be used.
        apply False.elim h30
    case inr h31 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Conjunctions on the right can always be decomposed.
      apply And.intro
      -- True on the right can always be proven directly.
      apply True.intro
      -- One of the premise coincides with the conclusion.
      exact h31



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_137073768060867581187896316859 : (((p4 → p5) → ((((True → ((p3 ∧ p5) → ((((p4 ∧ p3) ∧ p3) → p4) ∧ (p1 ∨ p1)))) ∧ True) → p2) ∧ p3)) ∨ (False → (p1 → p4))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_116187507223285694033088004579 : ((((True ∧ False) ∧ False) ∨ ((p3 → ((((((True ∧ p5) → p2) ∧ (p2 ∧ p5)) → (p1 → p1)) → p2) ∧ (False ∨ p2))) ∧ p2)) ∨ (p1 ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_342694179821542267108436825334 : (p2 → ((((p5 ∨ p3) → False) ∧ (p3 → ((True ∨ p4) → p5))) → (((p2 ∨ p4) ∨ True) → (p1 → ((p4 ∧ (p3 → (p1 → False))) ∨ p2))))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Implications on the right can always be decomposed.
  intro h3
  -- Implications on the right can always be decomposed.
  intro h4
  -- Disjunctions on the left can always be decomposed.
  cases h3
  case inl h5 =>
    -- Disjunctions on the left can always be decomposed.
    cases h5
    case inl h6 =>
      -- Conjunctions on the left can always be decomposed.
      let h7 := h2.left
      let h8 := h2.right
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- One of the premise coincides with the conclusion.
      exact h1
    case inr h9 =>
      -- Conjunctions on the left can always be decomposed.
      let h10 := h2.left
      let h11 := h2.right
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- One of the premise coincides with the conclusion.
      exact h1
  case inr h12 =>
    -- Conjunctions on the left can always be decomposed.
    let h13 := h2.left
    let h14 := h2.right
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_60723736378134147900518249593 : ((True ∧ (((p2 ∧ p1) ∧ (False ∧ True)) ∧ ((((((p1 → p5) ∨ p4) → False) ∨ ((p2 ∧ (p5 ∧ True)) → (True ∨ p4))) ∧ p4) → False))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_55243678253343342339965399053 : ((((p1 ∨ p3) ∧ (p5 → (False ∧ p3))) ∨ ((p5 ∧ ((p4 ∧ (False ∨ (p4 → p4))) → ((p3 ∨ False) → ((p3 ∧ p3) ∧ True)))) → p3)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_308741767665069692899845442679 : (p2 ∨ ((p4 → ((((p1 → p2) → (((p4 → (p1 ∧ p1)) → (p1 ∧ (p2 ∨ p2))) ∨ (False ∧ (p3 ∨ p3)))) ∨ (True ∨ p2)) ∨ True)) ∨ p2)) := by
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
theorem thm_5_vars_178353202500095955840169849279 : (((False ∨ (p1 ∧ (p4 → ((p4 → p3) ∨ (p1 ∨ p1))))) ∨ (p1 ∧ p1)) ∨ ((p2 → p1) ∨ (False → (((False → True) → p5) ∨ (p4 ∧ False))))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_41831623541348818796941588616 : ((((False ∧ (p3 ∧ p1)) ∧ (((((False ∧ p1) ∨ False) ∧ p4) → p2) → (((False ∧ (p4 → p2)) → (p2 → p1)) ∧ (True → False)))) ∨ p3) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



