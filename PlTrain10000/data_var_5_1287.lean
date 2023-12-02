variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_122287613609712333657622260025 : (((p4 ∧ (p5 → ((((p5 → p5) ∨ p5) → p2) ∨ (((p2 → True) ∨ (False → False)) → ((True ∧ True) ∧ p1))))) ∧ (p4 ∨ False)) → (p1 → p1)) := by
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
    -- One of the premise coincides with the conclusion.
    exact h2
  case inr h8 =>
    -- False on the left can always be used.
    apply False.elim h8



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_184128841793886239807413566894 : (((p1 ∧ (((p5 ∨ p2) → (True ∧ False)) → (p4 ∨ p2))) ∨ True) ∨ ((((p2 ∨ p4) → p5) ∨ p4) ∧ (((p3 → p3) → p1) ∨ (p5 ∧ p1)))) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_111091041723855825936280837069 : ((((p2 ∧ ((p2 → (p3 ∨ ((p3 ∧ p1) → False))) ∧ (p3 ∧ False))) ∨ (((False ∧ True) → p2) ∨ ((p5 ∧ p2) ∨ True))) ∧ True) ∨ (p3 → p5)) := by
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



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_593616715672784122572095802456 : (((((((False ∨ ((p2 ∧ ((p2 → p1) ∧ False)) ∨ p3)) ∨ ((p2 ∧ (p1 ∧ p2)) ∧ True)) ∧ True) ∧ (((p5 → p1) ∧ True) ∨ p4)) ∧ p4) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_166734024793204681473994226674 : ((p4 → (((((False ∧ p3) ∨ (p5 ∧ p1)) ∧ (p3 ∨ ((p3 ∧ False) ∧ True))) ∨ p5) ∨ p2)) ∨ (p5 ∨ (((p1 ∨ (p2 → True)) ∨ p5) ∨ p3))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_679552120804249577217318845804 : (((((((p3 → False) → (p4 → p1)) ∧ ((p2 → (True ∨ False)) → (p3 ∧ ((False ∨ p2) ∧ p5)))) ∧ p3) → (((p4 ∧ False) ∨ p5) ∧ True)) ∨ False) ∧ True) := by
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
  let h4 := h2.left
  let h5 := h2.right
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- We want to use the implication h5 based on <expert-advice>. So we show its premise.
  have h6 : (p2 → (True ∨ False)) := by
    -- Implications on the right can always be decomposed.
    intro h7
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h5, we can now drive its conclusion.
  let h8 := h5 h6
  -- We need to get the right conjuct of h8 based on <expert-advice>.
  let h9 := h8.right
  -- We need to get the right conjuct of h9 based on <expert-advice>.
  let h10 := h9.right
  -- One of the premise coincides with the conclusion.
  exact h10
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_159091570469145454528473661745 : ((True → ((p4 ∨ ((False ∨ ((p5 → ((True → p4) ∧ p4)) ∧ p2)) ∧ p2)) ∧ ((p3 ∨ False) ∨ p3))) ∨ (((p4 → p3) → (p4 → p4)) ∨ False)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- One of the premise coincides with the conclusion.
  exact h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_51193992004694446845079800058 : (((((p5 ∨ (p4 ∧ False)) → (False ∧ (((False → False) → False) ∧ False))) → ((p3 ∨ p5) ∨ p1)) ∨ ((p1 ∨ (p5 ∨ p2)) ∨ (False → p3))) ∨ p1) := by
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
theorem thm_5_vars_673118206396788908487269814381 : (((((((((True ∧ True) → ((True ∨ True) → p3)) ∨ p1) → p1) ∧ False) → (p4 ∧ (((p1 ∨ p4) ∧ p2) → False))) → (False ∧ (False → p1))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_625774556874903685298845126254 : ((((p1 → (p1 ∧ ((p2 ∨ (p1 → ((((p4 ∨ ((p2 ∧ ((p4 ∨ p3) ∨ p1)) → p4)) ∨ p1) ∨ p1) ∧ (p1 → p1)))) → p4))) ∨ True) ∨ p5) ∧ True) := by
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
theorem thm_5_vars_116448982114995088122371505109 : (((True ∧ True) ∧ ((((p1 → p3) → ((True ∨ (True → (True ∧ ((False ∧ p5) ∨ p2)))) ∧ (p3 → (p5 ∨ p1)))) ∧ False) ∧ p5)) ∨ (False → p5)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_119089555745720039711835169310 : ((p1 → (((p2 ∧ ((True → (((p1 ∨ p4) → p5) ∨ p1)) → p4)) ∨ p4) → (p4 ∨ (True → ((p4 ∧ p4) ∨ (False ∨ p4)))))) ∨ (p3 ∧ p2)) := by
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
    let h4 := h3.left
    let h5 := h3.right
    -- We want to use the implication h5 based on <expert-advice>. So we show its premise.
    have h6 : (True → (((p1 ∨ p4) → p5) ∨ p1)) := by
      -- Implications on the right can always be decomposed.
      intro h7
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- One of the premise coincides with the conclusion.
      exact h1
    -- We have shown the premise of h5, we can now drive its conclusion.
    let h8 := h5 h6
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- One of the premise coincides with the conclusion.
    exact h8
  case inr h9 =>
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- One of the premise coincides with the conclusion.
    exact h9



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_42727311210318229115914359863 : (((True → ((((((p2 ∧ (p4 ∧ (p3 ∧ False))) ∨ p1) ∨ p4) ∧ False) ∧ ((((p4 ∨ p1) → p3) ∧ (p3 ∨ p3)) ∧ True)) ∨ False)) ∨ True) ∨ p5) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_49133197147670590876488596308 : (((((p1 ∧ p2) ∧ (p4 → ((p4 → p2) ∧ ((p4 ∨ p3) ∨ p5)))) → ((((p2 ∨ p4) ∧ p3) ∧ p3) ∧ False)) ∨ (p3 ∨ (True ∨ p4))) ∨ p5) := by
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
theorem thm_5_vars_679300548209274044474199294481 : ((((p1 → (True ∧ (p3 ∨ ((((((False ∨ (p1 ∨ (p5 → p2))) ∨ p4) ∧ p1) → p5) ∨ False) ∧ False)))) ∨ ((False → p2) ∧ (False → p3))) ∨ p1) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
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
  -- False on the left can always be used.
  apply False.elim h2
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_64233719574243689073193360207 : ((False ∨ (False ∨ (((p2 ∧ p1) ∧ (((p5 ∧ (False → p4)) ∧ (False ∧ p2)) ∨ ((p2 ∨ ((p1 → p2) ∧ p5)) ∨ (False → p2)))) ∨ True))) ∨ p2) := by
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
theorem thm_5_vars_804201922150882215285457341524 : (((p3 → (((p4 → (p2 ∨ (((((p3 → p5) ∧ p3) ∧ p2) → False) ∨ (p5 ∨ p2)))) → p5) ∨ ((p1 ∨ p2) ∨ (p5 ∧ (False ∧ True))))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_185864801182153011240158797894 : (((((p5 ∨ (((p2 → p2) ∨ True) → p2)) ∨ True) → False) ∧ p4) → ((p1 ∨ p5) ∧ ((p4 ∨ p2) → ((p1 → (p1 ∨ (p2 ∧ p2))) ∨ p2)))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
  have h4 : ((p5 ∨ (((p2 → p2) ∨ True) → p2)) ∨ True) := by
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h2, we can now drive its conclusion.
  let h5 := h2 h4
  -- False on the left can always be used.
  apply False.elim h5
  -- Implications on the right can always be decomposed.
  intro h6
  -- Disjunctions on the left can always be decomposed.
  cases h6
  case inl h7 =>
    -- Conjunctions on the left can always be decomposed.
    let h8 := h1.left
    let h9 := h1.right
    -- We want to use the implication h8 based on <expert-advice>. So we show its premise.
    have h10 : ((p5 ∨ (((p2 → p2) ∨ True) → p2)) ∨ True) := by
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- True on the right can always be proven directly.
      apply True.intro
    -- We have shown the premise of h8, we can now drive its conclusion.
    let h11 := h8 h10
    -- False on the left can always be used.
    apply False.elim h11
  case inr h12 =>
    -- Conjunctions on the left can always be decomposed.
    let h13 := h1.left
    let h14 := h1.right
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h12



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_350168215463570877962383381965 : (p4 → (((p1 ∧ (False ∧ (False ∧ (p5 ∧ p4)))) ∧ (p3 ∧ ((((p2 ∨ p4) ∧ (True ∧ (True ∨ p5))) ∧ (False → (False ∧ p3))) ∨ p5))) ∨ True)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_599629525315663701682593029323 : (((((True → p4) ∨ (((p2 ∧ p2) → True) ∧ (((p2 → (p5 ∨ p4)) ∧ ((p5 ∨ False) ∨ (p4 ∨ (p2 ∧ (p5 ∧ p2))))) → p1))) ∧ p3) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_691704256240739828704948119398 : ((((False ∨ (((((True → p3) ∧ (p3 ∧ (p4 ∧ (False ∨ False)))) ∨ True) → p1) → p1)) → ((p5 ∧ (p3 ∧ ((p2 → p3) → p5))) → p3)) ∨ p2) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
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
  let h5 := h4.left
  let h6 := h4.right
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h7 =>
    -- False on the left can always be used.
    apply False.elim h7
  case inr h8 =>
    -- One of the premise coincides with the conclusion.
    exact h5
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_42091453902606907763762844796 : ((((p5 → p1) ∨ (p1 ∧ (((p3 ∧ False) ∧ p5) ∨ ((p5 ∨ p2) → ((p3 → ((p4 → p3) ∧ ((p3 ∧ p4) ∨ False))) ∧ p3))))) ∨ True) ∨ False) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_53471679635505814293854474292 : (((True ∧ ((p2 → ((p1 ∨ (p5 ∨ p5)) ∨ (p1 ∨ p2))) → p3)) → (((p3 → p5) ∨ p3) ∨ ((False ∨ True) → ((p1 ∨ p3) ∧ p4)))) ∨ p4) := by
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
  -- We want to use the implication h3 based on <expert-advice>. So we show its premise.
  have h4 : (p2 → ((p1 ∨ (p5 ∨ p5)) ∨ (p1 ∨ p2))) := by
    -- Implications on the right can always be decomposed.
    intro h5
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h5
  -- We have shown the premise of h3, we can now drive its conclusion.
  let h6 := h3 h4
  -- One of the premise coincides with the conclusion.
  exact h6



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_801950949654999480583658306595 : (((p2 → ((p4 ∨ False) ∨ (((p3 ∨ (False ∨ ((False ∨ p2) ∧ p1))) ∧ (p4 → True)) ∧ (((p1 → ((True ∨ False) ∧ p3)) ∨ False) ∨ False)))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_158258204724570672795751793119 : ((((p1 → p4) → p1) ∨ (((p2 ∧ (((p4 ∨ p4) ∨ (p2 ∧ p5)) → (p1 ∨ p3))) → False) ∧ p2)) ∨ ((False ∨ (p2 ∨ (False → p4))) ∨ p3)) := by
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
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_638792067304209046994732279327 : (((((p3 → ((p3 ∧ p1) ∨ (p1 ∧ True))) → (((True → True) ∨ (p4 ∨ p4)) ∨ ((p3 → p3) ∧ (p1 → (True ∨ (p5 → False)))))) → False) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_173215757737314583754303273333 : ((p5 ∨ (True ∧ (((p5 ∧ True) ∧ True) ∧ (False ∧ ((p2 → (p2 ∧ p5)) → p5))))) ∨ (True ∧ ((p3 → True) ∨ (((p1 ∨ p1) ∨ p5) ∨ p4)))) := by
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
theorem thm_5_vars_201082211507906660394336927879 : ((p5 ∨ (p3 ∧ ((p2 ∨ p4) ∧ (p4 → True)))) → ((p5 ∧ (p5 ∧ p2)) → (p2 → (((p1 ∨ p3) ∨ ((p4 ∧ False) ∨ False)) ∨ (p3 ∨ True))))) := by
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
  let h6 := h5.left
  let h7 := h5.right
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h8 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro
  case inr h9 =>
    -- Conjunctions on the left can always be decomposed.
    let h10 := h9.left
    let h11 := h9.right
    -- Conjunctions on the left can always be decomposed.
    let h12 := h11.left
    let h13 := h11.right
    -- Disjunctions on the left can always be decomposed.
    cases h12
    case inl h14 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- One of the premise coincides with the conclusion.
      exact h10
    case inr h15 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- One of the premise coincides with the conclusion.
      exact h10



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_185327639110497113370414105680 : ((p3 ∧ (p2 ∧ ((p3 ∨ p2) ∧ (p5 → ((True ∨ False) → p5))))) ∨ (p4 ∨ (p5 ∨ ((False → p1) ∨ (((True ∨ (p4 ∨ p1)) → p2) ∨ p1))))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
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
theorem thm_5_vars_703101489467129115060306532196 : (((((p5 ∨ p1) ∨ (False ∧ ((p4 → (p4 ∧ p2)) ∧ p4))) ∨ (p4 ∨ (True ∧ ((False ∧ p1) → (((True ∨ False) ∨ (p5 ∧ p5)) → True))))) ∨ p3) ∧ True) := by
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
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_717954299374377381417963598002 : (((((p3 → (False → p4)) ∧ p1) ∨ (p1 ∨ (p2 ∨ (p1 ∧ ((True ∧ p1) → (False ∧ ((((p5 ∧ True) ∧ p2) ∧ True) → (p1 ∧ p2)))))))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_791855209234177998454688218565 : (((True → (((((p2 → p1) ∧ p4) ∧ p1) → (((p3 ∧ True) ∧ p1) ∨ (p4 ∧ (((p4 ∧ p5) ∨ p3) ∧ (p2 ∧ p4))))) ∧ (p4 ∧ p4))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_693482706430612148980040670139 : (((((((p5 ∧ (p3 → False)) → ((p5 ∨ (p4 ∧ p3)) ∧ p4)) ∨ p2) ∧ p2) ∨ ((p4 ∧ ((True ∧ p3) ∨ p4)) ∨ (True ∨ (p2 ∨ True)))) ∨ p4) ∧ True) := by
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
theorem thm_5_vars_68381523906599116264735882667 : ((p3 → ((p5 ∧ (False ∧ (True → True))) ∨ (((False ∨ (p2 ∨ (((((p4 ∨ True) ∨ (p4 ∨ p5)) ∨ p3) ∨ p1) → p3))) → p5) ∧ p5))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_680286693173950097070941863877 : ((((((((False ∨ p5) ∧ True) ∨ ((p4 ∨ (True → True)) ∧ (True ∨ p3))) → p2) ∧ ((p4 → False) → False)) → (((False → p3) → p2) ∧ p5)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_40896472102956051068363902613 : ((((((False ∨ p3) ∨ p2) → (((p1 ∨ p1) → ((p5 → (True → (((True → False) ∨ False) ∨ p3))) → p3)) → p4)) ∧ (p2 ∨ p5)) ∨ p2) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_178697770975309276591650639347 : ((((p1 ∧ p4) ∨ (p4 ∨ p5)) ∨ (p2 → (p5 ∧ (p1 ∨ (p2 → p4))))) ∨ (p4 ∨ (((p2 ∧ p3) → (p2 → (p3 ∧ True))) ∨ (p2 ∨ p2)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Conjunctions on the left can always be decomposed.
  let h3 := h1.left
  let h4 := h1.right
  -- One of the premise coincides with the conclusion.
  exact h4
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_62337479017634997494441173001 : ((p3 ∧ ((p2 → (((p3 ∨ (p4 → (p1 ∨ ((True ∧ p5) → ((True ∧ p3) ∧ p3))))) ∨ (p5 ∧ p5)) → p3)) ∧ ((p4 ∧ p3) ∨ p3))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_261070671576454940050606517356 : ((p4 → p3) → ((((((p1 ∨ ((p4 → (p1 ∨ (p4 → (p2 ∧ p4)))) ∨ True)) ∧ (p1 → False)) ∨ False) ∧ ((True ∨ p3) ∧ p3)) ∨ p2) ∨ True)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_48805807663144527823630956286 : (((p2 ∧ (((p1 → False) ∧ (p2 ∧ (((p1 ∧ True) ∨ (p2 ∨ p2)) ∧ (True → (p5 ∨ p2))))) ∨ (p4 ∧ p2))) ∧ (p2 ∧ (p4 ∨ p5))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_955878435167169902871065122022 : (((((p2 ∧ p1) ∨ True) → (((False → ((True ∨ ((False ∨ p1) ∨ (p2 ∨ ((p1 ∧ True) ∧ True)))) → (p2 ∧ (p4 → p4)))) ∨ p2) ∧ False)) → p2) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h1
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h2 : ((p2 ∧ p1) ∨ True) := by
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h3 := h1 h2
  -- We need to get the right conjuct of h3 based on <expert-advice>.
  let h4 := h3.right
  -- False on the left can always be used.
  apply False.elim h4
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_239150610098889912103427029248 : ((p2 ∨ True) ∧ ((True ∧ (((p1 ∨ p1) → (p2 ∨ (p3 ∨ ((p3 → (True ∨ True)) → ((p1 → (p1 → p2)) ∧ True))))) ∧ (False ∧ False))) ∨ True)) := by
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
theorem thm_5_vars_230615865675099864841235262580 : (((p2 → p1) ∧ p5) → ((((False ∨ (p1 ∨ False)) → True) → (False ∧ (p1 ∨ False))) ∨ ((False ∨ p5) ∨ (p4 ∨ ((p5 ∧ (p5 → p3)) → True))))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h3



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_337220096753249578747102055520 : (p1 → ((((p5 ∧ (p3 ∨ False)) → False) ∨ (((((p3 → (p4 ∧ ((p4 ∨ (p4 → p2)) ∨ True))) → False) ∧ p1) ∧ True) → p3)) → (p2 → p2))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Implications on the right can always be decomposed.
  intro h3
  -- Disjunctions on the left can always be decomposed.
  cases h2
  case inl h4 =>
    -- One of the premise coincides with the conclusion.
    exact h3
  case inr h5 =>
    -- One of the premise coincides with the conclusion.
    exact h3



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_205994782661182262328104424824 : ((p1 ∧ (p5 ∧ ((p1 ∨ p2) → False))) ∨ ((p5 ∧ (p4 ∨ (p5 ∨ p3))) → (p4 ∨ (((p2 ∨ ((p4 ∨ (False → p3)) → p5)) ∧ p5) → True)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- Disjunctions on the left can always be decomposed.
  cases h3
  case inl h4 =>
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- One of the premise coincides with the conclusion.
    exact h4
  case inr h5 =>
    -- Disjunctions on the left can always be decomposed.
    cases h5
    case inl h6 =>
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



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_53626568171153296024642902287 : ((((p4 ∧ ((p5 ∨ p3) ∨ False)) ∧ ((p3 ∨ p3) ∨ p5)) ∧ ((((p2 ∨ ((p5 ∨ True) → p1)) ∨ True) ∧ (p5 ∧ (p3 ∧ p5))) ∧ p2)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_115432320492257153596726554616 : ((((((p5 ∧ p5) ∧ (p3 → False)) → True) → False) ∨ (True → ((p2 → (p3 → (p5 ∨ (p2 → (p3 → True))))) → (True ∨ False)))) ∨ (p4 ∨ p2)) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_656223956047759579235248166436 : ((((((True ∧ (True → p2)) ∧ (p4 → ((True ∧ True) ∨ (p3 → (p1 ∧ False))))) → ((p4 ∨ (p3 → (p2 → p4))) ∧ p4)) ∨ (False ∨ p2)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_353383727582319856282036821162 : (p4 → (False ∨ ((p5 → True) ∧ ((p4 → ((False ∨ False) ∧ ((True → (True ∧ ((((p1 → False) → True) ∧ p1) ∨ True))) → False))) ∨ (p3 ∨ True))))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h2
  -- True on the right can always be proven directly.
  apply True.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_53292631615510740295261071258 : (((False ∨ (p5 ∨ ((p3 → (p4 → p1)) → ((True → False) → p2)))) ∨ ((((True ∨ (((p5 ∨ p4) ∧ p4) → p3)) ∨ p4) ∨ p2) → p1)) ∨ p3) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
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
  -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
  have h3 : True := by
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h2, we can now drive its conclusion.
  let h4 := h2 h3
  -- False on the left can always be used.
  apply False.elim h4



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_668627417512607375917216931102 : (((((False ∨ ((p1 → ((p2 → p4) → (p4 ∧ (((p3 → (p5 ∧ p5)) ∨ p1) → False)))) → (False ∧ p3))) ∧ p2) ∨ (p4 → (p1 → p5))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_609529575438531865236359369682 : (((((p2 ∧ (p2 ∧ (p4 ∨ ((p3 ∨ p3) ∨ (p2 ∨ ((p5 → (p3 ∨ (p4 ∧ ((p2 ∨ p4) ∧ p5)))) ∨ (False ∧ p3))))))) ∨ False) ∨ p4) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_317751159099730287474470546353 : (p4 ∨ (((p5 ∧ ((p2 ∨ p4) ∧ (p3 → ((((((True → p4) ∨ p4) → False) → p3) → False) ∧ False)))) ∨ ((p1 → False) ∧ (p4 ∧ p3))) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_621653917729463576334439819533 : ((((False ∧ (p4 ∧ ((p1 ∨ (p3 ∧ False)) → (p3 ∨ ((((p5 ∨ p1) → p1) → (p1 → (p2 → (p5 ∨ p5)))) ∧ (False → p1)))))) ∨ p5) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_184765610677965906194875839940 : (((p4 ∨ (p2 ∨ (p2 → p2))) ∧ (p4 ∧ ((p5 ∨ p2) ∨ p1))) ∨ ((p5 ∧ (((((False ∨ p4) → p2) ∨ p5) ∨ p3) ∧ p2)) → (p2 ∧ p5))) := by
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
  let h4 := h3.left
  let h5 := h3.right
  -- Disjunctions on the left can always be decomposed.
  cases h4
  case inl h6 =>
    -- Disjunctions on the left can always be decomposed.
    cases h6
    case inl h7 =>
      -- One of the premise coincides with the conclusion.
      exact h5
    case inr h8 =>
      -- One of the premise coincides with the conclusion.
      exact h5
  case inr h9 =>
    -- One of the premise coincides with the conclusion.
    exact h5
  -- Conjunctions on the left can always be decomposed.
  let h10 := h1.left
  let h11 := h1.right
  -- Conjunctions on the left can always be decomposed.
  let h12 := h11.left
  let h13 := h11.right
  -- Disjunctions on the left can always be decomposed.
  cases h12
  case inl h14 =>
    -- Disjunctions on the left can always be decomposed.
    cases h14
    case inl h15 =>
      -- One of the premise coincides with the conclusion.
      exact h10
    case inr h16 =>
      -- One of the premise coincides with the conclusion.
      exact h16
  case inr h17 =>
    -- One of the premise coincides with the conclusion.
    exact h10



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_147895792935256694111766344332 : (((((p3 ∧ (p1 → (p5 ∧ False))) ∧ (((False ∧ p4) → True) → ((p1 ∨ False) ∧ p4))) ∨ p5) ∧ (p1 → p2)) ∨ (p5 → ((False → p3) ∨ p4))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h2
  -- False on the left can always be used.
  apply False.elim h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_340837432518861610712193812302 : (p2 → (((p4 ∧ (p4 ∧ (((True ∨ (p3 ∧ (p3 → (p3 ∨ p5)))) → ((p4 → p2) ∧ (p1 ∧ p4))) ∧ (p5 → False)))) → (False ∨ p3)) ∨ p2)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_181508970960085771951055771662 : ((p5 ∨ (p5 ∧ (((p5 → (p3 ∨ p3)) → ((p4 ∧ p1) ∨ True)) ∨ p4))) → (False ∨ (((p5 ∨ p5) ∧ p5) → ((p1 ∨ p2) ∨ (True ∨ p4))))) := by
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
    -- Disjunctions on the left can always be decomposed.
    cases h4
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
  case inr h8 =>
    -- Conjunctions on the left can always be decomposed.
    let h9 := h8.left
    let h10 := h8.right
    -- Disjunctions on the left can always be decomposed.
    cases h10
    case inl h11 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Implications on the right can always be decomposed.
      intro h12
      -- Conjunctions on the left can always be decomposed.
      let h13 := h12.left
      let h14 := h12.right
      -- Disjunctions on the left can always be decomposed.
      cases h13
      case inl h15 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- True on the right can always be proven directly.
        apply True.intro
      case inr h16 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- True on the right can always be proven directly.
        apply True.intro
    case inr h17 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Implications on the right can always be decomposed.
      intro h18
      -- Conjunctions on the left can always be decomposed.
      let h19 := h18.left
      let h20 := h18.right
      -- Disjunctions on the left can always be decomposed.
      cases h19
      case inl h21 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- True on the right can always be proven directly.
        apply True.intro
      case inr h22 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- True on the right can always be proven directly.
        apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_303740161026269032027434315193 : (p1 ∨ (((True → (((p4 ∧ p2) ∨ p1) ∧ (p1 ∨ ((p2 → ((False → p4) ∧ p4)) → ((False ∧ ((True → True) ∧ True)) ∨ False))))) ∧ True) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_201028440401199820527933199518 : ((p4 ∨ (((p3 ∧ (p4 → p3)) → p3) → p2)) → ((p3 ∧ (p1 → (p4 → ((p3 ∧ p5) ∧ (p3 → (p3 → p3)))))) ∨ (p1 ∨ (True → True)))) := by
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
    -- True on the right can always be proven directly.
    apply True.intro
  case inr h4 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h5
    -- True on the right can always be proven directly.
    apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_315257512492604973080842698094 : (p3 ∨ ((p2 ∧ ((p1 ∧ p4) ∧ p3)) ∨ (((((False ∨ (p1 ∨ True)) ∧ (((p5 → (p1 ∧ False)) ∧ True) ∨ (p2 → True))) ∨ p3) ∨ p1) ∨ False))) := by
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
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_40281428135525724435281908672 : ((((p1 → ((p2 ∨ p5) → (((((p1 → True) ∨ False) ∨ (False ∨ p5)) → ((p5 ∧ True) ∧ (p4 ∧ (p2 ∨ False)))) ∨ False))) ∧ p3) ∨ True) ∨ p1) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_300566215323275579524003157742 : (False ∨ ((p2 ∧ (((p3 ∨ True) → ((p3 ∨ False) ∨ (p2 ∧ ((p3 ∨ p4) → False)))) ∧ ((p3 → p5) → p2))) ∨ ((p4 ∧ (p3 ∧ False)) ∨ True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_190312487219451381240488152951 : (((((p1 ∨ p4) ∧ (False ∨ p1)) ∧ (p4 → p5)) ∨ False) ∨ ((p4 ∧ (p1 → ((p5 ∨ p4) → (p2 ∨ False)))) → (p2 → (p2 → (p2 ∨ p4))))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Implications on the right can always be decomposed.
  intro h3
  -- Conjunctions on the left can always be decomposed.
  let h4 := h1.left
  let h5 := h1.right
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- One of the premise coincides with the conclusion.
  exact h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_614383501328903118806641261985 : (((((False ∨ ((((False ∨ p1) ∨ (p4 → False)) → ((p4 → ((p4 → (p2 ∨ p2)) → p4)) ∧ p5)) ∧ p1)) → ((p4 ∨ p5) ∧ True)) ∨ p5) ∨ False) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h2 =>
    -- False on the left can always be used.
    apply False.elim h2
  case inr h3 =>
    -- Conjunctions on the left can always be decomposed.
    let h4 := h3.left
    let h5 := h3.right
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- We want to use the implication h4 based on <expert-advice>. So we show its premise.
    have h6 : ((False ∨ p1) ∨ (p4 → False)) := by
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- One of the premise coincides with the conclusion.
      exact h5
    -- We have shown the premise of h4, we can now drive its conclusion.
    let h7 := h4 h6
    -- We need to get the right conjuct of h7 based on <expert-advice>.
    let h8 := h7.right
    -- One of the premise coincides with the conclusion.
    exact h8
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_317910543678295875460804457429 : (p4 ∨ ((p4 ∧ ((p4 → ((p5 ∧ ((p3 ∧ p3) ∨ (p2 ∨ p4))) ∧ (p4 ∨ ((p4 → (p1 ∧ p5)) ∧ p4)))) ∧ ((False ∧ p4) ∨ p3))) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_183864433603145319863757304631 : (((((p1 ∧ p2) ∧ (p3 ∧ p2)) ∨ (p1 ∧ (p1 → False))) ∧ p5) ∨ ((((p4 ∨ False) → (((p2 ∨ p5) ∨ p1) ∧ p1)) → (p2 ∧ False)) → True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_308605552601889689031928739809 : (p2 ∨ (((False ∨ p1) ∧ ((p5 → (((((p5 ∧ p5) → p1) ∨ True) ∨ p2) ∧ p2)) ∨ ((p1 → ((p4 ∨ p4) ∨ p5)) ∧ (p3 → p5)))) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_610328363073836349880176895250 : ((((((p4 → (((True ∨ (False ∨ ((((p3 ∨ p5) → ((True ∨ p1) → p2)) → False) → (False ∨ p3)))) ∨ False) → p5)) ∨ p2) → p4) ∨ True) ∨ p3) ∧ True) := by
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
theorem thm_5_vars_655541157699968320211154450356 : ((((((((((p4 → (p2 ∨ True)) ∧ p2) ∧ p3) → (True ∧ p5)) → ((p4 → p4) ∧ p2)) → (False ∨ p5)) → (p4 ∧ p2)) ∨ (p5 → p5)) ∨ p1) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- One of the premise coincides with the conclusion.
  exact h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_178405260822881728081115593128 : ((((p2 → False) ∨ ((True ∨ (p2 → False)) ∧ (p4 → p5))) → (p5 ∨ p1)) ∨ (p1 → ((((p4 ∨ (True ∧ (p1 → True))) → p4) ∨ p5) → p1))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
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
theorem thm_5_vars_354896751068458836468983858015 : (p5 → ((p4 ∧ ((p3 ∧ p2) → (((True → p3) ∧ ((False → ((((p3 ∧ (True ∧ p4)) ∧ p1) ∨ p1) ∨ False)) → p4)) ∧ (p5 → p4)))) ∨ True)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_187148557756026999776759738504 : (((False → p1) ∨ ((p4 → False) ∧ ((p1 ∧ p2) → (p1 ∨ True)))) → ((p3 ∨ (p4 → False)) ∨ (((p3 ∨ p1) ∧ p1) → (p1 ∨ (p1 → True))))) := by
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
    -- Disjunctions on the left can always be decomposed.
    cases h4
    case inl h6 =>
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
  case inr h10 =>
    -- Conjunctions on the left can always be decomposed.
    let h11 := h10.left
    let h12 := h10.right
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h13
    -- We want to use the implication h11 based on <expert-advice>. So we show its premise.
    have h14 : p4 := by
      -- One of the premise coincides with the conclusion.
      exact h13
    -- We have shown the premise of h11, we can now drive its conclusion.
    let h15 := h11 h14
    -- False on the left can always be used.
    apply False.elim h15



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_171504844748818175325473659187 : (((((((p3 ∨ p4) → ((p2 → (False ∧ p2)) ∧ True)) ∨ p1) ∨ p1) ∧ p5) ∨ True) ∨ ((False ∨ False) ∨ (p1 ∨ (((True ∨ p1) → p4) ∨ p4)))) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_160782873849824436681806243439 : ((((((p3 ∧ p4) → p2) ∨ p4) ∧ True) ∨ (((p3 → p4) → (False → (False → (False ∧ p1)))) ∧ True)) → ((True ∨ p4) → (p5 → (p3 ∨ p5)))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Implications on the right can always be decomposed.
  intro h3
  -- Disjunctions on the left can always be decomposed.
  cases h2
  case inl h4 =>
    -- Disjunctions on the left can always be decomposed.
    cases h1
    case inl h5 =>
      -- Conjunctions on the left can always be decomposed.
      let h6 := h5.left
      let h7 := h5.right
      -- Disjunctions on the left can always be decomposed.
      cases h6
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
    case inr h10 =>
      -- Conjunctions on the left can always be decomposed.
      let h11 := h10.left
      let h12 := h10.right
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- One of the premise coincides with the conclusion.
      exact h3
  case inr h13 =>
    -- Disjunctions on the left can always be decomposed.
    cases h1
    case inl h14 =>
      -- Conjunctions on the left can always be decomposed.
      let h15 := h14.left
      let h16 := h14.right
      -- Disjunctions on the left can always be decomposed.
      cases h15
      case inl h17 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- One of the premise coincides with the conclusion.
        exact h3
      case inr h18 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- One of the premise coincides with the conclusion.
        exact h3
    case inr h19 =>
      -- Conjunctions on the left can always be decomposed.
      let h20 := h19.left
      let h21 := h19.right
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- One of the premise coincides with the conclusion.
      exact h3



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_351930979143434443603703814261 : (p4 → (((True → ((False ∧ p5) → ((p5 → False) → p2))) ∨ p5) → (((False → (p3 ∨ (((p2 ∧ (False ∨ p1)) ∨ False) → p4))) → False) → p5))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Implications on the right can always be decomposed.
  intro h3
  -- Disjunctions on the left can always be decomposed.
  cases h2
  case inl h4 =>
    -- We want to use the implication h3 based on <expert-advice>. So we show its premise.
    have h5 : (False → (p3 ∨ (((p2 ∧ (False ∨ p1)) ∨ False) → p4))) := by
      -- Implications on the right can always be decomposed.
      intro h6
      -- False on the left can always be used.
      apply False.elim h6
    -- We have shown the premise of h3, we can now drive its conclusion.
    let h7 := h3 h5
    -- False on the left can always be used.
    apply False.elim h7
  case inr h8 =>
    -- One of the premise coincides with the conclusion.
    exact h8



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_148798877201313877436767164017 : ((((p4 ∧ (True ∧ (p1 ∨ p5))) ∧ p4) → (((p3 ∨ ((p5 ∧ (p4 → p5)) ∧ p5)) ∧ p5) ∨ (p5 ∨ p4))) ∨ ((p2 → p5) ∧ (p1 ∨ False))) := by
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
  let h6 := h5.left
  let h7 := h5.right
  -- Disjunctions on the left can always be decomposed.
  cases h7
  case inl h8 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h3
  case inr h9 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- One of the premise coincides with the conclusion.
    exact h9



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_1857644412640630261389711729 : (((((False → (True → p2)) ∧ (p3 → True)) ∧ True) → (((p3 ∧ (p1 ∨ (p1 → p5))) ∧ p2) ∧ (p1 ∧ p5))) → ((p4 ∧ p4) ∨ p3)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h2 : (((False → (True → p2)) ∧ (p3 → True)) ∧ True) := by
    -- Conjunctions on the right can always be decomposed.
    apply And.intro
    -- Conjunctions on the right can always be decomposed.
    apply And.intro
    -- Implications on the right can always be decomposed.
    intro h3
    -- Implications on the right can always be decomposed.
    intro h4
    -- False on the left can always be used.
    apply False.elim h3
    -- Implications on the right can always be decomposed.
    intro h5
    -- True on the right can always be proven directly.
    apply True.intro
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h6 := h1 h2
  -- We need to get the left conjuct of h6 based on <expert-advice>.
  let h7 := h6.left
  -- We need to get the left conjuct of h7 based on <expert-advice>.
  let h8 := h7.left
  -- We need to get the left conjuct of h8 based on <expert-advice>.
  let h9 := h8.left
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h9



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_197503727476385995284648996029 : (((p2 ∨ ((p1 ∧ False) ∧ p5)) ∧ (p4 ∧ False)) ∨ (((p1 ∨ False) → (((p3 → p5) → ((p1 ∨ p5) ∧ (p1 ∧ (p1 ∨ True)))) ∨ False)) ∨ p5)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h2 =>
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Implications on the right can always be decomposed.
    intro h3
    -- Conjunctions on the right can always be decomposed.
    apply And.intro
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- One of the premise coincides with the conclusion.
    exact h2
    -- Conjunctions on the right can always be decomposed.
    apply And.intro
    -- One of the premise coincides with the conclusion.
    exact h2
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- One of the premise coincides with the conclusion.
    exact h2
  case inr h4 =>
    -- False on the left can always be used.
    apply False.elim h4



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_442411470947023286613138681146 : (((((p2 ∨ (((p3 ∨ (((False ∧ (p5 → p5)) ∧ p4) ∧ p4)) ∧ ((p1 ∧ p4) ∨ p2)) ∨ (p3 ∨ p2))) ∨ True) ∨ ((True ∨ False) ∨ p1)) ∧ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
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
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_304993245716712048199543600614 : (p1 ∨ (((p3 → ((p4 → (p4 ∧ True)) ∧ (p3 ∧ (((p5 → p5) ∧ ((False → p4) → (p5 ∧ True))) ∨ p3)))) → p2) ∨ ((False ∧ False) ∨ True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_636239846663013694169196172443 : (((((p5 ∧ (p3 ∧ ((p4 → (p3 ∧ p4)) ∨ (p5 ∨ ((p3 ∧ p2) ∧ (p2 ∨ True)))))) ∨ ((p3 ∧ p2) → ((p1 ∨ p5) → p3))) → False) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_159272291376300264645113747663 : ((p4 → (((((p2 ∨ (p3 ∧ ((p3 → (p1 ∨ p1)) ∨ False))) ∨ True) ∨ False) ∨ (p4 → False)) → p3)) ∨ (((p1 ∧ p2) ∨ (True ∨ p1)) ∨ False)) := by
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
theorem thm_5_vars_158060902089051736317586400797 : (((True → (p4 → (p5 ∧ (p2 → False)))) ∨ (True → (p4 ∧ ((p3 → (p1 ∧ p3)) → (p4 ∧ False))))) ∨ (False → (((p2 ∧ p5) → p5) ∧ p5))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h2
  -- Conjunctions on the left can always be decomposed.
  let h3 := h2.left
  let h4 := h2.right
  -- False on the left can always be used.
  apply False.elim h1
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_82231266003011216032242325097 : ((((True → (((p5 ∧ ((p5 → p2) → (((False ∨ p2) ∨ p5) ∧ p1))) ∧ p3) ∧ (True ∨ p4))) ∧ p1) ∧ (p1 → ((p1 ∨ True) ∧ False))) → p2) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- Conjunctions on the left can always be decomposed.
  let h4 := h2.left
  let h5 := h2.right
  -- We want to use the implication h3 based on <expert-advice>. So we show its premise.
  have h6 : p1 := by
    -- One of the premise coincides with the conclusion.
    exact h5
  -- We have shown the premise of h3, we can now drive its conclusion.
  let h7 := h3 h6
  -- We need to get the right conjuct of h7 based on <expert-advice>.
  let h8 := h7.right
  -- False on the left can always be used.
  apply False.elim h8



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_149934429217326881855950938794 : ((p3 ∨ (((p2 ∨ True) → False) → (False ∧ (p1 ∨ ((p2 → ((p5 ∨ (False ∨ (False ∧ p2))) ∧ False)) ∨ True))))) ∨ (True ∧ ((p5 → p3) ∧ False))) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h2 : (p2 ∨ True) := by
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h3 := h1 h2
  -- False on the left can always be used.
  apply False.elim h3
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_180889429801951992791265632234 : ((((p4 → True) ∨ p5) → ((p4 ∧ True) ∧ ((p1 ∧ p2) ∧ (p1 ∧ True)))) → ((p1 ∨ (p3 ∨ ((p2 → p1) ∨ (True ∨ (p5 → p2))))) → p1)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Disjunctions on the left can always be decomposed.
  cases h2
  case inl h3 =>
    -- One of the premise coincides with the conclusion.
    exact h3
  case inr h4 =>
    -- Disjunctions on the left can always be decomposed.
    cases h4
    case inl h5 =>
      -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
      have h6 : ((p4 → True) ∨ p5) := by
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- Implications on the right can always be decomposed.
        intro h7
        -- True on the right can always be proven directly.
        apply True.intro
      -- We have shown the premise of h1, we can now drive its conclusion.
      let h8 := h1 h6
      -- We need to get the right conjuct of h8 based on <expert-advice>.
      let h9 := h8.right
      -- We need to get the left conjuct of h9 based on <expert-advice>.
      let h10 := h9.left
      -- We need to get the left conjuct of h10 based on <expert-advice>.
      let h11 := h10.left
      -- One of the premise coincides with the conclusion.
      exact h11
    case inr h12 =>
      -- Disjunctions on the left can always be decomposed.
      cases h12
      case inl h13 =>
        -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
        have h14 : ((p4 → True) ∨ p5) := by
          -- Show the left disjunct based on <expert-advice>.
          apply Or.inl
          -- Implications on the right can always be decomposed.
          intro h15
          -- True on the right can always be proven directly.
          apply True.intro
        -- We have shown the premise of h1, we can now drive its conclusion.
        let h16 := h1 h14
        -- We need to get the right conjuct of h16 based on <expert-advice>.
        let h17 := h16.right
        -- We need to get the left conjuct of h17 based on <expert-advice>.
        let h18 := h17.left
        -- We need to get the left conjuct of h18 based on <expert-advice>.
        let h19 := h18.left
        -- One of the premise coincides with the conclusion.
        exact h19
      case inr h20 =>
        -- Disjunctions on the left can always be decomposed.
        cases h20
        case inl h21 =>
          -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
          have h22 : ((p4 → True) ∨ p5) := by
            -- Show the left disjunct based on <expert-advice>.
            apply Or.inl
            -- Implications on the right can always be decomposed.
            intro h23
            -- True on the right can always be proven directly.
            apply True.intro
          -- We have shown the premise of h1, we can now drive its conclusion.
          let h24 := h1 h22
          -- We need to get the right conjuct of h24 based on <expert-advice>.
          let h25 := h24.right
          -- We need to get the left conjuct of h25 based on <expert-advice>.
          let h26 := h25.left
          -- We need to get the left conjuct of h26 based on <expert-advice>.
          let h27 := h26.left
          -- One of the premise coincides with the conclusion.
          exact h27
        case inr h28 =>
          -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
          have h29 : ((p4 → True) ∨ p5) := by
            -- Show the left disjunct based on <expert-advice>.
            apply Or.inl
            -- Implications on the right can always be decomposed.
            intro h30
            -- True on the right can always be proven directly.
            apply True.intro
          -- We have shown the premise of h1, we can now drive its conclusion.
          let h31 := h1 h29
          -- We need to get the right conjuct of h31 based on <expert-advice>.
          let h32 := h31.right
          -- We need to get the left conjuct of h32 based on <expert-advice>.
          let h33 := h32.left
          -- We need to get the left conjuct of h33 based on <expert-advice>.
          let h34 := h33.left
          -- One of the premise coincides with the conclusion.
          exact h34



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_861429357113889420306750596919 : (((((p5 ∧ (((p4 ∧ ((p4 → (p4 ∨ (((p4 → p4) ∧ False) ∧ True))) ∨ (p3 ∧ False))) ∧ p1) ∧ p5)) ∨ (False → (p3 → p3))) → p4) → p4) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h1
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h2 : ((p5 ∧ (((p4 ∧ ((p4 → (p4 ∨ (((p4 → p4) ∧ False) ∧ True))) ∨ (p3 ∧ False))) ∧ p1) ∧ p5)) ∨ (False → (p3 → p3))) := by
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h3
    -- Implications on the right can always be decomposed.
    intro h4
    -- False on the left can always be used.
    apply False.elim h3
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h5 := h1 h2
  -- One of the premise coincides with the conclusion.
  exact h5
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_345443636086326071267846945604 : (p3 → ((((False ∨ (p5 ∧ (p5 → (((p3 ∧ ((p5 ∨ (p2 ∧ p3)) ∧ p4)) → (p1 → (p1 ∧ p4))) ∧ p1)))) → p4) ∨ (p3 ∨ True)) ∨ True)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_166276503639548659429992766410 : ((p4 ∧ (((p2 ∧ (((((False ∧ True) → p1) ∧ (p4 ∨ p5)) → p4) ∨ p2)) ∨ p5) ∧ p5)) ∨ ((False → True) ∨ (((p4 ∨ p4) ∧ p1) ∧ p3))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_55145692211132646904557019460 : (((((p4 ∨ (p5 ∧ p2)) ∨ False) ∨ False) ∨ (p2 → ((((True ∧ p3) ∨ (True → p2)) ∧ (p5 ∧ ((p3 → (True ∨ p3)) ∧ p3))) ∨ False))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_228831688890093505548671229425 : ((p3 ∨ (True → p3)) ∨ (((((p3 → (p3 ∧ p2)) ∨ (False → p2)) ∨ (p1 ∨ (False ∧ p5))) → p3) ∨ (((p2 ∨ False) ∨ p5) ∨ (True ∨ p2)))) := by
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
theorem thm_5_vars_265535346373324238374290534304 : (True ∧ (False ∨ (((((p1 → False) → p3) ∨ False) → (False ∨ ((True → False) ∧ p3))) → ((p3 ∧ ((True ∨ ((p4 ∧ p4) ∧ p5)) → p5)) → p1)))) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Conjunctions on the left can always be decomposed.
  let h3 := h2.left
  let h4 := h2.right
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h5 : (((p1 → False) → p3) ∨ False) := by
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Implications on the right can always be decomposed.
    intro h6
    -- One of the premise coincides with the conclusion.
    exact h3
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h7 := h1 h5
  -- Disjunctions on the left can always be decomposed.
  cases h7
  case inl h8 =>
    -- False on the left can always be used.
    apply False.elim h8
  case inr h9 =>
    -- Conjunctions on the left can always be decomposed.
    let h10 := h9.left
    let h11 := h9.right
    -- We want to use the implication h10 based on <expert-advice>. So we show its premise.
    have h12 : True := by
      -- True on the right can always be proven directly.
      apply True.intro
    -- We have shown the premise of h10, we can now drive its conclusion.
    let h13 := h10 h12
    -- False on the left can always be used.
    apply False.elim h13



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_44756728079047268750397376298 : (((((True → (p4 → p4)) ∧ p4) → (((p3 ∧ p2) ∨ (((False ∨ p3) ∨ (True ∨ (p2 ∧ p1))) ∨ True)) ∨ ((p5 ∧ p2) ∨ p3))) → p5) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_667709409799689258230290217772 : ((((p4 ∧ (p1 ∧ ((p2 ∧ (p1 → (p1 → (p2 ∨ (p4 ∨ (p1 ∧ (False → ((p3 ∧ False) ∨ p1)))))))) → p1))) ∧ (p4 → (p3 ∨ p2))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_190502471957594153032729565491 : ((((p1 ∧ (((True → True) ∧ True) ∨ p3)) ∨ False) → p3) ∨ ((((((True → True) → p4) ∨ (p3 ∧ (p2 → p3))) ∧ p1) → p3) → (p4 ∨ True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_155194434608829722215889377044 : ((((p2 ∨ p2) → ((p1 ∧ False) ∨ (p5 → p5))) ∧ (False ∨ ((True ∨ (p5 ∧ p2)) → (False → p3)))) ∧ (True ∨ ((p4 ∧ False) → (p5 → p5)))) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h1
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h2 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h3
    -- One of the premise coincides with the conclusion.
    exact h3
  case inr h4 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h5
    -- One of the premise coincides with the conclusion.
    exact h5
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h6
  -- Implications on the right can always be decomposed.
  intro h7
  -- False on the left can always be used.
  apply False.elim h7
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_726179712282105164357390727660 : (((((p5 ∧ True) ∨ p1) ∨ ((((p2 ∧ ((True ∨ ((False ∨ p3) ∧ p5)) ∨ ((False ∨ p3) ∨ (p2 ∨ p3)))) ∧ p1) ∨ (True → True)) ∧ p5)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_190597344989739146488145070094 : ((((False ∨ p5) ∨ ((p1 ∨ p2) ∧ (p2 ∧ p3))) → p4) ∨ (((((p2 → p5) ∨ p5) ∧ ((False ∨ p1) ∨ False)) ∧ False) ∨ (p1 → (True ∧ True)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
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
theorem thm_5_vars_232488539894790374119637818243 : ((True ∧ (p5 ∨ p5)) → ((p4 → p4) → (((p4 ∨ p3) ∧ (p1 ∨ p4)) ∨ ((p3 → ((p1 ∧ (p2 ∨ (p2 → p3))) → p5)) → (p4 → p4))))) := by
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
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h6
    -- Implications on the right can always be decomposed.
    intro h7
    -- One of the premise coincides with the conclusion.
    exact h7
  case inr h8 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h9
    -- Implications on the right can always be decomposed.
    intro h10
    -- One of the premise coincides with the conclusion.
    exact h10



