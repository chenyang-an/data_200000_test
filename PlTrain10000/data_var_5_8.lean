variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_622758408504119148382751200032 : ((((p4 ∧ (p5 ∧ ((True → ((False ∧ p4) → (p2 → (True → ((p4 → p3) → (True ∧ (((False ∨ p2) → False) ∧ p3))))))) → p1))) ∨ p1) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_172332953694911778598578566185 : ((((p3 ∨ (p1 ∨ p3)) ∨ (p3 ∨ p1)) ∧ ((((p1 → p3) → p3) → p3) ∧ p5)) ∨ (((((p3 ∧ p3) ∧ p4) ∨ False) ∨ (p5 → p5)) ∨ p3)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_51223994724330178778448007446 : ((((p4 ∨ (True → ((p3 ∨ p2) ∨ False))) → ((((p2 ∨ (p3 ∨ p2)) ∧ p5) ∨ p1) ∨ False)) ∨ (p3 → ((p3 ∧ p5) → (True ∨ p3)))) ∨ p5) := by
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
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_345449098255978999371848591333 : (p3 → (((p2 ∧ (((p1 ∧ p5) ∧ ((p4 ∨ (True ∧ ((p4 ∧ p2) ∨ (p2 ∧ False)))) ∨ (p4 ∨ True))) → (True → False))) ∨ (p5 → False)) ∨ p3)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_66257196584223681887911718542 : ((p5 ∨ ((p5 → (True → (False ∧ p5))) ∨ (p2 ∨ (((False ∧ p2) ∧ (p2 ∨ p1)) ∨ (((p4 → (p3 → (p4 → True))) → True) ∨ p1))))) ∨ p2) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
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
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_713307209917906673049614212845 : ((((p5 ∨ ((p5 ∨ (p4 → p1)) → p4)) ∨ ((((p2 → p4) → ((p2 ∧ ((p3 → ((p2 ∧ False) ∧ p4)) ∧ p1)) ∨ p2)) → True) ∨ p1)) ∨ p3) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_255621385783006517329675130880 : ((p5 ∧ p4) → (((p3 ∨ (((((p5 ∨ (p1 ∧ p3)) ∨ ((p2 ∨ p3) → p3)) ∨ (p4 → p3)) ∨ True) → p3)) → p2) ∨ ((p1 ∨ p5) → p4))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h4
  -- Disjunctions on the left can always be decomposed.
  cases h4
  case inl h5 =>
    -- One of the premise coincides with the conclusion.
    exact h3
  case inr h6 =>
    -- One of the premise coincides with the conclusion.
    exact h3



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_165572591477028633046092121928 : (((((True ∨ p5) ∧ (p2 ∨ p2)) ∧ (True ∧ p1)) ∨ ((True ∨ p4) → (p3 ∧ (p4 → p3)))) ∨ (False ∨ (p2 ∨ ((p5 → True) ∨ (p1 ∨ False))))) := by
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
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_49713254120541917422341410628 : (((True ∧ (((p4 → (p4 → ((((p1 ∧ p2) ∨ p1) ∨ (p1 ∨ p5)) ∨ p4))) ∧ p1) ∨ ((p1 ∨ p5) ∧ True))) → ((False ∨ p3) ∧ p1)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_323258538041115337820200138541 : (p5 ∨ ((p4 ∧ ((p2 ∧ (p5 → False)) → ((p5 ∨ False) ∨ (p3 ∧ ((p3 ∧ (p1 → p3)) → ((False ∧ False) → (p5 ∨ p4))))))) ∨ (True ∨ p2))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_39952910999706884608260691888 : (((p4 → (((False → p4) → ((p5 ∨ (True ∨ (((True → True) ∨ p3) ∨ (p2 ∨ ((p5 ∧ p4) → (p2 → True)))))) → p2)) → False)) ∧ p5) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_114329905811372063136758902133 : (((True ∧ (p1 ∨ (((((p3 → True) ∨ (True ∧ False)) → (p5 ∧ (p2 ∨ p3))) ∨ False) ∨ False))) ∧ (True ∨ (False ∧ (p4 ∧ p2)))) ∨ (False → False)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_111898968001480475078569936463 : ((((((p3 ∨ ((True → True) → p2)) → ((p4 ∧ (p1 → False)) → p4)) ∧ True) → (((p2 → p4) → (p2 → p2)) ∧ False)) ∨ p3) ∨ (False → False)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_613025228883472461766555556585 : ((((((p2 ∨ ((False ∧ p3) → (((False ∨ ((False ∧ False) ∧ (((p1 ∨ False) ∨ p4) ∧ p4))) ∨ p3) ∨ p2))) ∧ p5) → (p3 → p1)) ∨ p4) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_157431356496916247937237824479 : (((False ∧ ((True → (False ∧ (True → ((p4 → p5) ∨ p1)))) ∨ (p4 → (p3 ∧ p1)))) ∧ (p4 ∨ p5)) ∨ (((p3 ∧ p4) ∧ p5) → (p5 ∨ p1))) := by
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
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- One of the premise coincides with the conclusion.
  exact h3



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_135818373636388239657173609732 : ((((p1 ∧ ((((p5 ∧ True) ∨ p3) → p1) ∧ (True ∨ p3))) ∨ p3) ∧ ((p4 → ((p5 ∨ True) ∧ (False ∨ True))) ∨ False)) ∨ ((True ∨ p3) ∨ p1)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_73019394375516975998340838920 : ((((((((False → True) ∧ ((p1 ∨ False) ∧ (p5 → (((p5 → p5) ∧ True) ∨ True)))) ∧ (p4 ∧ p3)) ∨ False) ∨ (True ∨ p2)) → p5) ∨ False) → p5) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h2 =>
    -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
    have h3 : (((((False → True) ∧ ((p1 ∨ False) ∧ (p5 → (((p5 → p5) ∧ True) ∨ True)))) ∧ (p4 ∧ p3)) ∨ False) ∨ (True ∨ p2)) := by
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
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
theorem thm_5_vars_218248463834869338281345603731 : (((False ∨ True) ∨ (p2 ∨ p4)) → ((p1 ∨ ((p5 ∧ p4) ∨ (False → (False ∧ True)))) ∨ (False ∧ ((p2 ∧ (p3 ∨ ((p2 ∧ p3) ∧ p4))) ∧ p5)))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h2 =>
    -- Disjunctions on the left can always be decomposed.
    cases h2
    case inl h3 =>
      -- False on the left can always be used.
      apply False.elim h3
    case inr h4 =>
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Implications on the right can always be decomposed.
      intro h5
      -- Conjunctions on the right can always be decomposed.
      apply And.intro
      -- False on the left can always be used.
      apply False.elim h5
      -- True on the right can always be proven directly.
      apply True.intro
  case inr h6 =>
    -- Disjunctions on the left can always be decomposed.
    cases h6
    case inl h7 =>
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Implications on the right can always be decomposed.
      intro h8
      -- Conjunctions on the right can always be decomposed.
      apply And.intro
      -- False on the left can always be used.
      apply False.elim h8
      -- True on the right can always be proven directly.
      apply True.intro
    case inr h9 =>
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Implications on the right can always be decomposed.
      intro h10
      -- Conjunctions on the right can always be decomposed.
      apply And.intro
      -- False on the left can always be used.
      apply False.elim h10
      -- True on the right can always be proven directly.
      apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_53553250876714404614466590685 : ((((p5 ∨ (((p4 → (True ∧ False)) ∨ p4) ∨ p3)) ∧ p1) ∧ (((p1 ∧ (p4 ∨ p2)) ∧ False) ∧ ((p3 ∨ (False → (p2 → p4))) ∧ p3))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_231347521184729599206580194891 : (((False → True) ∨ True) → ((((p1 ∨ (((p3 → p3) → ((p3 ∧ (p2 → False)) → p3)) ∧ (p5 → (True → p1)))) ∧ p5) ∨ True) ∨ (p4 ∧ p5))) := by
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
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_175135299701883623573108282770 : ((p5 ∧ ((p2 ∨ (((((p5 ∨ (p5 ∨ False)) ∧ True) → p5) ∨ p1) → p1)) → p1)) → ((p4 ∨ (False ∧ ((True → (p5 ∧ p2)) ∧ True))) ∨ p5)) := by
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
theorem thm_5_vars_710144583318125650729223938294 : ((((((False ∧ (p1 → False)) ∨ p4) ∨ p4) ∧ ((((((p1 ∧ p2) → p1) → (((True → p1) → (p4 ∧ p2)) ∨ p4)) ∧ p4) ∧ p2) → p5)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_777899685344723054362750073202 : (((p1 ∨ (((True ∧ p5) ∨ p3) ∧ (p5 → ((p3 ∧ ((((p3 ∨ (False ∧ p4)) → p4) ∧ (False ∨ ((True ∧ True) → p4))) → p3)) ∨ p1)))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_245180501836458315702765064598 : ((p2 ∧ False) ∨ (((False → ((((p4 ∧ True) → ((p4 ∨ p5) ∧ p3)) ∨ (p2 → p1)) → p3)) → p5) → (p4 → (p5 ∨ ((False ∧ p2) ∧ p2))))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h3 : (False → ((((p4 ∧ True) → ((p4 ∨ p5) ∧ p3)) ∨ (p2 → p1)) → p3)) := by
    -- Implications on the right can always be decomposed.
    intro h4
    -- Implications on the right can always be decomposed.
    intro h5
    -- Disjunctions on the left can always be decomposed.
    cases h5
    case inl h6 =>
      -- False on the left can always be used.
      apply False.elim h4
    case inr h7 =>
      -- False on the left can always be used.
      apply False.elim h4
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h8 := h1 h3
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- One of the premise coincides with the conclusion.
  exact h8



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_745011379614075590523086194314 : ((((p4 ∧ p1) → (((False ∨ False) ∧ (((True ∧ (p4 ∧ (p2 ∨ p3))) → (p3 ∨ p3)) ∨ False)) ∨ (((True → True) → p4) ∧ (p3 → p4)))) ∨ p5) ∧ True) := by
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
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h4
  -- One of the premise coincides with the conclusion.
  exact h2
  -- Implications on the right can always be decomposed.
  intro h5
  -- One of the premise coincides with the conclusion.
  exact h2
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_191145420144643258908694134431 : ((((p4 ∨ p4) ∨ p5) ∨ (p1 ∧ ((False ∨ p3) ∨ True))) ∨ (p2 ∨ (p5 → (False → ((p5 ∨ ((p4 ∧ ((p5 ∨ True) ∨ True)) ∧ p5)) ∧ p5))))) := by
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
  -- False on the left can always be used.
  apply False.elim h2
  -- False on the left can always be used.
  apply False.elim h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_198152926422524203033765475647 : (((True ∨ True) → (False ∨ ((p5 ∨ p2) ∧ p5))) ∨ ((p4 ∨ False) ∨ (((p2 ∧ ((((p3 ∧ (False → False)) ∨ p5) → p1) ∧ p3)) ∨ True) ∨ p4))) := by
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
theorem thm_5_vars_68799888576179093517865357061 : ((p4 → (((p1 ∧ (p3 → p1)) ∨ p1) ∧ (((((((p2 → False) ∨ False) → p4) ∨ (p2 ∧ ((p4 → p1) ∨ p5))) ∨ p3) → True) → p5))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_710138561322168190724954733235 : (((((((True ∧ False) → p2) ∨ p5) ∨ True) ∧ (p2 → (((p3 → (p3 ∧ ((((False ∨ p5) ∨ True) ∨ p4) → False))) → p1) ∨ (p2 ∨ True)))) ∨ p1) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
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
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_783793395798829466296963984295 : (((p3 ∨ (((p2 → (p5 ∧ p4)) → p2) ∨ (((((p1 ∧ p5) → True) ∧ ((p4 ∨ p2) → (True → True))) ∨ p5) ∨ ((p1 ∨ p4) ∨ p3)))) ∨ False) ∧ True) := by
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
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro
  -- Implications on the right can always be decomposed.
  intro h2
  -- Implications on the right can always be decomposed.
  intro h3
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_53738442009925442790667639293 : (((p4 → ((False → (p5 ∧ ((p2 → p4) ∧ False))) → p1)) ∧ (p4 → ((((p2 → True) ∧ p5) → (False ∧ False)) ∨ (p4 → (True → p5))))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_40810004233769486290983981951 : ((((p2 ∨ (((p5 ∨ (p2 → p2)) → p3) → (p3 → (((p3 ∧ (False → p4)) ∨ True) ∨ ((p3 → (p5 ∨ p4)) ∧ p3))))) → p3) ∨ p2) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_134924737912506947579641529090 : (((((p4 → ((p5 ∧ ((p4 ∧ p1) ∨ ((True → (p2 ∨ p5)) ∨ (p3 → p5)))) ∧ p1)) ∧ p5) → False) ∧ (False ∨ False)) ∨ ((p1 ∨ False) → True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_255972457101165409031290119760 : ((True ∨ p3) → (((p5 ∧ False) ∨ (((((((p3 ∨ (True ∧ p4)) ∨ p3) ∨ p4) ∧ (True ∨ False)) ∧ (p2 → p1)) ∧ (p3 ∨ p5)) → p3)) ∨ True)) := by
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
theorem thm_5_vars_138012011573725493568146580992 : ((True → ((p2 ∨ ((p5 ∧ p5) ∧ (((((p5 → p3) ∧ p5) → p3) ∨ p1) ∧ (p3 ∨ (p4 ∧ (p1 → p1)))))) ∧ p1)) ∨ ((False ∧ p3) → p4)) := by
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
theorem thm_5_vars_60034904456245861281116085178 : (((p1 ∨ p3) → (p1 ∨ ((((p5 ∧ False) ∧ p1) ∨ p1) ∧ (((((p5 → p4) → p1) ∨ p1) ∧ p2) → ((p4 → p1) ∧ (p1 ∨ p5)))))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_65470950691371316908722593590 : ((p3 ∨ (False ∧ (((p3 ∨ (((p3 ∧ p5) ∧ ((p3 ∧ (p2 ∨ (p5 ∨ p5))) → p3)) ∧ p3)) ∧ (p3 → p2)) ∨ (p4 ∧ (p2 ∧ p1))))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_126773978082926363015351121737 : ((p4 ∧ (p2 → (p1 ∧ ((p5 ∧ (False → p3)) ∧ (False ∧ (p4 → ((False ∨ True) → ((p3 ∨ (False ∨ (True → p2))) ∧ True)))))))) → (p5 ∨ True)) := by
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
theorem thm_5_vars_41241329857837183376586427780 : ((((p5 → (((p4 → p2) → (p3 → (((p3 ∧ (False ∨ p1)) ∧ p5) ∧ (p4 → p2)))) ∨ True)) ∧ (((p3 → p2) ∧ p2) ∨ p5)) ∨ True) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_595646157929640520670915356297 : ((((((p2 ∧ p5) ∨ (p5 → (False ∨ (p2 ∨ ((p1 → p5) ∧ p3))))) → ((p5 → p5) ∧ (p1 ∨ (((p2 ∧ p5) ∨ p5) ∨ p5)))) ∧ p2) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_698288462361110419899870255941 : ((((((False ∨ (p4 → ((p5 ∨ p3) → False))) → p3) ∧ (False ∧ p3)) ∨ (((False → True) ∧ (True ∧ (False → True))) ∨ ((p2 ∧ p4) ∨ p3))) ∨ p3) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- Implications on the right can always be decomposed.
  intro h2
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_135839056064507270171335102431 : ((((p5 → p4) → ((p3 ∧ (True ∨ (p5 → False))) → (p5 ∧ p5))) ∧ (((p5 → p3) ∧ (False → p5)) → (p3 → p5))) ∨ (True ∨ (False → p1))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_207788091886411332582266226726 : (((True → ((False → p4) ∨ p3)) → False) → ((p5 → (((p5 ∨ True) ∧ (p4 → p5)) → (((p3 ∧ (False → True)) ∧ True) ∨ False))) ∨ (False ∧ p3))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h2 : (True → ((False → p4) ∨ p3)) := by
    -- Implications on the right can always be decomposed.
    intro h3
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Implications on the right can always be decomposed.
    intro h4
    -- False on the left can always be used.
    apply False.elim h4
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h5 := h1 h2
  -- False on the left can always be used.
  apply False.elim h5



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_299268007329891523134808030049 : (False ∨ (((((False ∨ (p5 → ((((True → True) ∧ True) ∨ p1) → (True ∧ False)))) → p3) ∧ False) ∨ (p3 ∧ (p4 ∧ (p2 ∧ (True ∧ False))))) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_41505491301593862507448744619 : ((((True ∨ (True ∨ (p4 ∧ ((False ∨ p3) ∨ ((p2 → p2) → True))))) → (p2 ∨ (False ∨ (p1 ∨ (p4 → (True ∧ (True ∨ p5))))))) ∨ p3) ∨ p1) := by
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
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h3
    -- Conjunctions on the right can always be decomposed.
    apply And.intro
    -- True on the right can always be proven directly.
    apply True.intro
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
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
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Implications on the right can always be decomposed.
      intro h6
      -- Conjunctions on the right can always be decomposed.
      apply And.intro
      -- True on the right can always be proven directly.
      apply True.intro
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- True on the right can always be proven directly.
      apply True.intro
    case inr h7 =>
      -- Conjunctions on the left can always be decomposed.
      let h8 := h7.left
      let h9 := h7.right
      -- Disjunctions on the left can always be decomposed.
      cases h9
      case inl h10 =>
        -- Disjunctions on the left can always be decomposed.
        cases h10
        case inl h11 =>
          -- False on the left can always be used.
          apply False.elim h11
        case inr h12 =>
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- Implications on the right can always be decomposed.
          intro h13
          -- Conjunctions on the right can always be decomposed.
          apply And.intro
          -- True on the right can always be proven directly.
          apply True.intro
          -- Show the left disjunct based on <expert-advice>.
          apply Or.inl
          -- True on the right can always be proven directly.
          apply True.intro
      case inr h14 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- Implications on the right can always be decomposed.
        intro h15
        -- Conjunctions on the right can always be decomposed.
        apply And.intro
        -- True on the right can always be proven directly.
        apply True.intro
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- True on the right can always be proven directly.
        apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_620106097824571028767885105310 : (((((False ∧ True) ∨ (((((p3 ∧ (((p5 ∨ p1) ∧ True) ∨ True)) ∧ False) ∨ ((False ∧ (p2 → p3)) → p3)) → False) ∨ (True ∨ p2))) ∨ p5) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_193555438404167616076845520138 : (((p5 ∧ False) → (True → ((p5 ∨ (p5 → p2)) → p5))) → ((p3 ∧ (True ∧ ((p4 → True) → p4))) → (p4 ∨ (p3 → ((p2 ∨ p2) ∧ p1))))) := by
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
  -- We want to use the implication h6 based on <expert-advice>. So we show its premise.
  have h7 : (p4 → True) := by
    -- Implications on the right can always be decomposed.
    intro h8
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h6, we can now drive its conclusion.
  let h9 := h6 h7
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- One of the premise coincides with the conclusion.
  exact h9



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_164800480142554991127158714148 : (((((p3 → p1) ∧ True) ∨ (((p2 ∧ (False ∧ p5)) ∧ p3) ∧ (p4 ∧ (p2 ∧ True)))) ∨ p3) ∨ (((p1 ∨ (False → (p5 → False))) → p3) → p3)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h2 : (p1 ∨ (False → (p5 → False))) := by
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



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_178951657271867739651928575132 : (((p5 ∧ p2) ∨ (p3 ∨ ((False → (((p4 → p3) ∧ True) → True)) → p2))) ∨ (((False → p4) ∧ (True ∧ False)) → ((p5 ∧ p2) ∨ (p5 ∧ p1)))) := by
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
  -- False on the left can always be used.
  apply False.elim h5



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_3405517101294442816202093977 : ((p5 → p1) → ((p1 → ((p1 ∧ (((p5 → (p3 ∧ (True ∧ p4))) → (p5 → ((p5 ∨ True) → p2))) ∨ p1)) ∨ p3)) ∨ (p2 ∨ p4))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h2
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- One of the premise coincides with the conclusion.
  exact h2
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_774075559375954146333298633490 : (((False ∨ ((((True → (p1 → (p3 ∨ True))) → p3) → ((p1 → (p1 ∧ (p3 ∧ ((True ∧ p2) ∧ False)))) ∨ (True ∨ p3))) ∨ (p1 → p3))) ∨ p4) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
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
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_178011899779901738857794639811 : (((p5 ∨ ((True ∨ True) ∧ ((p5 ∨ (p3 ∧ (p2 ∨ p5))) ∨ p3))) ∨ True) ∨ (False ∧ (((p4 ∨ (((False ∨ p1) ∨ p3) ∨ p2)) → p1) → p1))) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_48175505565789209668408657681 : ((((p3 → p3) ∧ ((p2 ∨ p2) ∨ ((p2 ∨ p2) ∧ ((True ∧ True) ∨ (((p4 → p4) ∨ (p2 → (p5 → p2))) → p5))))) → (False ∨ p2)) ∨ False) := by
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
    -- Disjunctions on the left can always be decomposed.
    cases h4
    case inl h5 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- One of the premise coincides with the conclusion.
      exact h5
    case inr h6 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- One of the premise coincides with the conclusion.
      exact h6
  case inr h7 =>
    -- Conjunctions on the left can always be decomposed.
    let h8 := h7.left
    let h9 := h7.right
    -- Disjunctions on the left can always be decomposed.
    cases h8
    case inl h10 =>
      -- Disjunctions on the left can always be decomposed.
      cases h9
      case inl h11 =>
        -- Conjunctions on the left can always be decomposed.
        let h12 := h11.left
        let h13 := h11.right
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- One of the premise coincides with the conclusion.
        exact h10
      case inr h14 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- One of the premise coincides with the conclusion.
        exact h10
    case inr h15 =>
      -- Disjunctions on the left can always be decomposed.
      cases h9
      case inl h16 =>
        -- Conjunctions on the left can always be decomposed.
        let h17 := h16.left
        let h18 := h16.right
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- One of the premise coincides with the conclusion.
        exact h15
      case inr h19 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- One of the premise coincides with the conclusion.
        exact h15



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_42684938711097666767412972832 : (((p5 ∨ (((p5 ∨ p2) ∧ ((p1 ∧ (p3 ∨ p1)) → ((p3 ∨ ((p3 → p1) → p2)) ∨ ((p4 → (p2 ∨ p4)) ∧ p5)))) ∧ True)) ∨ True) ∨ p5) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_133981592343161679855438281197 : ((((((((p2 ∨ False) ∨ ((False ∨ (p4 ∨ (p2 ∨ (p5 ∧ p2)))) → (p2 ∨ False))) ∧ p1) ∨ False) → False) ∧ p3) ∨ p4) ∨ (p2 → (p1 ∨ True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_258761684479333494830645565320 : ((True → False) → ((p5 ∨ (p2 ∧ ((p3 ∧ ((((p5 ∨ True) → p3) → p1) ∨ (True → p1))) → ((False ∨ ((p3 ∧ p4) → p2)) ∨ p5)))) ∧ False)) := by
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
theorem thm_5_vars_54580293507051210464463811141 : (((p2 ∨ (((p3 → False) → True) → (False ∧ p4))) ∨ ((p4 → (True ∨ ((False ∨ p5) → p5))) ∧ ((p3 ∨ (p1 ∧ (False ∨ True))) ∨ True))) ∨ p3) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_319392070415913795043854949002 : (p4 ∨ ((((p4 ∧ ((p2 ∧ ((p1 ∧ p1) → p2)) ∧ (False ∨ p5))) ∧ p4) → p5) → (((True ∧ p1) ∨ ((p5 ∨ p4) ∨ (False ∨ True))) ∨ p2))) := by
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



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_47391480403005213005108839779 : ((((p2 → p3) → ((p2 → p4) → (((p5 ∨ (((True → p2) ∧ (True → (True ∨ (True ∨ False)))) → p5)) → p1) → p1))) ∨ (p2 → p5)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_65333445824225865369089969588 : ((p3 ∨ (((p4 ∨ p2) ∨ ((p3 ∨ (p2 ∨ (p3 ∧ (((False → (False ∧ False)) → True) → p4)))) → False)) ∨ (p4 → (True ∨ (True ∨ p2))))) ∨ p2) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_55484435937433724330119976308 : ((((p4 ∨ (True ∧ p4)) ∨ (p5 ∨ False)) → ((p4 ∨ (((((p1 → (True ∧ p3)) ∧ p3) → p2) ∨ ((True ∨ p3) → p1)) ∨ p1)) ∨ p2)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_197438531062608158246500134485 : ((((False ∨ (p5 ∧ p4)) ∧ p4) ∧ (p2 ∨ p4)) ∨ ((True ∨ (False ∨ p4)) ∨ (((((p3 ∨ p3) ∨ p4) ∧ p5) → ((p1 → p3) ∨ False)) ∨ p3))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_58103644315284509656600174051 : (((p1 ∧ p3) ∧ ((((p4 ∨ True) ∨ (True → p4)) ∧ ((p3 ∨ (p2 → (p5 ∧ (p5 → True)))) ∧ (False ∨ p4))) → (p1 ∧ (p5 ∨ p1)))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_58348717489857434109566557132 : (((False ∨ p4) ∧ (p4 → ((p4 ∧ ((p2 ∧ p1) ∧ (p4 ∧ False))) ∨ (p4 → (p1 ∧ (p3 ∨ (False → ((p3 ∧ (p2 ∧ True)) → p2)))))))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_610578303416377733802598580312 : ((((((((((False ∧ True) ∧ (p1 ∧ (p5 ∧ (((p3 ∨ p5) → True) → p5)))) → p1) ∨ False) ∧ (p1 ∧ p5)) ∨ (p2 ∨ False)) → p3) ∨ False) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_191320531094508017816655558000 : (((False ∧ p3) ∨ ((p5 ∧ (p4 ∧ (p1 → False))) ∧ False)) ∨ ((((p2 ∨ (p1 ∧ (p4 ∧ False))) → True) ∨ p3) ∨ ((p1 ∨ p3) → (True ∨ False)))) := by
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
theorem thm_5_vars_623563894746587714350704775411 : ((((False ∨ (True ∧ (((p4 → ((p3 → p4) → p5)) ∧ p5) ∧ ((p1 ∧ (((p5 ∧ (p3 ∨ p1)) ∨ (p5 ∨ True)) → p4)) ∧ p2)))) ∨ p2) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_301629274901428504064263515325 : (False ∨ ((False ∨ (p2 ∧ p3)) → (((p4 → (p1 ∨ (p1 ∧ (p1 → (((p5 ∧ (((p3 ∨ p3) ∧ p1) ∨ p4)) → p4) ∨ p5))))) → p1) ∨ p3))) := by
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
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h5



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_314243238789672190574494529211 : (p3 ∨ ((((p4 ∧ ((p3 → (True → False)) → (((((p3 ∧ p4) ∧ False) → False) ∨ p5) ∧ p3))) ∧ p3) → (p5 → False)) ∨ (True ∨ (p1 ∧ p5)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_246764293141004651609876785959 : ((p5 ∧ p5) ∨ ((((p3 ∨ (p4 → (p3 → p1))) ∨ p3) ∨ p1) ∨ (p5 → (False ∨ (((p5 ∧ False) ∧ ((False ∧ (p1 ∧ False)) ∨ p2)) → p4))))) := by
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
  -- False on the left can always be used.
  apply False.elim h6



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_55292224269410341014472411340 : (((p2 ∧ (p2 ∨ (p3 ∨ (False ∧ p2)))) ∨ (((p1 → p4) → ((p2 → ((p3 ∧ p4) → p2)) → True)) ∨ ((p5 ∨ (p1 ∧ p2)) → p5))) ∨ p4) := by
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
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_54129088834633978533093557475 : (((p2 ∨ ((p4 ∧ (True → (p2 ∨ (False → p2)))) ∧ False)) → ((False ∧ (((p1 ∨ p3) ∧ (p4 → p1)) ∧ p5)) ∨ ((False ∧ p5) ∧ p3))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_41270184350940850303947299948 : ((((True → (False ∨ ((p2 ∧ True) ∧ (False → (True → ((((True → p2) ∧ p5) ∧ True) → p4)))))) ∨ ((True → (p5 ∨ p5)) ∧ False)) ∨ True) ∨ p1) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_798065388302625657965409881159 : (((p1 → (((p4 ∨ p2) ∧ (False ∨ (((p2 ∨ (((p1 → p3) ∧ ((p4 ∧ p5) ∨ p2)) → p5)) → False) ∨ p4))) ∨ ((p1 ∧ p4) → p2))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_255936763846200251013379692906 : ((True ∨ p2) → ((p1 ∨ (((p5 ∨ p5) ∧ p4) ∧ p2)) → (((p5 → (((p2 → p3) ∨ p5) → (((p5 ∧ False) → True) ∧ p1))) ∧ True) → p1))) := by
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
    -- Disjunctions on the left can always be decomposed.
    cases h1
    case inl h7 =>
      -- One of the premise coincides with the conclusion.
      exact h6
    case inr h8 =>
      -- One of the premise coincides with the conclusion.
      exact h6
  case inr h9 =>
    -- Conjunctions on the left can always be decomposed.
    let h10 := h9.left
    let h11 := h9.right
    -- Conjunctions on the left can always be decomposed.
    let h12 := h10.left
    let h13 := h10.right
    -- Disjunctions on the left can always be decomposed.
    cases h12
    case inl h14 =>
      -- Disjunctions on the left can always be decomposed.
      cases h1
      case inl h15 =>
        -- We want to use the implication h4 based on <expert-advice>. So we show its premise.
        have h16 : p5 := by
          -- One of the premise coincides with the conclusion.
          exact h14
        -- We have shown the premise of h4, we can now drive its conclusion.
        let h17 := h4 h16
        -- We want to use the implication h17 based on <expert-advice>. So we show its premise.
        have h18 : ((p2 → p3) ∨ p5) := by
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- One of the premise coincides with the conclusion.
          exact h14
        -- We have shown the premise of h17, we can now drive its conclusion.
        let h19 := h17 h18
        -- We need to get the right conjuct of h19 based on <expert-advice>.
        let h20 := h19.right
        -- One of the premise coincides with the conclusion.
        exact h20
      case inr h21 =>
        -- We want to use the implication h4 based on <expert-advice>. So we show its premise.
        have h22 : p5 := by
          -- One of the premise coincides with the conclusion.
          exact h14
        -- We have shown the premise of h4, we can now drive its conclusion.
        let h23 := h4 h22
        -- We want to use the implication h23 based on <expert-advice>. So we show its premise.
        have h24 : ((p2 → p3) ∨ p5) := by
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- One of the premise coincides with the conclusion.
          exact h14
        -- We have shown the premise of h23, we can now drive its conclusion.
        let h25 := h23 h24
        -- We need to get the right conjuct of h25 based on <expert-advice>.
        let h26 := h25.right
        -- One of the premise coincides with the conclusion.
        exact h26
    case inr h27 =>
      -- Disjunctions on the left can always be decomposed.
      cases h1
      case inl h28 =>
        -- We want to use the implication h4 based on <expert-advice>. So we show its premise.
        have h29 : p5 := by
          -- One of the premise coincides with the conclusion.
          exact h27
        -- We have shown the premise of h4, we can now drive its conclusion.
        let h30 := h4 h29
        -- We want to use the implication h30 based on <expert-advice>. So we show its premise.
        have h31 : ((p2 → p3) ∨ p5) := by
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- One of the premise coincides with the conclusion.
          exact h27
        -- We have shown the premise of h30, we can now drive its conclusion.
        let h32 := h30 h31
        -- We need to get the right conjuct of h32 based on <expert-advice>.
        let h33 := h32.right
        -- One of the premise coincides with the conclusion.
        exact h33
      case inr h34 =>
        -- We want to use the implication h4 based on <expert-advice>. So we show its premise.
        have h35 : p5 := by
          -- One of the premise coincides with the conclusion.
          exact h27
        -- We have shown the premise of h4, we can now drive its conclusion.
        let h36 := h4 h35
        -- We want to use the implication h36 based on <expert-advice>. So we show its premise.
        have h37 : ((p2 → p3) ∨ p5) := by
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- One of the premise coincides with the conclusion.
          exact h27
        -- We have shown the premise of h36, we can now drive its conclusion.
        let h38 := h36 h37
        -- We need to get the right conjuct of h38 based on <expert-advice>.
        let h39 := h38.right
        -- One of the premise coincides with the conclusion.
        exact h39



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_245421297471392493996429418079 : ((p2 ∧ p4) ∨ ((((True → (p2 ∨ (p5 → p4))) ∧ p3) ∨ ((((p3 → p2) ∨ p2) → False) ∧ (p5 ∧ True))) ∨ ((True → False) ∨ (p5 ∨ True)))) := by
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
theorem thm_5_vars_66496015766016928859392200647 : ((True → (((p1 → (False ∧ p1)) → ((p5 → (((((True ∧ ((p1 ∨ True) ∧ (True ∨ p2))) ∧ False) → p2) ∧ False) ∧ p3)) → p1)) ∨ True)) ∨ False) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_117034751434283901932561564501 : (((p3 ∨ False) → ((((p3 ∨ (((p5 → p5) → True) ∧ p1)) ∨ p3) → ((p1 ∨ (True → (p4 → (True → False)))) ∧ False)) ∧ p2)) ∨ (False → False)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_313182772112842472841906113341 : (p3 ∨ ((((p1 ∨ (p3 → p1)) ∧ (p4 ∨ True)) ∧ ((((p5 ∨ True) ∧ p3) → ((False → (((p3 ∧ p2) ∧ p1) → p1)) ∨ p4)) ∧ p4)) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_703872017362866490059079925123 : (((((((p4 ∨ p1) ∧ p5) ∨ ((p2 ∨ p2) → p4)) ∨ p4) → ((True ∧ (((p4 → p2) → p5) ∨ (p4 ∧ (p5 → p1)))) ∨ (p2 ∨ True))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_47756002900980528118701314165 : (((((p4 ∨ p5) ∨ ((False ∧ ((p3 → (False ∧ (p2 ∧ p3))) ∨ p5)) ∨ ((p5 → True) ∨ (p3 → (p2 ∧ p2))))) ∨ p5) → (p1 ∨ p3)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_112544376069313029124827894558 : ((((((p3 → p5) ∧ (p5 ∨ (p2 ∨ True))) ∧ (False ∧ (p2 ∧ (p4 → (p4 → (p1 ∧ ((p2 → True) → p1))))))) → p4) → p2) ∨ (False → p4)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_316369194034295448415949836942 : (p3 ∨ (False ∨ ((p2 ∨ (False ∨ (p4 → (((((p1 ∧ False) ∧ p1) ∨ (True ∨ p3)) ∨ (p1 ∧ p4)) ∨ (p1 ∨ ((p2 ∨ True) ∧ p4)))))) ∨ True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_354876006475290128717216193767 : (p5 → ((p1 ∧ ((((((p1 ∨ (p4 → p2)) ∧ False) ∧ (((False → ((True → p5) ∧ False)) ∧ (p4 ∨ p2)) ∧ p2)) ∨ p3) ∨ p1) ∧ False)) ∨ p5)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_116466494377784003881976032331 : (((False ∧ p3) ∧ (((((p2 ∨ (False → ((p2 ∧ (p1 → (p4 → p2))) → p3))) ∨ p4) ∧ False) ∧ (p1 → (False → p1))) ∨ p5)) ∨ (p4 → True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_46888921149438908314028289570 : ((((((p5 ∨ p3) ∧ (((True ∨ True) ∧ p5) → ((p1 ∨ (False ∧ p3)) → (p2 → (p2 ∧ (p2 ∨ p2)))))) ∨ p4) ∨ p1) ∨ (False ∨ True)) ∨ p2) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_636727149726117845788704715733 : (((((p3 ∧ ((p3 ∨ False) ∧ (((True ∨ p2) → (p5 → p3)) ∨ (p1 → True)))) ∨ (False ∨ (p2 ∨ (p5 ∧ (p5 → (p5 → p1)))))) → p5) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_750771911247755801696124552937 : (((True ∧ (((((p1 → (p2 → ((p4 ∨ p3) ∧ p4))) ∧ True) → p4) ∨ p4) ∨ (False ∧ (True ∨ (((p4 → p2) → (p4 ∧ p3)) ∧ p2))))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_321195033457159418273371887783 : (p4 ∨ (p3 ∨ ((True ∧ ((((p2 ∨ p1) ∨ True) → (p1 ∧ p2)) → False)) ∨ ((True → ((p1 ∨ p3) ∧ p4)) → (False → ((p3 ∧ p4) → p4)))))) := by
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
  -- Implications on the right can always be decomposed.
  intro h3
  -- Conjunctions on the left can always be decomposed.
  let h4 := h3.left
  let h5 := h3.right
  -- False on the left can always be used.
  apply False.elim h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_323241778817780445712954515241 : (p5 ∨ (((p1 ∨ p4) ∧ ((((p4 → p5) → (p1 ∧ ((p3 ∧ (False ∨ p1)) ∨ p2))) → p1) ∧ ((True → p3) ∧ (p2 → p3)))) ∨ (False → p2))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_928651224742474150567098562715 : ((((p3 → (p3 ∨ ((p4 ∧ ((p3 → p5) ∧ p2)) ∨ p4))) ∧ (((False ∨ p5) ∨ ((False ∨ p5) ∨ (True ∨ (p2 ∧ p3)))) → (True → p3))) → p3) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- We want to use the implication h3 based on <expert-advice>. So we show its premise.
  have h4 : ((False ∨ p5) ∨ ((False ∨ p5) ∨ (True ∨ (p2 ∧ p3)))) := by
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h3, we can now drive its conclusion.
  let h5 := h3 h4
  -- We want to use the implication h5 based on <expert-advice>. So we show its premise.
  have h6 : True := by
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h5, we can now drive its conclusion.
  let h7 := h5 h6
  -- One of the premise coincides with the conclusion.
  exact h7
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_650769307306821957788175040420 : (((((False ∧ (p5 ∨ ((True → False) → (False → p1)))) ∧ ((p1 ∨ p1) → ((p5 ∧ p5) ∧ ((p5 ∧ (False ∨ p3)) ∧ p1)))) ∧ (p2 → p3)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_137806794530547123290558114229 : ((p2 ∨ (p4 → ((p2 ∧ ((p2 ∨ p1) ∨ ((((p4 ∧ (True ∧ p2)) → p5) ∧ p3) → (p5 ∧ False)))) ∨ (p2 → p3)))) ∨ (p1 → (False ∨ True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_191121160230043748202494183705 : (((p5 ∨ (p1 ∨ p1)) ∧ (p2 → (p1 ∨ (p4 ∧ True)))) ∨ (((p2 ∨ ((p3 → False) ∧ (p3 ∧ (True ∨ p5)))) ∨ (p1 ∨ (p1 → p5))) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_244050298395598350707435151695 : ((True ∧ p2) ∨ (False ∨ (p5 ∨ (((p5 → p4) → (((p3 ∧ (p1 ∧ (((p4 → (p1 → p1)) ∨ p5) ∨ False))) ∨ p3) → p4)) ∨ (p3 → p3))))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
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
theorem thm_5_vars_705911058855242317687792107268 : (((((p3 ∧ (p4 ∨ p2)) ∨ (False ∧ (p2 → p3))) ∧ (True → ((p1 ∧ (p3 → p5)) → ((p5 → p2) ∧ ((False ∨ (True ∧ True)) → p2))))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_42391637115447806114113238459 : (((p4 ∧ ((p2 → (p4 → True)) ∧ (p3 ∨ ((p1 ∧ (True ∧ (((True → p2) ∧ ((p2 ∨ False) → p5)) ∧ (True ∧ True)))) ∨ p1)))) ∨ p4) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_650055821331874427217810519023 : ((((((p3 → (((((p5 ∨ p3) ∧ p1) ∨ (p1 → p2)) ∨ (True ∨ p2)) ∨ p5)) ∧ (p4 ∨ p3)) → ((p1 ∧ False) ∨ p1)) ∧ (p4 ∧ p1)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_113636619193926928815912646514 : (((p5 → ((p4 → ((((((p1 ∨ False) ∨ (True → p5)) ∨ p1) → False) ∧ False) ∧ p2)) ∧ (p4 → (p2 ∧ p3)))) ∨ (True ∨ p4)) ∨ (p3 → False)) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_653786850089224292934022697825 : ((((((((p2 ∨ p3) ∧ p4) ∧ ((True ∧ p4) → (p3 → (p2 → (p5 ∨ False))))) ∧ (((p3 ∨ p2) ∨ True) ∨ True)) ∧ True) ∨ (True ∧ True)) ∨ p3) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



