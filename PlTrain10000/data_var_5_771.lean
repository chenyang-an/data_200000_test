variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_809335086888894685053982898760 : (((p5 → ((p5 ∧ ((False ∨ ((p5 → (p2 → (((False → (((p5 ∨ True) ∨ (p5 ∨ p2)) → p4)) ∧ True) ∧ p3))) → False)) ∨ p4)) ∨ p5)) ∨ p3) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_47439449854608860336509083688 : (((p3 ∧ (((True ∨ (p1 ∧ (p4 ∧ (((p1 → (p1 ∨ p4)) ∨ p5) ∨ (True ∨ p3))))) → (p5 ∧ (p4 ∨ p4))) ∧ p5)) ∨ (p3 ∨ False)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_112557117757681314916664495064 : (((((p4 ∧ True) → (False ∨ (((True ∨ (((p4 ∨ (p2 ∧ True)) ∧ ((p4 → False) → p1)) ∧ p2)) ∧ p5) ∨ True))) → True) → False) ∨ (True → True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_398502446668799129593523394164 : ((((True → ((((p4 → (p1 → p1)) → p1) → (((p1 ∧ p2) ∧ (p4 ∧ True)) ∨ (((p5 ∨ (p5 ∨ p5)) ∧ p1) ∧ p2))) ∧ p3)) ∨ True) ∧ True) ∧ True) := by
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
theorem thm_5_vars_742973244125998583453802189017 : ((((p3 → p5) ∨ ((p2 ∧ p5) ∨ (((((False ∧ p4) ∨ ((p3 ∧ p2) ∨ p4)) → p2) ∧ (((True ∨ p5) ∧ (False ∧ p4)) → p3)) → p2))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_431537823427429630148605185384 : ((((p3 ∧ ((((False → p3) ∨ ((True ∨ False) → (p4 → ((p2 ∨ p5) ∧ (True ∧ p1))))) ∧ True) → (p2 ∨ (p5 ∧ False)))) ∨ (False → p1)) ∧ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- False on the left can always be used.
  apply False.elim h1
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_143245122348496464232767167985 : ((p3 → ((((p3 → p1) → (((p4 ∨ (p2 → (False → p2))) ∧ (p2 → (p3 ∨ True))) ∧ p5)) ∧ (p1 → p4)) → p4)) → (p1 ∨ (True ∨ p3))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_137427811715475098290889283965 : ((p4 ∧ ((((p4 ∨ False) ∧ False) → (((((p5 ∧ ((p2 ∨ p2) → p4)) ∨ (p3 ∧ p5)) → p4) ∨ False) ∨ p4)) → p1)) ∨ (p4 → (True ∨ p5))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_64495581939448890881325063315 : ((p1 ∨ ((p4 ∧ ((p4 ∨ p3) ∧ (p5 ∧ ((p4 ∧ False) → ((p2 ∨ True) ∨ (True ∨ p1)))))) ∨ (True ∨ ((p3 ∧ p2) ∧ (p4 ∨ p1))))) ∨ p2) := by
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
theorem thm_5_vars_133627995533719840519705521280 : (((((False → False) → (True ∨ (((p3 → (False ∧ p4)) ∧ p3) ∨ (((False ∧ p2) ∨ (False ∧ p4)) → p2)))) → p3) ∧ p3) ∨ (p5 ∨ (p3 → True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_49380354827730073086773365594 : (((((((True ∧ (p5 ∧ ((False ∨ p4) ∧ (True → p2)))) → (False ∧ p3)) ∧ (p1 ∧ (p2 ∧ p4))) ∧ p5) ∧ p5) → ((False ∧ p3) ∨ p3)) ∨ p5) := by
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
  let h6 := h4.left
  let h7 := h4.right
  -- Conjunctions on the left can always be decomposed.
  let h8 := h7.left
  let h9 := h7.right
  -- Conjunctions on the left can always be decomposed.
  let h10 := h9.left
  let h11 := h9.right
  -- We want to use the implication h6 based on <expert-advice>. So we show its premise.
  have h12 : (True ∧ (p5 ∧ ((False ∨ p4) ∧ (True → p2)))) := by
    -- Conjunctions on the right can always be decomposed.
    apply And.intro
    -- True on the right can always be proven directly.
    apply True.intro
    -- Conjunctions on the right can always be decomposed.
    apply And.intro
    -- One of the premise coincides with the conclusion.
    exact h3
    -- Conjunctions on the right can always be decomposed.
    apply And.intro
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h11
    -- Implications on the right can always be decomposed.
    intro h13
    -- One of the premise coincides with the conclusion.
    exact h10
  -- We have shown the premise of h6, we can now drive its conclusion.
  let h14 := h6 h12
  -- We need to get the left conjuct of h14 based on <expert-advice>.
  let h15 := h14.left
  -- False on the left can always be used.
  apply False.elim h15



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_159276085093811803189252594370 : ((p4 → (((p5 ∨ ((p2 → (((p4 → p3) → False) ∨ (True ∨ False))) → p3)) → p1) ∨ (True → False))) ∨ ((p3 → (p4 ∨ p3)) ∨ (p3 ∨ p4))) := by
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
theorem thm_5_vars_240901363679059524501267763758 : ((True → True) ∧ (p5 → ((((True → (((False ∨ p2) → ((p5 ∨ True) ∨ p4)) ∨ ((p2 ∨ (p3 ∧ (True → p4))) → p1))) ∨ p5) → p1) ∨ p5))) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro
  -- Implications on the right can always be decomposed.
  intro h2
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_358158043262838980005589398630 : (p5 → (p3 ∨ ((True ∧ ((p2 → (p4 ∧ p2)) → (p1 → ((((((False ∨ p4) → p3) ∧ p4) ∧ (p3 ∧ (p4 ∨ p1))) ∨ True) ∧ True)))) ∨ p3))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- Implications on the right can always be decomposed.
  intro h2
  -- Implications on the right can always be decomposed.
  intro h3
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_64799738907670418024218369706 : ((p2 ∨ ((False ∧ (p1 ∨ ((p3 ∨ p4) → (p2 → (p4 ∧ (((p3 ∨ (False ∧ p1)) ∨ (False ∧ p5)) → ((False ∨ p5) ∨ p4))))))) ∨ p2)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_69022583341195181750659165684 : ((p5 → (((((p2 → (p4 ∨ ((p1 → (True ∨ (p1 ∧ (p4 ∨ p3)))) ∧ p4))) ∧ (p1 → (p4 ∧ p4))) ∧ (False ∧ False)) ∧ p3) ∨ p5)) ∨ p5) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_178718327220572328908157887353 : ((((True ∨ (p4 ∨ p2)) ∧ p1) → (((p3 ∨ p2) ∨ True) ∨ (p1 ∧ False))) ∨ (p4 ∨ ((p4 → (((p3 ∨ p3) → (False → p2)) ∧ True)) ∧ p2))) := by
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
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- True on the right can always be proven directly.
      apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_310287711327104446295569530138 : (p2 ∨ (((((p2 ∨ p4) ∨ ((p4 ∨ p2) → p3)) ∧ p5) ∧ p2) ∨ ((((((p3 ∨ (False ∧ p1)) ∧ p5) ∧ False) ∨ True) ∨ (True → p5)) ∨ p5))) := by
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
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_720318927473739190146595815973 : ((((((p2 ∧ p1) ∨ p1) ∨ p3) → ((p5 → (p4 → p5)) → ((p3 → False) ∨ (p3 ∨ (p2 → (p3 ∧ ((p3 ∧ (p4 ∧ p4)) ∨ p4))))))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_38417601502000038764488979944 : (((((p2 ∧ True) ∧ (((p1 ∧ p4) → True) ∨ ((p1 → (p3 → True)) → p3))) ∧ (((p4 ∨ p5) ∧ False) ∧ (p1 → (p2 ∨ p4)))) ∧ p2) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_57821935240826870294970456556 : (((p3 ∧ (p2 → p1)) → ((p4 ∧ (((True ∨ (False ∨ p5)) → (((True ∨ p2) → p2) → p4)) ∨ p4)) ∨ ((True ∧ (p5 → p3)) → p2))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_708484528836144060276925103434 : ((((((p1 ∨ (True → (p1 ∧ p4))) ∧ p2) ∨ p1) → ((((False → p5) → (p5 → p5)) → p4) ∨ ((p1 ∨ p5) ∧ ((p2 → True) ∨ p3)))) ∨ p2) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
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
    -- Disjunctions on the left can always be decomposed.
    cases h3
    case inl h5 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Conjunctions on the right can always be decomposed.
      apply And.intro
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- One of the premise coincides with the conclusion.
      exact h5
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- Implications on the right can always be decomposed.
      intro h6
      -- True on the right can always be proven directly.
      apply True.intro
    case inr h7 =>
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- Implications on the right can always be decomposed.
      intro h8
      -- We want to use the implication h7 based on <expert-advice>. So we show its premise.
      have h9 : True := by
        -- True on the right can always be proven directly.
        apply True.intro
      -- We have shown the premise of h7, we can now drive its conclusion.
      let h10 := h7 h9
      -- We need to get the right conjuct of h10 based on <expert-advice>.
      let h11 := h10.right
      -- One of the premise coincides with the conclusion.
      exact h11
  case inr h12 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Conjunctions on the right can always be decomposed.
    apply And.intro
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- One of the premise coincides with the conclusion.
    exact h12
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Implications on the right can always be decomposed.
    intro h13
    -- True on the right can always be proven directly.
    apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_159047530306830582894074432943 : ((p5 ∨ (((False → (((p5 ∧ p1) ∨ (((p2 → p2) ∨ p5) ∨ p4)) ∧ (True ∨ p1))) ∨ p3) → p4)) ∨ (p2 → (p4 → (p3 → (p5 → p2))))) := by
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
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_197799248070969193553846415942 : ((((p2 ∧ False) ∨ False) ∨ ((p3 ∧ p3) ∨ p2)) ∨ ((p1 → (p3 ∧ p4)) → ((p2 → p5) → ((p3 ∨ True) ∧ (p2 ∨ (p2 → (True → p5))))))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h3
  -- Implications on the right can always be decomposed.
  intro h4
  -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
  have h5 : p2 := by
    -- One of the premise coincides with the conclusion.
    exact h3
  -- We have shown the premise of h2, we can now drive its conclusion.
  let h6 := h2 h5
  -- One of the premise coincides with the conclusion.
  exact h6



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_40496632613604765173019743807 : ((((True ∧ ((((p1 ∧ ((p1 → ((p5 → ((p1 ∨ True) → (p5 → p2))) ∨ True)) ∧ p2)) ∨ p3) ∧ p5) ∧ (p2 ∨ p3))) ∨ p3) ∨ True) ∨ p3) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_58698502005387921985975138332 : (((p2 → p4) ∧ ((p4 → (True → (((p4 → p5) ∨ (((p3 ∧ (((p5 ∨ p2) → p4) → p3)) ∧ (p3 ∧ True)) → p2)) ∨ p3))) ∨ p2)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_313282754465822431046874395838 : (p3 ∨ ((p3 ∧ (((p5 → (False → (p3 → (p2 → False)))) → True) → (p2 ∧ (p4 ∧ (((((True → p5) ∨ p2) ∧ p4) ∧ p3) ∨ p5))))) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_765788543177324667156141921544 : (((p4 ∧ (((p1 ∧ p5) ∨ ((p2 → (p2 ∨ False)) → False)) ∨ (((False → (False ∨ (p3 ∨ p3))) → (True ∧ (p5 → (p3 → True)))) → p5))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_337547338964925667491294603199 : (p1 → (((p2 ∧ True) → ((((p4 ∨ True) → p2) ∧ ((p4 → (True ∧ (p2 ∨ True))) ∧ (p4 ∧ p5))) → False)) ∨ (p3 → (False → (p1 → p4))))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h2
  -- Implications on the right can always be decomposed.
  intro h3
  -- Implications on the right can always be decomposed.
  intro h4
  -- False on the left can always be used.
  apply False.elim h3



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_200845105123299675333063174093 : ((True ∨ (((p3 ∧ True) → p3) ∧ (p3 → p1))) → (((p1 ∨ p5) ∧ p2) ∨ ((p1 ∨ ((p5 → p1) → p3)) ∨ ((False → (True → False)) ∨ p1)))) := by
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
    -- Implications on the right can always be decomposed.
    intro h3
    -- Implications on the right can always be decomposed.
    intro h4
    -- False on the left can always be used.
    apply False.elim h3
  case inr h5 =>
    -- Conjunctions on the left can always be decomposed.
    let h6 := h5.left
    let h7 := h5.right
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Implications on the right can always be decomposed.
    intro h8
    -- Implications on the right can always be decomposed.
    intro h9
    -- False on the left can always be used.
    apply False.elim h8



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_774489114014145340456471349440 : (((False ∨ (((p1 ∧ (False ∧ ((((p2 ∧ False) ∨ True) ∧ p2) → (p4 ∨ False)))) ∧ p2) ∧ (((False ∧ (p4 ∨ (p4 → False))) → p3) ∨ p2))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_643922213159936447133974204019 : ((((True ∨ (((((False → p2) → p3) ∨ ((((p4 ∨ (p2 ∨ p3)) → p2) ∧ p4) ∨ ((True ∨ (False ∧ p1)) ∨ p3))) ∨ p1) ∧ True)) → p1) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_615237503040617793289454521230 : (((((False ∨ ((p4 ∧ p5) ∨ ((True ∨ (True ∨ ((p1 ∨ False) ∧ (p3 ∨ p5)))) ∨ p3))) ∧ ((False ∨ p5) → ((p1 ∨ p1) ∨ p5))) ∨ p2) ∨ p5) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
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
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro
  -- Implications on the right can always be decomposed.
  intro h1
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h2 =>
    -- False on the left can always be used.
    apply False.elim h2
  case inr h3 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h3
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_912994440359737423738954083124 : (((((False → (p1 → False)) ∧ (((((p1 ∧ p2) ∨ p4) ∧ (False ∨ p4)) ∨ p3) ∨ (False → True))) → (False ∧ (((False ∧ p2) → p3) ∨ p5))) → False) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h1
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h2 : ((False → (p1 → False)) ∧ (((((p1 ∧ p2) ∨ p4) ∧ (False ∨ p4)) ∨ p3) ∨ (False → True))) := by
    -- Conjunctions on the right can always be decomposed.
    apply And.intro
    -- Implications on the right can always be decomposed.
    intro h3
    -- Implications on the right can always be decomposed.
    intro h4
    -- False on the left can always be used.
    apply False.elim h3
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h5
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h6 := h1 h2
  -- We need to get the left conjuct of h6 based on <expert-advice>.
  let h7 := h6.left
  -- False on the left can always be used.
  apply False.elim h7
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_142085440853390363265837580045 : ((True ∧ ((p4 ∨ p5) ∨ (False ∨ ((((p3 ∨ p2) ∧ p5) ∧ p3) → (p2 ∨ ((((p3 → p1) ∧ p3) ∨ True) ∧ False)))))) → (p1 → (p2 ∨ p1))) := by
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
    -- Disjunctions on the left can always be decomposed.
    cases h5
    case inl h6 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- One of the premise coincides with the conclusion.
      exact h2
    case inr h7 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- One of the premise coincides with the conclusion.
      exact h2
  case inr h8 =>
    -- Disjunctions on the left can always be decomposed.
    cases h8
    case inl h9 =>
      -- False on the left can always be used.
      apply False.elim h9
    case inr h10 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- One of the premise coincides with the conclusion.
      exact h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_53989999804988365302271506741 : (((((p4 → p5) ∨ (((True ∨ p1) → p1) → True)) ∨ p3) → (((((p5 → p5) ∨ False) ∨ False) ∧ p2) → ((p2 → (p1 → False)) → p5))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_732564115069356830009070462890 : ((((p1 ∧ False) ∧ (((p2 → ((((p3 ∨ p1) ∧ (False ∨ (p5 ∨ (p3 → False)))) → (p3 → p3)) → p1)) → ((p3 ∧ False) ∧ False)) → False)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_452120410298534100542934281025 : (((((p4 → p4) ∧ ((p2 → ((((True → p3) → p3) ∨ True) ∨ ((p3 ∧ False) ∧ (True ∧ p3)))) → p4)) ∨ (((False ∨ True) ∨ True) ∨ p5)) ∧ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
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
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_150906134256371236875058137918 : ((((p5 → (True → p1)) → (((p2 ∨ (p2 ∨ p5)) → (p4 ∧ (p3 → ((p5 → False) → p2)))) ∨ True)) ∨ p1) → (True ∧ ((p5 ∧ p4) ∨ True))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- True on the right can always be proven directly.
  apply True.intro
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
theorem thm_5_vars_168190855812236654465861622263 : ((((p1 ∨ p5) ∧ True) ∨ (p2 → ((p3 ∨ ((p4 ∨ (p3 → True)) → p5)) ∨ (p3 ∨ p2)))) → (((False ∧ ((p4 → p3) → True)) ∨ p1) ∨ True)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h2 =>
    -- Conjunctions on the left can always be decomposed.
    let h3 := h2.left
    let h4 := h2.right
    -- Disjunctions on the left can always be decomposed.
    cases h3
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
  case inr h7 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_312108275546195320831077482897 : (p2 ∨ (True → (((((True ∨ (p3 ∨ p4)) → ((p2 → (p4 ∨ True)) ∧ p5)) ∧ p3) ∧ ((False → ((p5 → p4) ∧ p3)) → (p1 ∧ p1))) ∨ True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_141693466430494923988791336351 : (((True ∨ p1) ∧ ((p3 ∨ ((p4 ∧ p5) → ((((p4 ∨ p4) ∨ ((p3 ∨ (p5 ∨ True)) ∧ p2)) ∨ True) ∧ p4))) ∧ p1)) → ((False ∧ False) ∨ True)) := by
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
    -- Disjunctions on the left can always be decomposed.
    cases h5
    case inl h7 =>
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
    -- Conjunctions on the left can always be decomposed.
    let h10 := h3.left
    let h11 := h3.right
    -- Disjunctions on the left can always be decomposed.
    cases h10
    case inl h12 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- True on the right can always be proven directly.
      apply True.intro
    case inr h13 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- True on the right can always be proven directly.
      apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_660940706901998701646335974589 : (((((p2 → ((((((False → p1) ∨ (p1 ∨ p1)) ∧ p5) → ((p4 ∧ ((p2 ∧ p4) → p2)) ∧ p2)) ∨ p3) → False)) → p3) → (p5 → p3)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_648233510313621416648091191578 : (((((p1 ∨ ((p3 ∨ False) ∨ ((p3 ∨ (((False ∨ p1) ∧ p1) ∧ (((p1 → True) → p5) ∨ p1))) → (p4 ∨ p2)))) ∧ False) ∧ (True ∨ p1)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_260364189087783247068039030201 : ((p2 → p5) → ((p4 → (((((True → p3) → p1) ∨ (True ∧ p2)) → False) ∧ (p4 ∨ p4))) ∨ (p2 → (((p1 ∨ (p2 ∨ p4)) ∨ p1) ∧ True)))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h2
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- One of the premise coincides with the conclusion.
  exact h2
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_137397716982007786958340554826 : ((p3 ∧ (p4 ∧ (((p5 ∨ p5) ∨ ((p5 ∧ (p3 ∧ p5)) ∧ p3)) ∨ ((p3 ∧ ((p2 ∧ p2) ∧ p4)) ∧ (True → p1))))) ∨ ((True → p5) → True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_149920964785210281074366945613 : ((p3 ∨ ((p1 ∧ (False → ((p1 ∧ ((True ∨ (p3 → True)) ∧ (p2 ∧ (True ∧ p2)))) ∨ True))) ∨ (p4 ∨ False))) ∨ (((p3 ∧ p2) ∧ False) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_598774108861881187208694605381 : (((((p1 ∧ p2) ∧ (p1 ∧ (((p3 → (True ∨ (p5 ∧ p4))) ∨ p1) ∧ (p1 ∧ (False ∨ ((p5 → p2) → ((p4 ∧ p4) → p1))))))) ∧ False) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_194065726199382433357065851539 : ((True → ((p5 ∧ (False → ((p1 → p2) → p2))) ∧ p1)) → (((p5 ∨ p5) → (p4 → p2)) → ((((True ∨ p3) ∨ p1) ∧ (p3 → False)) ∨ p1))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h3 : True := by
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h4 := h1 h3
  -- We need to get the right conjuct of h4 based on <expert-advice>.
  let h5 := h4.right
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h5



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_65860423938105239460640659624 : ((p4 ∨ ((p1 ∨ p5) ∧ (((((False → ((False ∧ True) ∧ (p5 ∧ (False ∧ p4)))) → True) → False) ∧ (((p2 → False) ∧ p2) ∧ p4)) ∨ True))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_214260890589554296451284021092 : (((p2 ∧ (p4 ∧ p3)) → p1) ∨ ((((p5 → False) ∧ True) ∧ (p2 ∧ (p5 ∧ False))) ∨ ((p1 → ((p4 ∧ p3) ∨ (p3 ∨ True))) ∧ (True → True)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- Implications on the right can always be decomposed.
  intro h2
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_135891954434284576887714434387 : (((((((False ∧ ((p5 ∧ p3) ∧ p2)) → p4) ∧ p4) ∨ p3) ∧ p3) → (p2 ∨ (((p2 ∧ (p1 ∧ p4)) ∧ p5) ∨ True))) ∨ ((p4 ∨ p3) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_303217602774439828736294849331 : (False ∨ (p4 → (p5 → (((p4 → (((True ∧ p4) → p4) ∧ ((((True ∨ p3) ∧ p1) ∨ ((p3 ∨ p1) ∨ p1)) ∨ (p5 → p4)))) ∧ p4) ∨ p4)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_309632377500628938002017787939 : (p2 ∨ ((((True ∨ False) ∧ ((False → p4) → (p2 → p5))) → ((((p2 ∨ (p1 ∨ p4)) → False) ∧ (True → p1)) → p3)) ∨ ((p4 → p5) ∧ p5))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
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
  let h5 := h1.left
  let h6 := h1.right
  -- Disjunctions on the left can always be decomposed.
  cases h5
  case inl h7 =>
    -- We want to use the implication h4 based on <expert-advice>. So we show its premise.
    have h8 : True := by
      -- True on the right can always be proven directly.
      apply True.intro
    -- We have shown the premise of h4, we can now drive its conclusion.
    let h9 := h4 h8
    -- We want to use the implication h3 based on <expert-advice>. So we show its premise.
    have h10 : (p2 ∨ (p1 ∨ p4)) := by
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- One of the premise coincides with the conclusion.
      exact h9
    -- We have shown the premise of h3, we can now drive its conclusion.
    let h11 := h3 h10
    -- False on the left can always be used.
    apply False.elim h11
  case inr h12 =>
    -- False on the left can always be used.
    apply False.elim h12



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_37650118067894887204472176067 : (((((((p2 ∨ p4) → ((((False ∧ (False ∧ p4)) ∧ ((p3 → p1) → False)) ∧ True) ∨ ((False ∧ True) ∨ False))) ∧ True) → p2) → p3) ∧ p3) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_186114414415548127956813541574 : ((((p3 → (((p2 ∨ p5) → True) → False)) → (p4 ∧ p5)) ∨ p3) → (p1 → (p2 → (p2 ∧ (((((p4 ∧ p5) ∨ p3) ∧ p4) ∧ p4) ∨ True))))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Implications on the right can always be decomposed.
  intro h3
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h4 =>
    -- One of the premise coincides with the conclusion.
    exact h3
  case inr h5 =>
    -- One of the premise coincides with the conclusion.
    exact h3
  -- Disjunctions on the left can always be decomposed.
  cases h1
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



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_180960064923664038693054550134 : (((True → p2) ∧ ((((p2 ∨ (p1 ∧ p4)) → p1) → (p2 ∨ p3)) ∧ True)) → ((p2 → (((False → False) → ((p1 → True) ∧ p5)) → p3)) ∨ True)) := by
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
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_121434545278966253984001583405 : (((((((False → p2) ∨ (p5 → (p5 ∨ p3))) → ((p3 ∧ (((p1 → p1) ∧ p1) → p4)) ∧ (p5 ∧ p3))) ∧ p5) → p3) → p5) → (p4 ∨ p5)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h2 : (((((False → p2) ∨ (p5 → (p5 ∨ p3))) → ((p3 ∧ (((p1 → p1) ∧ p1) → p4)) ∧ (p5 ∧ p3))) ∧ p5) → p3) := by
    -- Implications on the right can always be decomposed.
    intro h3
    -- Conjunctions on the left can always be decomposed.
    let h4 := h3.left
    let h5 := h3.right
    -- We want to use the implication h4 based on <expert-advice>. So we show its premise.
    have h6 : ((False → p2) ∨ (p5 → (p5 ∨ p3))) := by
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- Implications on the right can always be decomposed.
      intro h7
      -- False on the left can always be used.
      apply False.elim h7
    -- We have shown the premise of h4, we can now drive its conclusion.
    let h8 := h4 h6
    -- We need to get the left conjuct of h8 based on <expert-advice>.
    let h9 := h8.left
    -- We need to get the left conjuct of h9 based on <expert-advice>.
    let h10 := h9.left
    -- One of the premise coincides with the conclusion.
    exact h10
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h11 := h1 h2
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h11



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_233911415051231381619957492782 : ((p4 ∨ (True → p5)) → (p5 → (p5 → (((p5 → (p2 ∧ (True ∨ p5))) ∨ ((True ∨ p1) ∨ p5)) ∨ ((p3 ∧ p3) ∧ ((p5 ∧ p3) → True)))))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Implications on the right can always be decomposed.
  intro h3
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h4 =>
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
  case inr h5 =>
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



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_902189817811567940041339791881 : ((((((True ∨ ((True ∧ (((p4 ∨ p4) → p3) ∨ p3)) → p3)) ∧ ((p3 ∨ False) → True)) → (p2 ∧ False)) ∧ (p4 → ((p2 → p5) ∨ False))) → False) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
  have h4 : ((True ∨ ((True ∧ (((p4 ∨ p4) → p3) ∨ p3)) → p3)) ∧ ((p3 ∨ False) → True)) := by
    -- Conjunctions on the right can always be decomposed.
    apply And.intro
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- True on the right can always be proven directly.
    apply True.intro
    -- Implications on the right can always be decomposed.
    intro h5
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h2, we can now drive its conclusion.
  let h6 := h2 h4
  -- We need to get the right conjuct of h6 based on <expert-advice>.
  let h7 := h6.right
  -- False on the left can always be used.
  apply False.elim h7
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_148708555533725000554944145054 : ((((p3 → (p2 ∨ ((p1 ∧ p2) ∧ p4))) → p5) → (p2 → (((((p5 ∨ p1) ∧ p4) ∨ p4) → False) ∨ True))) ∨ ((p3 → (p2 ∧ p5)) ∧ True)) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_62947696742333098671783667860 : ((p4 ∧ (p5 ∧ (((False → True) ∨ (((p1 → ((p3 → True) → ((((p2 ∧ p1) ∨ p1) ∧ p3) ∨ (p5 → p4)))) ∨ p4) ∧ p3)) → p3))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_41380866828367705181095671706 : ((((((((p4 → p5) ∧ p3) → p2) → ((p1 ∧ (True → p5)) ∨ False)) ∧ p3) ∧ ((p2 ∨ ((p4 → p1) ∧ p3)) ∨ (p5 ∧ p3))) ∨ p4) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_616070491722001227838035216940 : (((((p4 ∨ (((p4 ∧ p3) ∨ p3) ∨ ((((True ∨ p5) ∧ p2) ∧ False) → p5))) → (p4 ∧ (((p4 ∨ p3) → (False → False)) → p1))) ∨ True) ∨ p5) ∧ True) := by
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
theorem thm_5_vars_164869143082226966551815150198 : (((p4 ∨ (p4 ∨ ((p5 ∧ p4) ∧ (p4 ∨ ((p2 ∧ (p4 ∧ (False → p2))) → True))))) ∨ p5) ∨ ((((True ∨ p1) → p2) ∨ p4) → (False → p1))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- False on the left can always be used.
  apply False.elim h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_65244310720341350466177478967 : ((p3 ∨ (((((p4 ∨ p3) → (p3 → p1)) ∧ ((p2 ∧ (p4 → p1)) → ((False ∨ False) ∨ ((p3 → p2) → (p3 ∧ p3))))) → p4) → p5)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_109162177720540749403855265938 : ((False ∨ (((((True → (True ∧ ((p3 ∧ ((p4 → p2) ∧ (p5 ∧ p4))) → p3))) → p2) ∨ (p4 ∨ (p4 → True))) ∨ p1) ∧ True)) ∧ (p4 → p4)) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
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
  -- Implications on the right can always be decomposed.
  intro h2
  -- One of the premise coincides with the conclusion.
  exact h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_185211646052670723465617536509 : ((True ∧ (p4 ∨ (((p5 ∨ (p5 ∧ p5)) ∧ True) → (p1 → p4)))) ∨ (p5 ∨ (p4 ∨ (((p4 ∧ (((True ∨ p3) → p3) ∧ False)) ∧ p1) → p1)))) := by
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
  -- Conjunctions on the left can always be decomposed.
  let h4 := h2.left
  let h5 := h2.right
  -- Conjunctions on the left can always be decomposed.
  let h6 := h5.left
  let h7 := h5.right
  -- False on the left can always be used.
  apply False.elim h7



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_737936626761540642904936799009 : ((((True ∧ p3) ∨ ((p2 → False) → ((p3 → (p2 ∧ (True ∨ (p3 ∧ p3)))) ∨ (((p2 → ((p4 → p2) ∨ False)) → p3) ∨ (p3 ∧ True))))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_252984167248820197473895450954 : ((True ∧ p2) → (p2 → (((((True → ((p4 ∨ (p5 ∨ (p5 ∧ p2))) → (p3 ∨ False))) ∨ (p4 ∧ (p1 ∨ True))) → False) ∧ (p2 ∧ p2)) ∨ p2))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Conjunctions on the left can always be decomposed.
  let h3 := h1.left
  let h4 := h1.right
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h4



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_231628827348688500777828471368 : (((False ∧ False) → True) → (((((((False ∧ False) ∧ p1) ∧ p1) ∧ p1) ∧ True) ∧ p5) ∨ ((((((p5 → p5) ∧ p2) → p5) → False) → p3) ∨ True))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_216757949633064150720616532240 : ((((p2 → p2) → p2) ∧ p3) → ((((p1 ∨ p2) → (p1 ∧ (((p2 ∨ True) → p4) ∧ (p5 ∧ False)))) ∨ ((p4 → p5) ∨ p2)) ∨ (p4 → p5))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
  have h4 : (p2 → p2) := by
    -- Implications on the right can always be decomposed.
    intro h5
    -- One of the premise coincides with the conclusion.
    exact h5
  -- We have shown the premise of h2, we can now drive its conclusion.
  let h6 := h2 h4
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h6



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_345712951089134721504327133997 : (p3 → ((p1 → (p3 ∧ (((p4 ∧ ((((p4 ∨ p2) ∨ (((p5 ∨ p1) ∧ p4) ∨ (p1 ∨ p3))) ∨ p3) → p2)) ∨ True) ∨ (p4 ∨ p1)))) ∨ p1)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h2
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- One of the premise coincides with the conclusion.
  exact h1
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_190360649083622271158864164772 : ((((True ∨ p4) ∧ (p1 ∨ (p2 ∧ (p5 ∧ p2)))) ∨ p2) ∨ ((p3 ∨ p1) ∨ ((p2 → p2) → ((p5 ∧ ((p1 ∨ (p4 ∨ p1)) ∧ p4)) → True)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_116836768881412428385154101638 : (((True → False) ∨ ((p1 ∧ ((p2 ∨ ((p3 ∨ True) ∧ ((p3 ∧ p2) ∧ ((p2 → p3) ∧ (p1 → False))))) ∧ p5)) ∧ (p3 ∧ False))) ∨ (p3 ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_156613031385904138651135686604 : ((((p2 ∨ ((p4 ∧ (p4 → p1)) ∨ ((p3 → p3) ∧ ((p5 ∨ (p2 ∧ p3)) → p2)))) ∧ p5) ∧ False) ∨ ((p1 ∧ (False → (p5 ∧ p2))) → True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_643185767902229526137819394480 : ((((p3 ∧ ((((p4 → (False ∨ (p5 ∧ (p4 → ((p5 → False) ∨ True))))) ∨ ((True → p3) ∧ p4)) ∨ (p3 → p3)) → (False ∧ p3))) → p5) ∨ p2) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- We want to use the implication h3 based on <expert-advice>. So we show its premise.
  have h4 : (((p4 → (False ∨ (p5 ∧ (p4 → ((p5 → False) ∨ True))))) ∨ ((True → p3) ∧ p4)) ∨ (p3 → p3)) := by
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h5
    -- One of the premise coincides with the conclusion.
    exact h5
  -- We have shown the premise of h3, we can now drive its conclusion.
  let h6 := h3 h4
  -- We need to get the left conjuct of h6 based on <expert-advice>.
  let h7 := h6.left
  -- False on the left can always be used.
  apply False.elim h7
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_341328412518254860735945432182 : (p2 → (((p2 ∧ ((True ∨ p5) → ((p2 ∧ (p4 → p2)) ∨ True))) ∧ (((p1 → True) → (True ∨ p4)) → (((p4 → p2) ∧ p4) ∧ False))) → False)) := by
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
  -- We want to use the implication h4 based on <expert-advice>. So we show its premise.
  have h7 : ((p1 → True) → (True ∨ p4)) := by
    -- Implications on the right can always be decomposed.
    intro h8
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h4, we can now drive its conclusion.
  let h9 := h4 h7
  -- We need to get the right conjuct of h9 based on <expert-advice>.
  let h10 := h9.right
  -- False on the left can always be used.
  apply False.elim h10



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_191172714191923739342177037278 : (((p3 ∨ (p1 ∨ p5)) ∨ (False ∧ ((True ∨ True) ∨ p3))) ∨ ((True → (p5 ∧ True)) ∨ (((((p1 ∧ p1) → p5) ∧ p2) ∧ p1) → (p1 ∨ False)))) := by
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
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- One of the premise coincides with the conclusion.
  exact h3



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_198963571787034194593680480701 : ((p5 → ((((p1 ∧ p3) ∨ p3) → p4) ∧ False)) ∨ ((((p2 ∧ (p5 → p3)) ∨ (p5 ∧ (False → p4))) ∨ p5) → ((False ∨ p1) ∨ (p1 → True)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
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
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Implications on the right can always be decomposed.
      intro h6
      -- True on the right can always be proven directly.
      apply True.intro
    case inr h7 =>
      -- Conjunctions on the left can always be decomposed.
      let h8 := h7.left
      let h9 := h7.right
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Implications on the right can always be decomposed.
      intro h10
      -- True on the right can always be proven directly.
      apply True.intro
  case inr h11 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h12
    -- True on the right can always be proven directly.
    apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_158908426871852933435540836518 : ((p1 ∨ (((p5 ∨ (p5 ∧ ((True ∨ False) → False))) ∧ True) → (((p1 ∨ p4) ∨ p5) ∨ (p3 ∨ p5)))) ∨ ((p5 → p2) ∧ (True ∧ (True → p5)))) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
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
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h4
  case inr h5 =>
    -- Conjunctions on the left can always be decomposed.
    let h6 := h5.left
    let h7 := h5.right
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h6



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_108033407019599182281623319724 : (((p3 ∧ p1) → (p5 → (p1 ∧ ((p4 ∧ (p3 ∧ (p1 ∨ ((p2 ∨ p4) ∨ p3)))) → (p4 ∧ ((p3 → (p2 → False)) ∨ True)))))) ∧ (p1 ∨ True)) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
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
  -- Implications on the right can always be decomposed.
  intro h5
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Conjunctions on the left can always be decomposed.
  let h6 := h5.left
  let h7 := h5.right
  -- Conjunctions on the left can always be decomposed.
  let h8 := h7.left
  let h9 := h7.right
  -- Disjunctions on the left can always be decomposed.
  cases h9
  case inl h10 =>
    -- Conjunctions on the left can always be decomposed.
    let h11 := h1.left
    let h12 := h1.right
    -- One of the premise coincides with the conclusion.
    exact h6
  case inr h13 =>
    -- Disjunctions on the left can always be decomposed.
    cases h13
    case inl h14 =>
      -- Disjunctions on the left can always be decomposed.
      cases h14
      case inl h15 =>
        -- Conjunctions on the left can always be decomposed.
        let h16 := h1.left
        let h17 := h1.right
        -- One of the premise coincides with the conclusion.
        exact h6
      case inr h18 =>
        -- Conjunctions on the left can always be decomposed.
        let h19 := h1.left
        let h20 := h1.right
        -- One of the premise coincides with the conclusion.
        exact h18
    case inr h21 =>
      -- Conjunctions on the left can always be decomposed.
      let h22 := h1.left
      let h23 := h1.right
      -- One of the premise coincides with the conclusion.
      exact h6
  -- Conjunctions on the left can always be decomposed.
  let h24 := h5.left
  let h25 := h5.right
  -- Conjunctions on the left can always be decomposed.
  let h26 := h25.left
  let h27 := h25.right
  -- Disjunctions on the left can always be decomposed.
  cases h27
  case inl h28 =>
    -- Conjunctions on the left can always be decomposed.
    let h29 := h1.left
    let h30 := h1.right
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro
  case inr h31 =>
    -- Disjunctions on the left can always be decomposed.
    cases h31
    case inl h32 =>
      -- Disjunctions on the left can always be decomposed.
      cases h32
      case inl h33 =>
        -- Conjunctions on the left can always be decomposed.
        let h34 := h1.left
        let h35 := h1.right
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- True on the right can always be proven directly.
        apply True.intro
      case inr h36 =>
        -- Conjunctions on the left can always be decomposed.
        let h37 := h1.left
        let h38 := h1.right
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- True on the right can always be proven directly.
        apply True.intro
    case inr h39 =>
      -- Conjunctions on the left can always be decomposed.
      let h40 := h1.left
      let h41 := h1.right
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- True on the right can always be proven directly.
      apply True.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_353375711384960625008130295393 : (p4 → (False ∨ (((((True ∨ (False ∨ p1)) ∨ p3) → True) ∨ p3) → (((p2 → (p4 ∨ p1)) → (p1 ∨ ((p5 ∧ (p1 ∧ p4)) ∨ p4))) ∨ True)))) := by
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
    -- True on the right can always be proven directly.
    apply True.intro
  case inr h4 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_155686346248456844166858342802 : (((False ∨ p3) ∨ ((p3 → True) ∨ ((False ∨ False) ∧ (p2 ∧ (((p1 ∧ p2) → p5) → (False ∧ True)))))) ∧ (p2 ∨ ((p5 ∧ (p3 → True)) → p5))) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h2
  -- Conjunctions on the left can always be decomposed.
  let h3 := h2.left
  let h4 := h2.right
  -- One of the premise coincides with the conclusion.
  exact h3



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_233302199474069010006163480512 : ((True ∨ (p3 ∨ p3)) → (((p4 ∧ False) ∧ p3) ∨ ((p3 → True) ∨ (((False ∨ (p2 → (p1 ∨ ((p4 → True) ∧ p5)))) → (p4 → p1)) → p4)))) := by
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
    -- True on the right can always be proven directly.
    apply True.intro
  case inr h4 =>
    -- Disjunctions on the left can always be decomposed.
    cases h4
    case inl h5 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- Implications on the right can always be decomposed.
      intro h6
      -- True on the right can always be proven directly.
      apply True.intro
    case inr h7 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- Implications on the right can always be decomposed.
      intro h8
      -- True on the right can always be proven directly.
      apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_699033155902383123027378138743 : ((((p1 ∨ (True → ((p3 → ((False → (p4 ∧ False)) ∧ True)) → p2))) ∨ (((((True ∨ (False ∨ p1)) ∧ p2) → (p3 ∨ p5)) ∧ p3) ∧ False)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_349995115955196426933460626901 : (p4 → ((((((p2 ∧ p2) → (p3 ∧ p2)) ∧ p2) ∧ (((((False ∨ False) ∧ (True ∨ (True ∨ p5))) ∨ p2) ∨ (True ∧ p1)) ∧ False)) ∨ True) ∨ p5)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_337528074883115029499072045803 : (p1 → (((False → (((p1 ∧ p2) → (p4 → (True ∨ ((p3 → p3) → p4)))) ∨ ((True ∧ p1) → p2))) → p4) ∨ ((True ∨ (True ∧ True)) ∨ p5))) := by
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
theorem thm_5_vars_634488339200116936142703506208 : ((((((((p3 ∨ p5) ∨ (True ∨ p2)) ∧ ((p2 → (p5 → False)) → p1)) → (p5 → (p1 → (p1 → False)))) ∧ ((p2 ∨ p1) → True)) → p1) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_711912565017371200835011258053 : (((((p1 → (True ∧ (p2 ∨ p2))) ∧ p2) ∨ (((((p1 ∧ True) ∧ False) ∧ False) ∨ (p2 ∧ p1)) → (p3 ∨ (False ∨ (p1 ∨ (p3 ∨ p5)))))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_40672490733048260688650623909 : ((((((p5 → (((p3 ∨ ((((p2 → p4) → p1) ∨ (p1 ∨ p2)) ∧ p2)) → True) ∨ p1)) ∨ False) ∧ (p5 ∨ (False ∧ p4))) → p3) ∨ True) ∨ p4) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_145231639609826466590645580692 : (((((p5 ∨ (p5 → False)) ∨ (p3 ∨ p4)) ∨ False) → (((p3 ∨ p1) → p5) → (p4 ∨ ((p2 ∨ p5) ∨ True)))) ∧ (((False ∨ True) ∨ p4) ∨ p2)) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
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
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- True on the right can always be proven directly.
        apply True.intro
      case inr h6 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- True on the right can always be proven directly.
        apply True.intro
    case inr h7 =>
      -- Disjunctions on the left can always be decomposed.
      cases h7
      case inl h8 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- True on the right can always be proven directly.
        apply True.intro
      case inr h9 =>
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- One of the premise coincides with the conclusion.
        exact h9
  case inr h10 =>
    -- False on the left can always be used.
    apply False.elim h10
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_629392876034372132862918272387 : ((((((p4 ∨ ((p2 ∧ ((p4 → (p2 ∧ (p4 ∨ p1))) ∨ (((p2 → True) ∨ p4) ∨ (True ∨ (p4 → p4))))) ∨ True)) → p4) ∨ p1) → p5) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_660154231674176802017306776078 : ((((((((p1 → p2) ∧ ((p1 ∧ p3) → (p1 → True))) ∨ False) → ((p5 ∨ p4) → ((p5 ∧ (p5 ∧ False)) ∧ p4))) ∨ p4) → (p1 ∧ False)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_208165165477442832925655650247 : (((p1 ∧ (p5 ∨ p2)) → (p5 → True)) → ((((p1 ∨ p3) → p5) ∨ True) ∧ ((p4 ∨ (p3 → (p5 ∧ ((p2 ∨ (True ∨ p5)) ∨ p5)))) → True))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- Implications on the right can always be decomposed.
  intro h2
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_797848434428017168575877662031 : (((p1 → ((((p5 ∧ (p4 ∨ ((((p1 ∨ (p4 ∨ p4)) ∧ True) → p3) ∧ (p3 ∧ (p1 ∨ (p2 ∨ p3)))))) → p3) ∨ p5) ∨ (p2 ∧ True))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_213258582106982942114117576811 : ((((p1 ∨ p5) → p4) ∧ p4) ∨ (((p2 → (p5 ∨ ((p2 ∧ p5) → p1))) ∨ ((p1 ∨ (p2 ∨ p3)) ∨ True)) ∨ (True ∧ ((p2 ∧ True) ∨ p4)))) := by
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
theorem thm_5_vars_190906168204518597424851437176 : (((True → ((True ∧ p1) → (p5 → p1))) → (p3 ∧ False)) ∨ (p2 ∨ ((p2 ∧ ((False → p3) ∧ ((p4 ∨ (p2 ∨ (p1 → p2))) → p4))) → p2))) := by
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
  let h4 := h3.left
  let h5 := h3.right
  -- One of the premise coincides with the conclusion.
  exact h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_153148641321917813285858976007 : ((p5 ∧ ((((True → p2) ∨ (((p5 → p2) → p5) ∨ (((p2 → (p4 ∧ p3)) ∨ p5) → True))) ∨ p3) ∨ p2)) → ((p5 ∧ (p3 ∨ p5)) ∨ False)) := by
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
      -- Disjunctions on the left can always be decomposed.
      cases h5
      case inl h6 =>
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
      case inr h7 =>
        -- Disjunctions on the left can always be decomposed.
        cases h7
        case inl h8 =>
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
        case inr h9 =>
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
    case inr h10 =>
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
  case inr h11 =>
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
theorem thm_5_vars_689532450937569329674004452045 : ((((((p1 ∨ ((p5 ∧ (p5 ∨ True)) → p3)) → False) ∨ (((p4 ∧ p5) ∨ p2) ∧ False)) ∨ ((p2 → p3) ∨ ((p4 → p2) ∨ (p5 → False)))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



