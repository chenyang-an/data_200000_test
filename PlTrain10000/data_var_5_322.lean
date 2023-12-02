variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_39755713845809081793742630330 : (((True → (((p4 → (p2 → p5)) ∧ (False → ((p3 ∨ (p3 → p4)) ∨ ((p2 ∧ p1) ∧ (p5 → (p5 → (p1 → p4))))))) → p2)) ∧ p2) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_117495577526577755350631492102 : ((p1 ∧ (p4 → (False ∧ (((True ∨ (p1 ∧ ((p3 ∨ p2) → ((p3 ∧ True) ∧ ((p4 → (p2 → p5)) ∨ p4))))) ∨ p4) → p5)))) ∨ (p3 → p3)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_191233502544147265585331044894 : (((p1 → (True → True)) → (((p5 → p5) → p4) ∨ False)) ∨ ((False → (p3 ∧ False)) ∧ (p5 ∨ (p2 ∨ ((True ∨ ((p3 → p1) ∨ False)) → True))))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- False on the left can always be used.
  apply False.elim h1
  -- False on the left can always be used.
  apply False.elim h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h2
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_117012718046915290378248386002 : (((p1 ∨ False) → (((True → (p4 ∨ (p2 ∧ p3))) ∨ (((False ∧ (((p2 → True) → True) ∧ p3)) ∨ (p2 ∨ p2)) ∧ p1)) ∧ True)) ∨ (True ∨ p1)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_193209811603486425028919419998 : (((p4 ∨ ((p2 ∧ True) ∧ p5)) → ((False → True) ∧ p3)) → (p3 ∨ ((p1 → ((p5 ∨ p2) ∧ (p4 ∧ p5))) ∨ (False ∨ ((p4 → p3) ∨ p5))))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h2
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h3 : (p4 ∨ ((p2 ∧ True) ∧ p5)) := by
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- One of the premise coincides with the conclusion.
    exact h2
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h4 := h1 h3
  -- We need to get the right conjuct of h4 based on <expert-advice>.
  let h5 := h4.right
  -- One of the premise coincides with the conclusion.
  exact h5



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_627451390266414688018184285180 : ((((((p5 ∧ (p5 ∨ (p5 ∧ ((p5 ∧ p1) ∨ (((p2 → (((p5 ∨ p1) ∧ p5) → p5)) ∨ (p4 ∨ p3)) ∨ p2))))) → True) ∧ p1) → p3) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_159267925790967768419984110472 : ((p4 → ((((True → (((p1 ∧ (False ∨ (False ∧ p3))) ∧ (p2 ∨ p3)) ∨ p2)) ∨ p5) ∨ p5) ∨ p4)) ∨ (((True ∧ (p4 → p3)) ∨ p3) ∨ False)) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_111568287981490703475427257633 : ((((((p5 ∨ p5) ∨ True) ∧ ((((p2 ∧ (p4 ∨ (p1 → (p4 → p2)))) → True) → (p5 ∧ (True → p5))) ∧ p2)) ∧ True) ∨ p5) ∨ (False → p4)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_113760150596915459031565313391 : ((((p4 ∨ ((p2 → (p3 ∧ p5)) ∨ (p5 → p1))) → ((True ∨ p4) ∨ ((p5 → p3) ∨ (p1 → (p5 ∧ p5))))) → (p1 → p2)) ∨ (p2 → p2)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_632524785952297275775912984936 : (((((p4 ∨ (p2 → (((p1 ∧ p1) ∧ p3) → (p4 ∨ ((p2 ∨ ((p2 → p4) ∨ (p5 → p5))) → (p2 ∧ (True → p5))))))) → p3) → p2) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_37531282342981956324997725013 : ((((p2 ∧ ((((((((p3 ∨ (p1 ∨ True)) ∧ (p3 ∧ p5)) ∨ p3) ∨ p2) → (p3 → p3)) ∨ (False → True)) → p2) ∨ p3)) ∨ False) ∧ p3) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_166284939500310574157464322035 : ((p4 ∧ ((False ∨ (p1 ∧ (p5 ∧ ((False → p1) ∧ (False → ((p2 ∧ p1) → False)))))) → p4)) ∨ ((((p5 → p5) ∨ p5) ∨ p5) ∨ (p1 → p4))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_231584601187326407194824332844 : (((True ∧ True) → False) → ((((p5 ∨ (True ∨ p3)) ∧ ((p4 ∧ p5) ∨ p5)) ∧ ((p5 → p1) → p4)) ∧ ((p2 → ((p5 ∨ p1) ∧ p4)) ∨ True))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h2 : (True ∧ True) := by
    -- Conjunctions on the right can always be decomposed.
    apply And.intro
    -- True on the right can always be proven directly.
    apply True.intro
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h3 := h1 h2
  -- False on the left can always be used.
  apply False.elim h3
  -- Implications on the right can always be decomposed.
  intro h4
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h5 : (True ∧ True) := by
    -- Conjunctions on the right can always be decomposed.
    apply And.intro
    -- True on the right can always be proven directly.
    apply True.intro
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h6 := h1 h5
  -- False on the left can always be used.
  apply False.elim h6
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_118240436428661297324531620362 : ((p1 ∨ (((p4 ∧ (p1 ∨ (p3 ∨ ((p2 ∨ p1) ∧ ((p2 ∧ (True ∨ p5)) ∨ p4))))) → (True → (p3 ∨ p1))) ∧ (True ∧ p1))) ∨ (p5 → True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_205295514861496917565121587898 : (((p4 ∧ (p5 ∧ p5)) ∨ (True ∧ p2)) ∨ ((((p3 ∧ p1) ∧ ((((True → p3) ∧ ((p4 → True) → (True ∨ p2))) → True) ∨ p4)) ∨ True) ∨ p3)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_134674705490646527367838612313 : ((((p1 ∨ (p2 → ((True ∨ (True ∨ True)) → p4))) ∨ (((True → (((False → p3) ∨ True) → True)) ∨ p5) → p3)) → False) ∨ ((False ∨ p1) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_179238167311408878892485606027 : ((p5 ∧ (((p5 ∧ (p1 ∨ False)) ∨ (False → (p5 ∨ (p5 ∧ True)))) ∨ p4)) ∨ ((((True ∨ True) → p1) ∨ p2) ∨ ((p1 → p3) ∨ (False → p1)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_205714079820431950794919220772 : (((p2 → p1) ∨ ((p3 → p5) → p2)) ∨ ((False ∨ (False ∨ (((p2 ∧ False) ∧ (True ∨ (p4 ∧ ((p5 ∧ (p5 ∧ p4)) → p3)))) → p1))) ∨ p2)) := by
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
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- Conjunctions on the left can always be decomposed.
  let h4 := h2.left
  let h5 := h2.right
  -- False on the left can always be used.
  apply False.elim h5



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_258948020189741345102623337302 : ((True → p3) → (((True ∧ True) ∧ (((p4 → (((True ∨ (False ∨ p4)) ∧ p1) ∧ p4)) → p5) ∨ ((p1 ∧ (p5 ∧ (p2 ∨ p3))) ∨ True))) ∨ p3)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_111416760543538800508177409710 : (((p3 ∨ ((((False → True) → (((((p1 → False) ∧ p5) ∨ p3) ∨ True) ∨ p5)) ∧ p4) ∧ (((True ∨ p5) ∧ p4) ∨ p5))) ∧ p3) ∨ (True ∨ p4)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_354808259664274540438866432259 : (p5 → (((p3 → ((p3 → False) ∧ True)) ∨ (p5 ∧ ((((((((False ∧ p4) ∨ p2) → (p2 ∧ True)) → False) ∨ True) ∨ p4) → False) → False))) ∨ False)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- One of the premise coincides with the conclusion.
  exact h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
  have h3 : ((((((False ∧ p4) ∨ p2) → (p2 ∧ True)) → False) ∨ True) ∨ p4) := by
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h2, we can now drive its conclusion.
  let h4 := h2 h3
  -- False on the left can always be used.
  apply False.elim h4



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_119050893327818413279106855604 : ((p1 → (((p4 ∨ False) ∧ ((p2 → (p2 ∧ ((p1 ∨ p3) ∨ (p2 → p5)))) ∧ ((p5 → (p1 → (p2 ∨ p2))) → p3))) ∨ p1)) ∨ (p4 ∧ p5)) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_204329567778606938264114136269 : (((p4 ∧ ((p4 ∨ p4) ∧ p3)) ∧ p3) ∨ (((((p3 ∨ p3) ∨ p4) ∧ p1) ∧ p2) → ((True ∨ ((p2 ∧ (p4 → (p4 ∨ False))) → True)) ∨ True))) := by
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
    -- Disjunctions on the left can always be decomposed.
    cases h6
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
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_668696520974242267149319719644 : (((((((p1 → (p3 ∧ (p2 ∧ p4))) → (((p2 ∨ (False ∨ p4)) ∨ (p5 → p2)) ∧ (True ∨ p3))) ∧ p5) ∨ p1) ∨ ((p1 ∨ p3) → p2)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_39455496954554240709979445525 : (((p5 ∧ (((p1 ∧ p1) → p3) ∨ ((((((p5 → p3) ∧ (p3 → True)) → p1) → p1) → (p4 ∨ (p3 → (p1 ∨ p4)))) ∧ p3))) ∧ p3) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_919091447191857938104495909429 : (((((False → (p4 ∨ (((True → p2) → p2) ∧ (True ∨ p3)))) → (p3 ∧ p2)) ∧ (False ∨ (p5 → ((True ∧ ((True ∧ p4) → True)) ∧ True)))) → p3) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
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
    -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
    have h6 : (False → (p4 ∨ (((True → p2) → p2) ∧ (True ∨ p3)))) := by
      -- Implications on the right can always be decomposed.
      intro h7
      -- False on the left can always be used.
      apply False.elim h7
    -- We have shown the premise of h2, we can now drive its conclusion.
    let h8 := h2 h6
    -- We need to get the left conjuct of h8 based on <expert-advice>.
    let h9 := h8.left
    -- One of the premise coincides with the conclusion.
    exact h9
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_188411633100548531468340400918 : ((((((p5 ∧ False) ∧ p5) ∧ p1) → (p4 ∨ p3)) → True) ∧ (p3 ∨ (((p2 ∧ (p1 ∧ ((True ∧ (p1 ∨ True)) → False))) ∧ False) ∨ (p4 ∨ True)))) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
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
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_44118100300412396162946175953 : ((((((True ∨ (p2 → p1)) ∨ ((p2 → False) ∨ (p4 ∧ (p1 ∨ p1)))) ∨ (((p1 ∨ p1) → p1) ∧ p2)) ∨ ((p3 ∨ True) ∨ p1)) → False) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_141455132671877308575307636996 : ((((p2 ∨ p5) → p1) ∧ (((((False ∨ ((p5 ∧ False) ∧ ((p1 → True) → p2))) ∧ p2) ∨ (p2 → p2)) ∨ p4) → p5)) → (p3 ∨ (p5 ∨ p4))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- We want to use the implication h3 based on <expert-advice>. So we show its premise.
  have h4 : ((((False ∨ ((p5 ∧ False) ∧ ((p1 → True) → p2))) ∧ p2) ∨ (p2 → p2)) ∨ p4) := by
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h5
    -- One of the premise coincides with the conclusion.
    exact h5
  -- We have shown the premise of h3, we can now drive its conclusion.
  let h6 := h3 h4
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- One of the premise coincides with the conclusion.
  exact h6



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_304721903097128657794449327497 : (p1 ∨ (((((True → p5) → (False ∧ ((((True → p2) ∧ p2) ∧ p4) → p3))) ∧ (p1 → p2)) ∨ ((p3 ∨ (p4 ∧ p1)) ∧ p1)) ∨ (p2 ∨ True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_33779513791680437797128444591 : ((p5 ∨ ((((((p1 → True) ∧ p5) → (p1 ∧ p3)) ∧ (False → p5)) ∨ (False ∧ ((((False ∧ p3) ∨ False) → False) ∧ p2))) ∨ (p5 → p5))) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
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
theorem thm_5_vars_165823593024756455738976546687 : (((p3 ∨ (p2 ∧ p1)) ∧ (p3 ∧ ((p3 ∨ (p2 ∧ (p3 → p2))) → ((p4 → False) ∧ True)))) ∨ (((False ∧ p5) ∧ p4) → (p1 → (p2 → p5)))) := by
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
  -- Conjunctions on the left can always be decomposed.
  let h6 := h4.left
  let h7 := h4.right
  -- False on the left can always be used.
  apply False.elim h6



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_901867899252029860549532846972 : (((((((((p1 ∨ p2) ∧ p2) ∨ ((False ∧ (True → p3)) → (p4 → (False ∧ p3)))) → False) → p5) → False) ∧ ((p1 ∧ False) → (p4 ∨ True))) → False) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
  have h4 : (((((p1 ∨ p2) ∧ p2) ∨ ((False ∧ (True → p3)) → (p4 → (False ∧ p3)))) → False) → p5) := by
    -- Implications on the right can always be decomposed.
    intro h5
    -- We want to use the implication h5 based on <expert-advice>. So we show its premise.
    have h6 : (((p1 ∨ p2) ∧ p2) ∨ ((False ∧ (True → p3)) → (p4 → (False ∧ p3)))) := by
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Implications on the right can always be decomposed.
      intro h7
      -- Implications on the right can always be decomposed.
      intro h8
      -- Conjunctions on the right can always be decomposed.
      apply And.intro
      -- Conjunctions on the left can always be decomposed.
      let h9 := h7.left
      let h10 := h7.right
      -- False on the left can always be used.
      apply False.elim h9
      -- Conjunctions on the left can always be decomposed.
      let h11 := h7.left
      let h12 := h7.right
      -- False on the left can always be used.
      apply False.elim h11
    -- We have shown the premise of h5, we can now drive its conclusion.
    let h13 := h5 h6
    -- False on the left can always be used.
    apply False.elim h13
  -- We have shown the premise of h2, we can now drive its conclusion.
  let h14 := h2 h4
  -- False on the left can always be used.
  apply False.elim h14
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_220309603130765615208593523728 : (((True ∨ p3) ∧ True) ∧ ((p5 ∨ (False → p4)) → ((p5 → (False ∨ p2)) → (((((p5 ∧ p2) ∨ ((p3 → p5) ∨ p3)) ∨ p4) → False) ∨ True)))) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Disjunctions on the left can always be decomposed.
  cases h1
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
theorem thm_5_vars_781757537735502460242189074051 : (((p2 ∨ (p5 ∨ (((True ∧ p3) → ((False ∧ ((((False ∧ True) → False) ∨ p2) ∨ p4)) → ((p2 → p4) ∧ p4))) → ((p3 ∧ p5) ∧ True)))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_253074057352531223467641637793 : ((True ∧ p4) → ((p5 ∧ ((False ∨ True) ∨ ((p5 → (True ∨ (p4 → (False ∨ False)))) ∨ ((p5 → False) ∨ p2)))) → (p5 → (p3 ∨ (False ∨ p4))))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Implications on the right can always be decomposed.
  intro h3
  -- Conjunctions on the left can always be decomposed.
  let h4 := h2.left
  let h5 := h2.right
  -- Disjunctions on the left can always be decomposed.
  cases h5
  case inl h6 =>
    -- Disjunctions on the left can always be decomposed.
    cases h6
    case inl h7 =>
      -- False on the left can always be used.
      apply False.elim h7
    case inr h8 =>
      -- Conjunctions on the left can always be decomposed.
      let h9 := h1.left
      let h10 := h1.right
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- One of the premise coincides with the conclusion.
      exact h10
  case inr h11 =>
    -- Disjunctions on the left can always be decomposed.
    cases h11
    case inl h12 =>
      -- Conjunctions on the left can always be decomposed.
      let h13 := h1.left
      let h14 := h1.right
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- One of the premise coincides with the conclusion.
      exact h14
    case inr h15 =>
      -- Disjunctions on the left can always be decomposed.
      cases h15
      case inl h16 =>
        -- Conjunctions on the left can always be decomposed.
        let h17 := h1.left
        let h18 := h1.right
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- One of the premise coincides with the conclusion.
        exact h18
      case inr h19 =>
        -- Conjunctions on the left can always be decomposed.
        let h20 := h1.left
        let h21 := h1.right
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- One of the premise coincides with the conclusion.
        exact h21



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_693230514645272369863906193693 : ((((p2 ∨ (((((False ∨ (p2 ∧ p2)) ∨ p1) ∨ (p1 ∨ p3)) ∨ False) ∨ p4)) ∧ ((((True → (True ∧ p2)) ∨ p3) ∨ p3) → (p2 ∨ p5))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_205819088646781406893033435774 : (((p5 ∨ False) → ((p3 → p3) → p4)) ∨ ((False ∨ ((False ∧ (((p3 → p4) ∧ p3) ∧ p2)) ∨ (p5 ∨ (p4 → True)))) ∨ ((False → p5) → p2))) := by
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
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_342751690243908285707605819467 : (p2 → (((p5 ∨ (False → (p3 → (p1 ∧ True)))) → p5) ∨ (((p4 ∨ p1) ∧ (p1 ∨ p1)) → (True ∨ (p1 → ((True → (p1 ∨ True)) ∨ p4)))))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h2
  -- Conjunctions on the left can always be decomposed.
  let h3 := h2.left
  let h4 := h2.right
  -- Disjunctions on the left can always be decomposed.
  cases h3
  case inl h5 =>
    -- Disjunctions on the left can always be decomposed.
    cases h4
    case inl h6 =>
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- True on the right can always be proven directly.
      apply True.intro
    case inr h7 =>
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- True on the right can always be proven directly.
      apply True.intro
  case inr h8 =>
    -- Disjunctions on the left can always be decomposed.
    cases h4
    case inl h9 =>
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- True on the right can always be proven directly.
      apply True.intro
    case inr h10 =>
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- True on the right can always be proven directly.
      apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_129362365486292982363132582315 : (((p1 ∧ (False ∧ (((p1 ∨ False) → (p5 ∧ ((p2 ∨ (True ∧ (p1 ∧ p3))) ∧ (True ∨ p2)))) ∧ (p1 ∨ False)))) ∨ True) ∧ (p2 ∨ (True → True))) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
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
theorem thm_5_vars_66541414452732857806848460872 : ((True → ((p4 ∧ (((True ∧ ((p4 ∧ (((True ∨ p1) ∨ p1) ∧ (p2 ∨ p1))) ∨ p5)) ∨ p4) → ((p3 → (True → True)) ∨ p1))) → p3)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_52572454176363773101726096247 : ((((((False ∧ p1) → p3) → ((p5 ∨ (p4 ∨ p4)) ∧ p4)) ∨ (False ∨ p3)) ∨ ((False ∨ p4) ∧ (((p1 ∧ True) ∧ (p4 ∨ p1)) ∨ p1))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_157606666059192767506513641310 : (((((p4 → p5) → (((False ∨ (p2 ∧ (p3 ∧ False))) → p1) → False)) ∧ p1) ∧ ((True → p2) → p5)) ∨ (((True ∨ p5) ∧ p4) ∨ (True ∨ p1))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_711461451000675526471770978738 : ((((p4 ∨ (p1 → (False ∨ (p2 → p1)))) ∧ (p3 ∧ ((False ∨ ((True ∨ (p4 → p2)) → (True ∧ False))) ∧ (((True ∧ p5) → True) → p1)))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_725615361673591383583596576863 : (((((p4 ∧ True) ∧ p3) ∨ ((p5 → p1) → ((p3 → (((p5 ∨ (True ∨ p3)) ∨ p1) → p5)) → (((p3 ∧ p4) ∨ (True → p4)) → p4)))) ∨ p3) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
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
  -- Disjunctions on the left can always be decomposed.
  cases h3
  case inl h4 =>
    -- Conjunctions on the left can always be decomposed.
    let h5 := h4.left
    let h6 := h4.right
    -- One of the premise coincides with the conclusion.
    exact h6
  case inr h7 =>
    -- We want to use the implication h7 based on <expert-advice>. So we show its premise.
    have h8 : True := by
      -- True on the right can always be proven directly.
      apply True.intro
    -- We have shown the premise of h7, we can now drive its conclusion.
    let h9 := h7 h8
    -- One of the premise coincides with the conclusion.
    exact h9
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_109735912789707840191186981341 : ((p4 ∨ (p3 ∨ (((False ∨ (((p1 → p2) → ((False ∧ (p5 ∨ True)) ∨ p5)) ∨ (p2 ∨ (p3 → p3)))) ∨ p1) ∨ (p5 ∧ p2)))) ∧ (p4 → p4)) := by
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
  -- Implications on the right can always be decomposed.
  intro h2
  -- One of the premise coincides with the conclusion.
  exact h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_58018416093262326453949923628 : (((True ∧ p2) ∧ (((((True ∨ False) ∨ p5) ∧ False) → ((((((p1 → p1) ∧ True) → (p1 → p3)) → p4) ∧ (p4 ∨ p5)) ∧ p2)) → p5)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_228538380643348978195527174374 : ((p1 ∨ (p3 ∧ p2)) ∨ (((((True → p3) → (p2 ∨ True)) → False) ∨ ((((False → p5) ∨ (p2 → (p5 ∧ p5))) → True) ∨ p5)) ∨ (p1 → p5))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
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



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_214827914108829911487448697514 : (((p4 ∨ p4) ∨ (True ∧ False)) ∨ ((((False ∨ ((False ∨ p3) → (p3 ∨ False))) ∧ ((False ∧ p3) ∨ p3)) ∨ True) ∧ (False → (p4 ∨ (p5 → p2))))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- Implications on the right can always be decomposed.
  intro h1
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_53324248957111370177416193444 : (((p4 → ((((False ∧ p2) ∨ False) ∧ p1) ∧ (False ∨ (p4 ∨ False)))) ∨ ((p2 ∨ ((p2 ∨ (p1 → p2)) ∨ (False ∧ True))) ∨ (False → False))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_318615071737972034886130695847 : (p4 ∨ (((p2 ∨ (p2 → p4)) ∨ ((False ∨ (p4 ∧ (((p1 → p3) → (p1 ∨ p3)) → p3))) ∨ ((p5 → p5) ∧ (p2 → p5)))) ∨ (True ∨ p1))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_596548889463007392820077249822 : ((((((True → p3) ∨ (p3 ∧ (p3 ∨ (p1 → p5)))) → ((((p5 ∧ ((p1 → p1) ∨ p4)) ∧ p1) ∧ (True → (p5 → p3))) ∨ p5)) ∧ p1) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_671431521250316766278589092997 : ((((p1 → (p4 ∧ (p1 → ((((p5 → p5) ∨ p1) ∨ p3) → ((False ∧ ((p4 ∧ (p2 ∧ p3)) ∧ p2)) ∧ p3))))) ∨ (True → (p5 → p5))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_60167451059944846946864620126 : (((p5 ∨ True) → ((((((True ∨ p2) ∨ ((True ∧ p5) ∧ True)) → (p4 ∧ p4)) ∨ p2) → (True → False)) ∨ (((p5 → p3) ∧ p2) → p2))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_177878163328483713948885334857 : (((((((p4 → (p1 ∧ p3)) ∨ p3) ∨ p5) ∧ (True → p5)) → p4) ∨ True) ∨ ((False ∧ ((((True ∨ p3) ∨ p1) ∨ p2) → (p1 → p4))) ∧ p1)) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_51150288249514990174046320220 : ((((((p4 → False) → p1) → (True ∧ (p4 ∧ (True ∧ (p3 → (p1 ∧ (False → p2))))))) → False) ∨ ((p5 → (p5 → False)) → (p4 → True))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_307687625548235279263545640085 : (p1 ∨ (p2 → (((True ∨ (p5 ∨ p3)) → ((True ∨ (True ∨ ((p3 → p5) ∨ p4))) ∧ p1)) ∨ (p1 ∨ ((((p2 ∨ False) → p3) ∨ p2) ∨ p3))))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_156966955401456121069129760635 : ((((p1 ∧ ((p5 ∧ p4) ∨ (((False → True) ∨ p5) ∨ False))) ∧ (((p3 ∨ True) ∨ p4) → p1)) ∨ True) ∨ (p5 ∨ (((p5 ∧ p5) → True) ∧ p2))) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_351096466897553244287434467056 : (p4 → (((False → (p3 ∨ p2)) → ((((p5 ∨ (True → ((False ∧ (True → (p2 ∧ p4))) ∨ False))) ∨ p5) → p3) ∧ (p5 ∧ p1))) → (p4 ∧ p1))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- One of the premise coincides with the conclusion.
  exact h1
  -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
  have h3 : (False → (p3 ∨ p2)) := by
    -- Implications on the right can always be decomposed.
    intro h4
    -- False on the left can always be used.
    apply False.elim h4
  -- We have shown the premise of h2, we can now drive its conclusion.
  let h5 := h2 h3
  -- We need to get the right conjuct of h5 based on <expert-advice>.
  let h6 := h5.right
  -- We need to get the right conjuct of h6 based on <expert-advice>.
  let h7 := h6.right
  -- One of the premise coincides with the conclusion.
  exact h7



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_712268301926723917832505282 : (((((p1 ∨ (True → False)) → (p3 ∨ p4)) → False) ∨ (False → ((((True ∧ (False ∧ True)) → (p5 → (p5 ∨ True))) → True) ∧ p3))) ∨ p2) := by
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
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_309343834990712471951911642286 : (p2 ∨ ((((False ∨ (True → ((False ∨ (p3 → p4)) → p4))) ∧ (False → ((True → p1) ∧ p3))) ∧ (p5 → (False ∨ (p2 ∨ p3)))) ∨ (False → False))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_204799856597469391057881753844 : (((((False ∧ p4) ∧ True) ∨ p5) → False) ∨ ((((((p3 ∨ (p1 → False)) ∧ p4) ∧ p4) ∨ p3) ∧ False) ∨ ((((p1 → p1) ∨ False) ∨ p3) ∨ p3))) := by
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
  -- Implications on the right can always be decomposed.
  intro h1
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_313226779450120189074219743469 : (p3 ∨ (((p3 ∧ p5) ∧ (((((p3 → p1) ∨ ((p4 → False) → p5)) ∨ (((True → p2) ∧ True) ∧ ((p1 ∧ p2) ∨ p4))) → False) → p2)) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_643404061320940303161396445330 : ((((p4 ∧ (((p2 ∨ ((((p5 → ((p4 ∧ True) ∨ (True → p1))) ∧ p2) ∨ False) ∧ p3)) ∨ (p1 ∧ (p1 ∨ (p2 ∧ p1)))) ∨ p2)) → False) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_259423396373166983701321557303 : ((False → p3) → (p4 → ((p4 → ((((p3 → False) ∧ (p3 ∧ False)) ∨ p4) → ((True ∨ True) ∧ False))) → ((p2 ∧ ((p3 ∨ p3) ∨ p2)) ∨ p1)))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Implications on the right can always be decomposed.
  intro h3
  -- We want to use the implication h3 based on <expert-advice>. So we show its premise.
  have h4 : p4 := by
    -- One of the premise coincides with the conclusion.
    exact h2
  -- We have shown the premise of h3, we can now drive its conclusion.
  let h5 := h3 h4
  -- We want to use the implication h5 based on <expert-advice>. So we show its premise.
  have h6 : (((p3 → False) ∧ (p3 ∧ False)) ∨ p4) := by
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h2
  -- We have shown the premise of h5, we can now drive its conclusion.
  let h7 := h5 h6
  -- We need to get the right conjuct of h7 based on <expert-advice>.
  let h8 := h7.right
  -- False on the left can always be used.
  apply False.elim h8



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_231318245718058892981819240044 : (((True → False) ∨ p4) → (p2 ∨ (p4 ∨ (p5 ∨ ((p4 ∨ ((p3 → (p3 ∨ p1)) → (p4 ∧ True))) ∨ (((False → p5) ∨ (p1 → p4)) ∨ True)))))) := by
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
    -- False on the left can always be used.
    apply False.elim h4
  case inr h5 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- One of the premise coincides with the conclusion.
    exact h5



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_326955146043155143217797235541 : (True → ((((p5 ∨ (p3 ∧ p3)) ∧ ((p4 ∨ (True ∨ (False ∧ p3))) → (((p5 → ((False → True) ∨ False)) ∨ p4) ∧ p4))) ∨ (p4 → p3)) ∨ True)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_232959196695573091204558391130 : ((p3 ∧ (p5 ∨ p3)) → ((p5 ∧ (True → p1)) ∨ (((p1 → ((p4 ∧ p5) ∧ p4)) ∨ ((p1 → (p3 ∧ (p3 ∧ p4))) ∨ p1)) ∨ (True ∨ p3)))) := by
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
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- True on the right can always be proven directly.
    apply True.intro
  case inr h5 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- True on the right can always be proven directly.
    apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_172916238215545837345981431686 : ((p2 ∧ (False ∧ (p2 ∧ (((p2 ∧ ((p4 → (p5 → True)) → True)) ∨ p4) → p1)))) ∨ (((((p3 ∨ False) ∧ False) ∧ p3) ∨ (False → False)) ∧ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
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



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_228652964783310652342747449338 : ((p2 ∨ (p2 ∧ p4)) ∨ (p3 → ((((((p4 ∨ ((p2 ∨ True) ∨ p1)) ∨ ((p2 → p5) → True)) ∧ (p3 → True)) ∨ p3) ∧ (p4 → p4)) ∨ p3))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_602001932664051145958221582015 : ((((p5 ∧ ((p2 ∧ ((p4 ∧ False) ∧ (((p3 ∧ True) ∨ ((p4 ∨ p2) ∧ p1)) ∨ ((p3 ∧ p2) ∧ ((False ∧ p3) ∧ p2))))) ∧ p2)) ∧ p3) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_191811894746335838359635134527 : ((p2 ∨ ((p2 ∨ p4) → (p3 ∨ ((p1 → False) → p1)))) ∨ (((p3 ∧ (True ∧ p4)) ∧ p5) → (p2 ∨ (True ∧ (p3 ∨ (p2 ∨ (False → p5))))))) := by
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
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- One of the premise coincides with the conclusion.
  exact h4



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_48186566558992004493668334163 : ((((False ∨ p1) ∨ (((True → (p3 → p5)) ∨ (p3 ∧ ((p1 ∧ ((p3 → p5) ∧ (p1 ∨ False))) ∨ (p2 ∨ p4)))) → p1)) → (False ∧ p1)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_686868636367376008739605566070 : ((((True ∨ ((p3 ∨ ((p5 ∨ ((((False ∧ False) → p3) → p5) → p5)) ∧ (p2 ∧ p3))) ∨ p3)) → ((p1 → False) ∨ ((p5 ∨ p3) ∨ True))) ∨ False) ∧ True) := by
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
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro
  case inr h3 =>
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
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- True on the right can always be proven directly.
      apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_56188668839797817150512546253 : (((p4 ∧ (p4 ∧ (p1 ∧ p5))) ∨ (p2 → ((((p3 ∨ ((p2 ∨ True) ∧ p1)) ∨ False) ∨ True) ∨ ((p1 ∨ p1) ∧ ((p2 → False) ∧ False))))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_80907612383675210340067934873 : (((((((p5 ∨ ((p2 → p2) → (p2 ∨ False))) ∧ p3) ∧ ((True ∨ False) ∧ (p4 ∨ (p1 ∧ p4)))) ∨ False) → p5) ∧ (True → (p3 ∧ False))) → p1) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- We want to use the implication h3 based on <expert-advice>. So we show its premise.
  have h4 : True := by
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h3, we can now drive its conclusion.
  let h5 := h3 h4
  -- We need to get the right conjuct of h5 based on <expert-advice>.
  let h6 := h5.right
  -- False on the left can always be used.
  apply False.elim h6



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_245432399630986372625692478398 : ((p2 ∧ p4) ∨ ((p1 ∨ ((p4 ∧ True) → p1)) → (((((p4 ∧ p4) → ((p4 → p2) ∨ p1)) → p3) → (p5 ∨ (True ∧ p3))) ∨ (p5 → False)))) := by
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
    -- Conjunctions on the right can always be decomposed.
    apply And.intro
    -- True on the right can always be proven directly.
    apply True.intro
    -- We want to use the implication h3 based on <expert-advice>. So we show its premise.
    have h4 : ((p4 ∧ p4) → ((p4 → p2) ∨ p1)) := by
      -- Implications on the right can always be decomposed.
      intro h5
      -- Conjunctions on the left can always be decomposed.
      let h6 := h5.left
      let h7 := h5.right
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- One of the premise coincides with the conclusion.
      exact h2
    -- We have shown the premise of h3, we can now drive its conclusion.
    let h8 := h3 h4
    -- One of the premise coincides with the conclusion.
    exact h8
  case inr h9 =>
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Implications on the right can always be decomposed.
    intro h10
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Conjunctions on the right can always be decomposed.
    apply And.intro
    -- True on the right can always be proven directly.
    apply True.intro
    -- We want to use the implication h10 based on <expert-advice>. So we show its premise.
    have h11 : ((p4 ∧ p4) → ((p4 → p2) ∨ p1)) := by
      -- Implications on the right can always be decomposed.
      intro h12
      -- Conjunctions on the left can always be decomposed.
      let h13 := h12.left
      let h14 := h12.right
      -- We want to use the implication h9 based on <expert-advice>. So we show its premise.
      have h15 : (p4 ∧ True) := by
        -- Conjunctions on the right can always be decomposed.
        apply And.intro
        -- One of the premise coincides with the conclusion.
        exact h14
        -- True on the right can always be proven directly.
        apply True.intro
      -- We have shown the premise of h9, we can now drive its conclusion.
      let h16 := h9 h15
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- One of the premise coincides with the conclusion.
      exact h16
    -- We have shown the premise of h10, we can now drive its conclusion.
    let h17 := h10 h11
    -- One of the premise coincides with the conclusion.
    exact h17



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_135820757510944739052342922322 : (((((False ∨ ((p4 ∧ (p3 ∧ p4)) ∨ (p4 → False))) → p1) → p5) ∧ (p4 ∨ ((False ∨ p2) → ((p5 ∧ True) ∨ p1)))) ∨ ((p4 → True) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_330538396659049875787587620041 : (True → (p5 ∨ ((((((((p2 ∨ p3) ∧ p4) ∨ p5) → p5) ∨ (((p3 ∧ True) → True) → False)) ∨ (False → (False → (p1 ∨ p4)))) → p3) ∨ True))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_174725005909799656447576380407 : ((((p4 → p3) ∧ p4) → (((True ∨ p4) ∨ (True → ((p5 ∨ p4) → p1))) ∧ True)) → (p1 → (False ∨ ((True → ((p3 → p3) ∧ False)) → p4)))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h3
  -- We want to use the implication h3 based on <expert-advice>. So we show its premise.
  have h4 : True := by
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h3, we can now drive its conclusion.
  let h5 := h3 h4
  -- We need to get the right conjuct of h5 based on <expert-advice>.
  let h6 := h5.right
  -- False on the left can always be used.
  apply False.elim h6



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_133998681043235780030867458544 : (((((p1 ∧ (p3 → False)) ∧ (((p5 → p3) ∧ ((p4 ∧ (p5 → True)) → (True → (p4 → p3)))) ∨ p4)) ∧ p1) ∨ True) ∨ ((True ∨ p1) ∧ False)) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_351723769585990845126050087702 : (p4 → ((((p4 → ((p5 ∨ (((False → p5) ∧ p2) → p3)) ∨ p3)) ∨ p1) → False) ∨ (True ∧ ((True ∧ ((True ∨ p5) ∨ p5)) ∨ (p4 ∨ False))))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_656412887979840772575218175794 : ((((((True ∨ (p2 ∨ p1)) → (((p4 → False) → False) ∨ p3)) ∧ ((p2 → p1) ∨ (True ∧ (p2 ∧ (True ∨ (p4 ∨ p1)))))) ∨ (p1 ∧ p1)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_336305291665668557713149751474 : (p1 → (((((p3 → False) ∧ p2) ∨ (p4 → p2)) → ((((p4 ∧ p5) → (p1 ∧ p2)) → ((p5 ∧ p2) ∨ p2)) ∧ (p4 ∧ (p5 → False)))) ∨ True)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_52197710272290748121462977719 : ((((True → (False ∨ p1)) ∨ (p4 ∧ ((p1 ∧ (p2 ∨ (p5 ∧ (False ∧ p1)))) ∧ p4))) → (((((False → p3) → p5) ∨ False) ∧ True) ∨ True)) ∨ p2) := by
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
    -- Conjunctions on the left can always be decomposed.
    let h4 := h3.left
    let h5 := h3.right
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
      -- True on the right can always be proven directly.
      apply True.intro
    case inr h11 =>
      -- Conjunctions on the left can always be decomposed.
      let h12 := h11.left
      let h13 := h11.right
      -- Conjunctions on the left can always be decomposed.
      let h14 := h13.left
      let h15 := h13.right
      -- False on the left can always be used.
      apply False.elim h14



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_303909628179175606847152321885 : (p1 ∨ ((((p5 ∧ p5) ∨ ((p2 → p5) → ((False → (p3 ∨ p5)) ∨ p5))) ∧ ((False ∧ (p3 → p2)) ∨ (((p4 → p1) ∧ False) → p2))) ∨ p1)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
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
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h3
  -- Conjunctions on the left can always be decomposed.
  let h4 := h3.left
  let h5 := h3.right
  -- False on the left can always be used.
  apply False.elim h5



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_731296278393363352073024854394 : ((((p4 ∨ (True ∨ True)) → (((p5 ∧ (((p4 ∨ (False ∨ False)) → ((p5 ∨ (p1 → p4)) ∧ p3)) → True)) ∧ (p4 ∨ (p1 ∨ p2))) ∨ True)) ∨ p3) ∧ True) := by
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
    -- True on the right can always be proven directly.
    apply True.intro
  case inr h3 =>
    -- Disjunctions on the left can always be decomposed.
    cases h3
    case inl h4 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- True on the right can always be proven directly.
      apply True.intro
    case inr h5 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- True on the right can always be proven directly.
      apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_306589146105047721701868856694 : (p1 ∨ ((True → p1) → (((p1 ∨ p1) ∧ (p1 ∧ ((((((False → False) ∨ p2) ∧ True) → (False → p2)) → p5) ∨ ((True ∨ p5) → p1)))) ∨ p3))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h2 : True := by
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h3 := h1 h2
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- One of the premise coincides with the conclusion.
  exact h3
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- One of the premise coincides with the conclusion.
  exact h3
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
theorem thm_5_vars_708578027803476878491584110341 : ((((((p4 ∨ False) → ((p1 → p2) ∧ p1)) ∨ p3) → (True → ((((((True ∨ p4) ∧ False) → p2) ∧ (True ∧ p1)) → p4) ∨ (False → p2)))) ∨ p5) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
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
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_127587683302330349048173737647 : ((p4 ∨ (p1 ∨ ((p3 ∧ ((p5 ∧ p1) → False)) ∧ ((p3 ∧ (p1 ∨ ((p1 ∨ p2) ∨ True))) ∨ ((p3 ∨ (p5 ∨ True)) → p3))))) → (p2 ∨ True)) := by
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
    -- Disjunctions on the left can always be decomposed.
    cases h3
    case inl h4 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- True on the right can always be proven directly.
      apply True.intro
    case inr h5 =>
      -- Conjunctions on the left can always be decomposed.
      let h6 := h5.left
      let h7 := h5.right
      -- Conjunctions on the left can always be decomposed.
      let h8 := h6.left
      let h9 := h6.right
      -- Disjunctions on the left can always be decomposed.
      cases h7
      case inl h10 =>
        -- Conjunctions on the left can always be decomposed.
        let h11 := h10.left
        let h12 := h10.right
        -- Disjunctions on the left can always be decomposed.
        cases h12
        case inl h13 =>
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- True on the right can always be proven directly.
          apply True.intro
        case inr h14 =>
          -- Disjunctions on the left can always be decomposed.
          cases h14
          case inl h15 =>
            -- Disjunctions on the left can always be decomposed.
            cases h15
            case inl h16 =>
              -- Show the right disjunct based on <expert-advice>.
              apply Or.inr
              -- True on the right can always be proven directly.
              apply True.intro
            case inr h17 =>
              -- Show the left disjunct based on <expert-advice>.
              apply Or.inl
              -- One of the premise coincides with the conclusion.
              exact h17
          case inr h18 =>
            -- Show the right disjunct based on <expert-advice>.
            apply Or.inr
            -- True on the right can always be proven directly.
            apply True.intro
      case inr h19 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- True on the right can always be proven directly.
        apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_39939567604458163488452725301 : (((p3 → (True → (((True → (True ∨ p2)) ∨ (p2 → p5)) → ((((p1 → p5) ∧ p1) ∧ (p2 → (p3 → p5))) ∧ (p4 ∨ True))))) ∧ False) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_65962277657176502976288354467 : ((p4 ∨ (p5 ∨ (((p5 → False) ∧ (((((p4 ∨ (False ∧ ((p4 ∧ p2) ∨ p4))) ∧ (True → p1)) ∨ p5) ∨ p3) ∨ (p4 ∧ p1))) ∨ True))) ∨ p5) := by
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
theorem thm_5_vars_749435875311642143954210296079 : (((True ∧ ((((p5 → (((((p3 ∧ True) ∨ p3) ∧ (p1 → p4)) ∨ False) ∨ False)) ∨ (p1 ∨ True)) ∧ (p2 → ((p2 ∨ True) → p2))) ∧ True)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_141437318601330093958076793829 : ((((False ∧ p5) ∨ True) ∧ (True → ((p1 ∨ ((p1 ∨ False) ∧ p5)) ∧ ((p2 → (((p5 ∨ False) ∧ p5) → p4)) ∧ True)))) → ((p4 ∨ p5) ∨ True)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- Disjunctions on the left can always be decomposed.
  cases h2
  case inl h4 =>
    -- Conjunctions on the left can always be decomposed.
    let h5 := h4.left
    let h6 := h4.right
    -- False on the left can always be used.
    apply False.elim h5
  case inr h7 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_172141582896814312585416391921 : (((p5 ∧ (((p1 ∧ p1) ∨ (False ∨ p4)) ∨ (False ∨ p4))) ∧ ((p5 → p5) → p1)) ∨ ((((p4 ∧ True) ∨ p5) ∨ (p1 ∨ False)) → (p1 → p1))) := by
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
      -- Conjunctions on the left can always be decomposed.
      let h5 := h4.left
      let h6 := h4.right
      -- One of the premise coincides with the conclusion.
      exact h2
    case inr h7 =>
      -- One of the premise coincides with the conclusion.
      exact h2
  case inr h8 =>
    -- Disjunctions on the left can always be decomposed.
    cases h8
    case inl h9 =>
      -- One of the premise coincides with the conclusion.
      exact h9
    case inr h10 =>
      -- False on the left can always be used.
      apply False.elim h10



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_301184079412868343626887078056 : (False ∨ (((p4 → (p4 ∨ True)) → ((p3 ∨ False) ∧ p1)) → ((((p5 ∨ ((p2 ∨ p1) ∧ (True → ((p2 → True) ∧ p1)))) → p2) ∧ False) ∨ True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_313193434467602541780177052119 : (p3 ∨ (((((True → p5) ∧ p5) → True) ∧ (((((((p4 → p2) → (p5 ∧ (p1 → (False → p2)))) ∧ p1) ∨ p3) ∨ True) ∨ p1) ∨ p3)) ∨ p1)) := by
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
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_96786570843085703666111439066 : ((p1 ∨ ((((((p5 ∨ p2) ∧ p2) ∨ (p4 → (((p2 ∧ (p1 → False)) → ((p3 ∨ p5) → p5)) ∧ p5))) ∨ p2) ∨ p5) ∧ (True → False))) → p1) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h2 =>
    -- One of the premise coincides with the conclusion.
    exact h2
  case inr h3 =>
    -- Conjunctions on the left can always be decomposed.
    let h4 := h3.left
    let h5 := h3.right
    -- Disjunctions on the left can always be decomposed.
    cases h4
    case inl h6 =>
      -- Disjunctions on the left can always be decomposed.
      cases h6
      case inl h7 =>
        -- Disjunctions on the left can always be decomposed.
        cases h7
        case inl h8 =>
          -- Conjunctions on the left can always be decomposed.
          let h9 := h8.left
          let h10 := h8.right
          -- Disjunctions on the left can always be decomposed.
          cases h9
          case inl h11 =>
            -- We want to use the implication h5 based on <expert-advice>. So we show its premise.
            have h12 : True := by
              -- True on the right can always be proven directly.
              apply True.intro
            -- We have shown the premise of h5, we can now drive its conclusion.
            let h13 := h5 h12
            -- False on the left can always be used.
            apply False.elim h13
          case inr h14 =>
            -- We want to use the implication h5 based on <expert-advice>. So we show its premise.
            have h15 : True := by
              -- True on the right can always be proven directly.
              apply True.intro
            -- We have shown the premise of h5, we can now drive its conclusion.
            let h16 := h5 h15
            -- False on the left can always be used.
            apply False.elim h16
        case inr h17 =>
          -- We want to use the implication h5 based on <expert-advice>. So we show its premise.
          have h18 : True := by
            -- True on the right can always be proven directly.
            apply True.intro
          -- We have shown the premise of h5, we can now drive its conclusion.
          let h19 := h5 h18
          -- False on the left can always be used.
          apply False.elim h19
      case inr h20 =>
        -- We want to use the implication h5 based on <expert-advice>. So we show its premise.
        have h21 : True := by
          -- True on the right can always be proven directly.
          apply True.intro
        -- We have shown the premise of h5, we can now drive its conclusion.
        let h22 := h5 h21
        -- False on the left can always be used.
        apply False.elim h22
    case inr h23 =>
      -- We want to use the implication h5 based on <expert-advice>. So we show its premise.
      have h24 : True := by
        -- True on the right can always be proven directly.
        apply True.intro
      -- We have shown the premise of h5, we can now drive its conclusion.
      let h25 := h5 h24
      -- False on the left can always be used.
      apply False.elim h25



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_158984921842705668913953716154 : ((p3 ∨ (((p3 ∧ (p1 ∨ True)) ∧ False) ∧ (((True → (p5 ∧ (p2 ∨ p2))) ∧ (p4 → p4)) ∧ p3))) ∨ (((False ∨ (p3 → p3)) ∨ p3) ∨ p5)) := by
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
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_251824926853884105003133278618 : ((p3 → p4) ∨ (p2 ∨ ((((p2 → (False ∨ (((True ∧ p2) → ((p5 ∧ p1) ∧ p5)) ∨ p4))) ∨ False) ∨ p2) → (p1 → ((p5 → p3) ∨ p1))))) := by
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
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- One of the premise coincides with the conclusion.
      exact h2
    case inr h5 =>
      -- False on the left can always be used.
      apply False.elim h5
  case inr h6 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h2



