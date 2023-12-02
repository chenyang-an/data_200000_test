variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_318604181890060528350266037805 : (p4 ∨ ((((((False → (p5 → p4)) ∨ p5) → p1) → p4) → (((((p3 → (False → p5)) ∧ (False ∨ p2)) ∨ p5) ∧ p4) → p3)) ∨ (True ∨ p4))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_42021313893419295085405305308 : ((((False ∧ p1) ∨ ((((((False ∧ p5) → (p2 → p1)) ∧ p3) ∧ (p5 → (((p2 ∧ True) ∨ p1) ∨ (p3 → p1)))) ∨ True) ∨ p2)) ∨ True) ∨ p1) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_51634637757174041008211154375 : ((((((p3 ∨ ((((p2 ∨ p3) → p4) → p3) ∨ (p2 ∨ p4))) ∧ p4) → False) ∨ p2) ∧ (p4 → (((p2 ∧ p5) ∧ (False ∨ p1)) → p3))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_184982458316693828698011663070 : (((p3 → (p3 ∨ p1)) → (p5 ∨ (((True ∨ False) ∨ False) → p4))) ∨ (True ∨ (p4 ∨ ((((p5 ∧ (True → True)) → (p2 → p2)) ∨ p5) ∨ False)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_40272228088551992479930446972 : ((((True → ((((p2 ∧ (True ∨ ((((p1 ∨ True) ∧ p3) ∧ ((p2 → True) → False)) ∨ p1))) ∧ (False → p4)) ∨ p5) → p4)) ∧ p1) ∨ True) ∨ p4) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_902224502456250916920738399695 : (((((p2 → (((p2 → p3) ∧ ((((p2 ∨ p1) ∨ (p5 → False)) → p1) ∨ p5)) ∨ True)) → (p1 ∧ False)) ∧ ((p4 ∧ p2) → (False → p1))) → p1) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
  have h4 : (p2 → (((p2 → p3) ∧ ((((p2 ∨ p1) ∨ (p5 → False)) → p1) ∨ p5)) ∨ True)) := by
    -- Implications on the right can always be decomposed.
    intro h5
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
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
theorem thm_5_vars_229629257395870988831086690121 : ((p3 → (p1 ∨ p2)) ∨ (((((((p3 → (p2 ∨ True)) ∧ (p5 ∧ p1)) ∨ p2) ∨ p4) ∧ (p3 ∨ ((p1 ∨ p5) ∧ False))) ∨ True) ∨ (p2 ∨ True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_69260130070892114000128973932 : ((p5 → ((True ∨ p3) ∧ ((p2 → False) → ((p1 ∨ p3) ∧ ((((p2 ∧ (p3 ∨ p2)) ∨ p1) → (p3 ∧ p5)) ∨ ((False ∧ p1) ∧ p2)))))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_172357449508785733474790033344 : (((((p2 → p5) ∧ (True → p5)) → p2) ∨ (p3 ∨ (p3 → ((p5 ∨ p5) → p2)))) ∨ (((p5 → p3) ∧ p5) → (((p5 ∧ False) ∧ p4) → True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_179541355499400195053800074657 : ((p1 → ((p1 ∧ ((p4 → False) ∨ p5)) → (p2 ∨ ((p3 ∧ p4) ∧ p3)))) ∨ ((False → (((p3 → (p4 ∨ (p3 → True))) ∧ p3) → p3)) ∧ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Conjunctions on the left can always be decomposed.
  let h3 := h2.left
  let h4 := h2.right
  -- False on the left can always be used.
  apply False.elim h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_785540407316274590923327133658 : (((p4 ∨ ((p1 ∨ ((p5 ∧ ((((True → ((True ∨ ((False → p1) → p2)) ∨ p3)) → (False ∨ False)) → (p1 ∨ p1)) ∧ p2)) → p1)) ∨ p3)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_785696134897058347289188193045 : (((p4 ∨ ((((False → ((p1 ∨ (p4 ∨ True)) ∨ ((True ∨ p4) → p3))) ∧ ((p5 → p5) ∨ p1)) ∧ ((True ∧ p2) ∨ (p5 ∧ p2))) → False)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_73566884852739214726841198103 : ((((p4 ∨ (((False ∨ True) ∨ p4) ∨ ((p2 → (p3 ∧ True)) ∧ (((True → p5) → (p4 ∧ True)) ∧ p3)))) → ((p4 → p5) ∧ False)) ∨ False) → p4) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h2 =>
    -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
    have h3 : (p4 ∨ (((False ∨ True) ∨ p4) ∨ ((p2 → (p3 ∧ True)) ∧ (((True → p5) → (p4 ∧ True)) ∧ p3)))) := by
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
    -- We have shown the premise of h2, we can now drive its conclusion.
    let h4 := h2 h3
    -- We need to get the right conjuct of h4 based on <expert-advice>.
    let h5 := h4.right
    -- False on the left can always be used.
    apply False.elim h5
  case inr h6 =>
    -- False on the left can always be used.
    apply False.elim h6



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_178752162150148146110843166521 : ((((p2 ∨ p4) ∧ p5) ∧ (p3 → ((p3 ∨ (False → p5)) ∧ (False ∧ False)))) ∨ ((True → ((p2 ∨ False) ∧ (p1 → (True ∧ (p5 ∨ p5))))) → p2)) := by
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
  -- We need to get the left conjuct of h3 based on <expert-advice>.
  let h4 := h3.left
  -- Disjunctions on the left can always be decomposed.
  cases h4
  case inl h5 =>
    -- One of the premise coincides with the conclusion.
    exact h5
  case inr h6 =>
    -- False on the left can always be used.
    apply False.elim h6



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_343665877924201928813956182476 : (p2 → (True ∧ (p5 ∨ ((((((p2 → p3) ∨ True) → p2) ∧ p5) → p1) ∨ (((p2 ∨ p3) → (False ∧ ((p1 ∧ p5) ∨ (p3 ∧ p5)))) ∨ True))))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
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
theorem thm_5_vars_134714763123165916721398198016 : ((((p5 ∨ (p5 ∨ False)) ∧ ((False → (False ∧ ((((True ∧ p4) ∨ p2) ∨ (False ∧ p4)) ∨ (p1 ∨ p1)))) ∧ p3)) → False) ∨ ((p3 ∨ False) → p3)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h2 =>
    -- One of the premise coincides with the conclusion.
    exact h2
  case inr h3 =>
    -- False on the left can always be used.
    apply False.elim h3



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_50401081403703753742104777634 : ((((p3 → True) → (p4 ∨ ((p1 ∧ ((p2 → (p5 ∨ ((p1 → (p4 → p5)) ∧ p5))) ∨ p2)) ∨ p4))) ∨ (p4 → (p1 → (False ∨ p4)))) ∨ p4) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
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
theorem thm_5_vars_140718548431494542495075202837 : (((False ∨ (p2 ∧ (((False ∧ False) → (False ∨ (False ∨ (p4 ∨ p3)))) → False))) ∨ ((p4 ∨ ((p1 ∧ p1) ∨ True)) → False)) → (False ∨ (p4 ∧ p2))) := by
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
      -- Conjunctions on the left can always be decomposed.
      let h5 := h4.left
      let h6 := h4.right
      -- We want to use the implication h6 based on <expert-advice>. So we show its premise.
      have h7 : ((False ∧ False) → (False ∨ (False ∨ (p4 ∨ p3)))) := by
        -- Implications on the right can always be decomposed.
        intro h8
        -- Conjunctions on the left can always be decomposed.
        let h9 := h8.left
        let h10 := h8.right
        -- False on the left can always be used.
        apply False.elim h9
      -- We have shown the premise of h6, we can now drive its conclusion.
      let h11 := h6 h7
      -- False on the left can always be used.
      apply False.elim h11
  case inr h12 =>
    -- We want to use the implication h12 based on <expert-advice>. So we show its premise.
    have h13 : (p4 ∨ ((p1 ∧ p1) ∨ True)) := by
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- True on the right can always be proven directly.
      apply True.intro
    -- We have shown the premise of h12, we can now drive its conclusion.
    let h14 := h12 h13
    -- False on the left can always be used.
    apply False.elim h14



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_163038873156712949000686236218 : (((p4 ∧ ((((True → p5) ∨ ((False ∧ False) → True)) ∨ p2) → p2)) ∨ ((p5 ∧ False) → p3)) ∧ ((True ∨ ((p5 ∧ p1) → (p5 ∨ p2))) → True)) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- False on the left can always be used.
  apply False.elim h3
  -- Implications on the right can always be decomposed.
  intro h4
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_248192033165280550547313072653 : ((p2 ∨ p1) ∨ (((p3 → (p1 ∧ ((p5 ∧ ((p3 ∧ (p5 → p1)) ∨ False)) ∨ (p4 ∧ (False → p1))))) ∨ (((p1 ∧ p1) ∨ True) ∧ True)) ∧ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
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
theorem thm_5_vars_55696273912498606967154880165 : ((((True ∧ (p1 ∨ p5)) ∨ p5) ∧ ((((p1 → ((False ∨ ((True → p3) ∧ (True → True))) → (p4 ∧ p3))) ∧ (p1 ∧ p3)) ∨ True) ∧ p2)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_631396094285339672477002848124 : (((((((((False ∨ ((p2 ∧ p5) → p1)) ∧ ((p1 → p4) ∨ p3)) → (((p4 ∧ p5) ∧ p4) ∧ p5)) ∧ True) ∨ (p4 → p1)) → True) → p2) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_810439392335095106859502546592 : (((p5 → ((((p5 ∧ (p3 → (p3 ∨ p3))) ∨ True) → False) → (p5 ∧ (((p1 ∨ p2) ∨ ((p1 ∧ (p3 ∧ p5)) ∨ p2)) ∨ (p5 ∨ p3))))) ∨ p4) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- One of the premise coincides with the conclusion.
  exact h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- One of the premise coincides with the conclusion.
  exact h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_41497250189992009297605062782 : ((((((p4 ∨ (p2 → p3)) ∧ (p5 ∨ p2)) ∧ (p4 → (p3 ∧ False))) → (((False ∧ (p2 ∨ (p5 ∧ False))) ∧ p1) ∧ (p1 → p4))) ∨ True) ∨ p5) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_148048087186291385191379248518 : (((p3 ∧ (p2 ∨ (p5 ∧ (p2 ∧ ((True ∨ ((p5 ∧ (p2 ∨ (p4 ∧ p2))) ∨ p1)) → p4))))) ∨ (p1 → True)) ∨ (False → ((p5 → p3) ∧ p4))) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_751202249739447348052625765791 : (((True ∧ (((p5 ∨ p3) ∧ p5) → (((True → p2) ∧ (((p4 ∨ False) → p1) ∨ p4)) ∨ (((True ∨ p2) ∧ (False → False)) → (p3 ∧ p4))))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_186299654154556003102714528391 : ((((p4 ∨ (p2 → ((p4 ∧ p5) → (False → True)))) → p3) → p3) → (((False ∨ p2) ∧ (p3 → p1)) ∨ (False → ((p1 → (True ∨ p1)) ∧ p3)))) := by
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
  -- False on the left can always be used.
  apply False.elim h2
  -- False on the left can always be used.
  apply False.elim h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_320122635274325161559595830867 : (p4 ∨ ((False ∨ (p4 → False)) → ((True → (((True → p4) ∨ (p2 ∨ (p4 → False))) ∨ p3)) ∨ (True ∨ (p3 ∨ (((p5 ∧ True) ∨ p5) ∨ False)))))) := by
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
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- True on the right can always be proven directly.
    apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_135071047935112906929356340523 : ((((((p3 ∨ p3) → (p1 ∨ ((((p2 ∧ p2) → p3) ∧ (p1 ∨ p2)) ∨ True))) ∨ p3) ∨ (p2 ∨ True)) ∨ (p3 ∨ p3)) ∨ (p2 ∧ (p4 ∨ p2))) := by
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



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_788893749905284760235925784757 : (((p5 ∨ ((p2 ∧ (((p1 → (p5 ∧ p4)) ∨ ((p2 → p5) ∧ (p4 ∧ p4))) ∧ (p3 → ((p3 ∧ (p2 ∧ p5)) → p4)))) ∧ (p4 → p3))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_328636090471710523483639839807 : (True → ((((((p2 ∧ (p2 ∧ p3)) → p4) → (True ∨ p2)) → (True ∧ False)) ∨ False) → (p5 → ((p4 ∧ (p1 ∨ p5)) ∧ ((p5 ∧ p4) ∧ p2))))) := by
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
  -- Disjunctions on the left can always be decomposed.
  cases h2
  case inl h4 =>
    -- We want to use the implication h4 based on <expert-advice>. So we show its premise.
    have h5 : (((p2 ∧ (p2 ∧ p3)) → p4) → (True ∨ p2)) := by
      -- Implications on the right can always be decomposed.
      intro h6
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- True on the right can always be proven directly.
      apply True.intro
    -- We have shown the premise of h4, we can now drive its conclusion.
    let h7 := h4 h5
    -- We need to get the right conjuct of h7 based on <expert-advice>.
    let h8 := h7.right
    -- False on the left can always be used.
    apply False.elim h8
  case inr h9 =>
    -- False on the left can always be used.
    apply False.elim h9
  -- Disjunctions on the left can always be decomposed.
  cases h2
  case inl h10 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h3
  case inr h11 =>
    -- False on the left can always be used.
    apply False.elim h11
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Disjunctions on the left can always be decomposed.
  cases h2
  case inl h12 =>
    -- One of the premise coincides with the conclusion.
    exact h3
  case inr h13 =>
    -- False on the left can always be used.
    apply False.elim h13
  -- Disjunctions on the left can always be decomposed.
  cases h2
  case inl h14 =>
    -- We want to use the implication h14 based on <expert-advice>. So we show its premise.
    have h15 : (((p2 ∧ (p2 ∧ p3)) → p4) → (True ∨ p2)) := by
      -- Implications on the right can always be decomposed.
      intro h16
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- True on the right can always be proven directly.
      apply True.intro
    -- We have shown the premise of h14, we can now drive its conclusion.
    let h17 := h14 h15
    -- We need to get the right conjuct of h17 based on <expert-advice>.
    let h18 := h17.right
    -- False on the left can always be used.
    apply False.elim h18
  case inr h19 =>
    -- False on the left can always be used.
    apply False.elim h19
  -- Disjunctions on the left can always be decomposed.
  cases h2
  case inl h20 =>
    -- We want to use the implication h20 based on <expert-advice>. So we show its premise.
    have h21 : (((p2 ∧ (p2 ∧ p3)) → p4) → (True ∨ p2)) := by
      -- Implications on the right can always be decomposed.
      intro h22
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- True on the right can always be proven directly.
      apply True.intro
    -- We have shown the premise of h20, we can now drive its conclusion.
    let h23 := h20 h21
    -- We need to get the right conjuct of h23 based on <expert-advice>.
    let h24 := h23.right
    -- False on the left can always be used.
    apply False.elim h24
  case inr h25 =>
    -- False on the left can always be used.
    apply False.elim h25



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_61876877788041923278287757442 : ((p2 ∧ (((((((p1 ∨ (((p3 ∧ p1) → p5) → True)) ∨ p2) ∨ p4) ∨ ((p3 ∨ p5) ∧ p3)) → p2) ∨ (p4 → p1)) ∧ (p3 ∧ p2))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_204522678993024561659758945714 : (((((p4 → p4) ∧ p4) → p2) ∨ p1) ∨ ((((p5 ∧ ((p1 → ((p3 ∨ (p5 ∨ True)) ∨ p3)) ∨ (p1 ∧ p3))) ∧ (p3 ∧ p2)) ∨ True) ∨ p1)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_350114537248694781301909392416 : (p4 → ((((True ∧ (p2 ∧ ((((True ∧ True) ∨ p1) → (True ∧ p2)) → (p5 ∨ (p1 ∨ p3))))) → p2) → ((True → (p1 ∨ True)) ∧ p1)) ∨ p4)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_613127631037685208463835784226 : ((((((p3 ∨ ((p2 ∧ p2) ∧ ((p2 ∧ (p2 ∧ p3)) ∧ ((p2 ∨ ((p1 → p3) ∧ p3)) ∨ (True ∨ p2))))) → p3) → (p4 ∧ False)) ∨ p2) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_68263105069289289653181275830 : ((p3 → (((p5 → ((p1 ∨ ((False ∧ p5) ∧ ((p5 → True) ∧ p4))) ∨ (p2 ∧ (True ∧ (p2 → (p2 → False)))))) ∨ p4) ∨ (p2 → True))) ∨ p3) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h2
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_117098116973196145821949222553 : (((p1 → p5) → ((((((True ∨ p3) ∨ (False → p4)) ∧ (True → p2)) ∨ (p4 ∨ p2)) ∨ (p4 ∧ (p5 ∧ p3))) ∧ (p5 ∨ p1))) ∨ (p1 → True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_523765297300818726336555136513 : (((True ∧ ((p3 ∨ ((p5 ∧ False) ∨ (p4 ∧ ((p2 ∧ ((True ∨ (p3 ∨ True)) ∨ p1)) → (p4 ∨ (p2 ∧ (p4 ∨ p5))))))) ∨ (p3 → True))) ∧ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
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
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_689581511156128923442644815197 : ((((((False ∨ (p3 → True)) → (False → p3)) ∧ ((p3 ∧ (p5 ∧ (p1 ∧ p4))) ∨ p1)) ∨ (((p2 → p2) ∨ p1) ∨ ((True ∨ p3) → p5))) ∨ False) ∧ True) := by
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
  -- Implications on the right can always be decomposed.
  intro h1
  -- One of the premise coincides with the conclusion.
  exact h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_65212668618723488331993118491 : ((p3 ∨ (((p1 ∨ ((p5 ∨ (p3 → ((((p4 → p2) → p5) → p4) ∧ (p4 ∨ p5)))) ∧ p5)) → (p1 → ((False ∧ p5) ∨ p1))) ∨ p3)) ∨ False) := by
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
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h3 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h3
  case inr h4 =>
    -- Conjunctions on the left can always be decomposed.
    let h5 := h4.left
    let h6 := h4.right
    -- Disjunctions on the left can always be decomposed.
    cases h5
    case inl h7 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- One of the premise coincides with the conclusion.
      exact h2
    case inr h8 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- One of the premise coincides with the conclusion.
      exact h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_55410017276663772867272603755 : ((((((p5 ∨ p2) → p2) → p1) ∨ True) → (p1 → (p5 ∨ (((True → p2) ∨ (p2 → (p4 ∧ (p3 ∨ True)))) ∧ ((p1 ∨ p1) ∧ p3))))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_41247343701887339676446764727 : (((((p4 ∨ (((False ∧ p2) ∧ p2) ∨ (((True ∧ p5) → False) → (p4 ∧ (p5 ∨ p1))))) ∨ p4) ∨ (False → (False → (p2 → p1)))) ∨ p1) ∨ False) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
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
  -- False on the left can always be used.
  apply False.elim h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_928599348528801296097693216491 : ((((p1 → ((p5 → (True → p2)) ∨ ((p5 ∨ p3) ∧ False))) ∧ (p5 ∧ (((False → (p1 → p3)) ∧ ((p1 ∨ (p4 → p3)) ∨ True)) → False))) → p3) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- Conjunctions on the left can always be decomposed.
  let h4 := h3.left
  let h5 := h3.right
  -- We want to use the implication h5 based on <expert-advice>. So we show its premise.
  have h6 : ((False → (p1 → p3)) ∧ ((p1 ∨ (p4 → p3)) ∨ True)) := by
    -- Conjunctions on the right can always be decomposed.
    apply And.intro
    -- Implications on the right can always be decomposed.
    intro h7
    -- Implications on the right can always be decomposed.
    intro h8
    -- False on the left can always be used.
    apply False.elim h7
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h5, we can now drive its conclusion.
  let h9 := h5 h6
  -- False on the left can always be used.
  apply False.elim h9
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_175030219646651281007718129487 : ((p1 ∧ (p4 ∧ (p2 ∧ ((p1 → (p2 → ((p2 ∧ p3) → (p2 ∧ p2)))) ∨ p5)))) → ((((True → False) ∨ p1) ∧ (p1 ∧ (False ∨ True))) ∨ False)) := by
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
  cases h7
  case inl h8 =>
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Conjunctions on the right can always be decomposed.
    apply And.intro
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h2
    -- Conjunctions on the right can always be decomposed.
    apply And.intro
    -- One of the premise coincides with the conclusion.
    exact h2
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro
  case inr h9 =>
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Conjunctions on the right can always be decomposed.
    apply And.intro
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h2
    -- Conjunctions on the right can always be decomposed.
    apply And.intro
    -- One of the premise coincides with the conclusion.
    exact h2
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_45611651484860963087642762699 : (((p3 ∨ (True ∨ (((((p2 → (True → (((p3 ∨ False) ∧ p1) → p5))) → p2) ∨ p1) ∧ (p5 ∧ ((p5 ∧ p2) ∨ p5))) ∨ False))) → p2) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_195464092685755573135713982452 : ((((False → False) → True) ∨ (False ∨ (True ∨ p2))) ∧ (((((True → (p3 ∧ (p3 ∧ (True ∨ (p5 ∨ (p3 → p5)))))) ∧ p3) ∨ p3) → p2) ∨ True)) := by
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
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_67783994338817746937261284350 : ((p2 → ((p3 → (((p3 ∨ ((False ∧ (p3 → ((p1 ∨ False) ∨ True))) → p3)) → ((p3 ∧ ((p3 ∨ True) → False)) ∧ p5)) ∧ p5)) ∨ p2)) ∨ p1) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_139645679772787035989099060628 : ((((((p3 ∧ p2) → p4) → (True → p2)) ∨ (False → ((False ∧ (p3 ∧ p1)) ∧ ((p1 ∨ (p2 ∧ p3)) ∧ p1)))) → False) → (False ∨ (p3 ∧ False))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h2 : ((((p3 ∧ p2) → p4) → (True → p2)) ∨ (False → ((False ∧ (p3 ∧ p1)) ∧ ((p1 ∨ (p2 ∧ p3)) ∧ p1)))) := by
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h3
    -- Conjunctions on the right can always be decomposed.
    apply And.intro
    -- Conjunctions on the right can always be decomposed.
    apply And.intro
    -- False on the left can always be used.
    apply False.elim h3
    -- Conjunctions on the right can always be decomposed.
    apply And.intro
    -- False on the left can always be used.
    apply False.elim h3
    -- False on the left can always be used.
    apply False.elim h3
    -- Conjunctions on the right can always be decomposed.
    apply And.intro
    -- False on the left can always be used.
    apply False.elim h3
    -- False on the left can always be used.
    apply False.elim h3
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h4 := h1 h2
  -- False on the left can always be used.
  apply False.elim h4



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_682557083891187204551143084065 : ((((((((p3 → p5) → False) ∨ ((p2 → True) ∨ p4)) → False) → ((p5 → False) ∨ (p4 ∨ p3))) ∧ (((p2 ∨ (p2 ∨ p4)) → p3) ∨ p3)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_142289194388576719524943711657 : ((p2 ∧ (p2 ∧ ((False ∨ (p2 → ((p3 ∧ p1) ∨ ((p3 ∨ (((p5 → True) ∧ False) ∨ (False ∨ False))) ∨ True)))) → p1))) → ((p1 ∨ False) ∨ p1)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- Conjunctions on the left can always be decomposed.
  let h4 := h3.left
  let h5 := h3.right
  -- We want to use the implication h5 based on <expert-advice>. So we show its premise.
  have h6 : (False ∨ (p2 → ((p3 ∧ p1) ∨ ((p3 ∨ (((p5 → True) ∧ False) ∨ (False ∨ False))) ∨ True)))) := by
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h7
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h5, we can now drive its conclusion.
  let h8 := h5 h6
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h8



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_349124498627256607378417390331 : (p3 → (True → ((p4 ∨ p3) ∧ ((True ∧ ((p3 → p4) ∨ (p4 ∨ (((p4 → (p4 → (p1 ∧ (p1 ∨ (p5 ∧ p2))))) ∧ p2) ∨ True)))) ∧ p3)))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
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
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_265564694311325256086391650720 : (True ∧ (False ∨ (p4 → (((True → ((p5 → (p4 ∧ (p4 ∧ False))) → (True → False))) → p2) ∨ ((p1 ∧ ((True ∧ (True ∧ p3)) ∨ p3)) ∨ p4))))) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- True on the right can always be proven directly.
  apply True.intro
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



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_171519464586264362939176163800 : ((((False ∨ ((((False ∨ p3) → p1) → p3) → (p5 ∨ (p2 ∨ p4)))) ∧ p4) ∨ True) ∨ (p3 ∧ ((p2 ∧ (((p4 ∨ p5) ∧ False) ∧ p3)) → False))) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_181104588964827561010031399310 : (((p5 → p3) → (((((p5 ∧ (p4 ∧ p1)) ∧ p4) ∨ p5) ∨ p3) → p3)) → (True → (p5 ∨ ((p3 → (p1 ∨ False)) ∨ (p1 ∨ (p3 ∨ True)))))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
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
theorem thm_5_vars_52261339136068140965081623764 : (((p4 ∨ ((p5 → (False ∨ (((True ∨ p5) ∧ (p2 ∨ False)) → (p5 ∨ True)))) ∨ False)) → (p2 ∨ (((p3 ∨ p2) ∧ p3) → (p2 ∧ p1)))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_157879369366566631693881323002 : (((((p5 ∧ (p2 ∨ True)) ∨ p2) ∨ ((p3 ∧ p5) → False)) ∨ (p2 → (((p5 ∨ p5) → p4) → p4))) ∨ ((((p5 ∧ p4) ∧ p1) ∨ p1) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_355750991176390599177506234368 : (p5 → ((p5 ∨ (True → ((((False ∨ True) ∨ (p4 ∨ ((True ∧ (p5 ∧ True)) ∧ False))) ∨ ((p4 ∨ False) ∨ False)) → (p4 → p1)))) → (p1 ∨ True))) := by
  -- Implications on the right can always be decomposed.
  intro h1
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
theorem thm_5_vars_759745023452196251856753746015 : (((p2 ∧ (((False → ((False ∨ (p3 ∧ (p1 ∨ p5))) ∨ p1)) → p5) ∧ ((False → (p1 ∨ (p5 ∧ p2))) ∧ (((p1 ∧ True) ∨ p4) ∨ True)))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_141284570707990919368805800055 : ((((False ∨ p3) ∧ (p4 ∧ True)) ∧ (((((True ∨ True) → False) ∨ p1) ∨ (False ∧ p2)) ∨ ((p3 ∨ (p1 ∨ p2)) ∨ p5))) → ((p4 → p5) → p5)) := by
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
  cases h5
  case inl h7 =>
    -- False on the left can always be used.
    apply False.elim h7
  case inr h8 =>
    -- Conjunctions on the left can always be decomposed.
    let h9 := h6.left
    let h10 := h6.right
    -- Disjunctions on the left can always be decomposed.
    cases h4
    case inl h11 =>
      -- Disjunctions on the left can always be decomposed.
      cases h11
      case inl h12 =>
        -- Disjunctions on the left can always be decomposed.
        cases h12
        case inl h13 =>
          -- We want to use the implication h13 based on <expert-advice>. So we show its premise.
          have h14 : (True ∨ True) := by
            -- Show the left disjunct based on <expert-advice>.
            apply Or.inl
            -- True on the right can always be proven directly.
            apply True.intro
          -- We have shown the premise of h13, we can now drive its conclusion.
          let h15 := h13 h14
          -- False on the left can always be used.
          apply False.elim h15
        case inr h16 =>
          -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
          have h17 : p4 := by
            -- One of the premise coincides with the conclusion.
            exact h9
          -- We have shown the premise of h2, we can now drive its conclusion.
          let h18 := h2 h17
          -- One of the premise coincides with the conclusion.
          exact h18
      case inr h19 =>
        -- Conjunctions on the left can always be decomposed.
        let h20 := h19.left
        let h21 := h19.right
        -- False on the left can always be used.
        apply False.elim h20
    case inr h22 =>
      -- Disjunctions on the left can always be decomposed.
      cases h22
      case inl h23 =>
        -- Disjunctions on the left can always be decomposed.
        cases h23
        case inl h24 =>
          -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
          have h25 : p4 := by
            -- One of the premise coincides with the conclusion.
            exact h9
          -- We have shown the premise of h2, we can now drive its conclusion.
          let h26 := h2 h25
          -- One of the premise coincides with the conclusion.
          exact h26
        case inr h27 =>
          -- Disjunctions on the left can always be decomposed.
          cases h27
          case inl h28 =>
            -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
            have h29 : p4 := by
              -- One of the premise coincides with the conclusion.
              exact h9
            -- We have shown the premise of h2, we can now drive its conclusion.
            let h30 := h2 h29
            -- One of the premise coincides with the conclusion.
            exact h30
          case inr h31 =>
            -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
            have h32 : p4 := by
              -- One of the premise coincides with the conclusion.
              exact h9
            -- We have shown the premise of h2, we can now drive its conclusion.
            let h33 := h2 h32
            -- One of the premise coincides with the conclusion.
            exact h33
      case inr h34 =>
        -- One of the premise coincides with the conclusion.
        exact h34



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_123293771707047912032098744190 : (((((False ∨ (((True ∧ True) ∨ p2) ∨ (((p5 ∧ False) ∧ (False ∨ p4)) ∧ p3))) ∨ p1) ∨ p4) ∨ ((p4 ∧ (p2 ∧ p2)) ∧ True)) → (p5 ∨ True)) := by
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
        -- Disjunctions on the left can always be decomposed.
        cases h4
        case inl h5 =>
          -- False on the left can always be used.
          apply False.elim h5
        case inr h6 =>
          -- Disjunctions on the left can always be decomposed.
          cases h6
          case inl h7 =>
            -- Disjunctions on the left can always be decomposed.
            cases h7
            case inl h8 =>
              -- Conjunctions on the left can always be decomposed.
              let h9 := h8.left
              let h10 := h8.right
              -- Show the right disjunct based on <expert-advice>.
              apply Or.inr
              -- True on the right can always be proven directly.
              apply True.intro
            case inr h11 =>
              -- Show the right disjunct based on <expert-advice>.
              apply Or.inr
              -- True on the right can always be proven directly.
              apply True.intro
          case inr h12 =>
            -- Conjunctions on the left can always be decomposed.
            let h13 := h12.left
            let h14 := h12.right
            -- Conjunctions on the left can always be decomposed.
            let h15 := h13.left
            let h16 := h13.right
            -- Conjunctions on the left can always be decomposed.
            let h17 := h15.left
            let h18 := h15.right
            -- False on the left can always be used.
            apply False.elim h18
      case inr h19 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- True on the right can always be proven directly.
        apply True.intro
    case inr h20 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- True on the right can always be proven directly.
      apply True.intro
  case inr h21 =>
    -- Conjunctions on the left can always be decomposed.
    let h22 := h21.left
    let h23 := h21.right
    -- Conjunctions on the left can always be decomposed.
    let h24 := h22.left
    let h25 := h22.right
    -- Conjunctions on the left can always be decomposed.
    let h26 := h25.left
    let h27 := h25.right
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_602816954231418325706723048031 : ((((p1 ∨ (((((p3 → ((p2 ∧ p5) → p4)) → ((p3 ∧ p5) → ((p3 ∧ (False ∨ False)) ∧ True))) → p4) ∨ (p5 ∧ p4)) ∧ p5)) ∧ p2) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_43682895534711858857417051564 : (((((p1 → (p1 ∨ ((p2 ∧ p2) ∨ ((True ∧ True) ∧ (p4 ∨ p1))))) → (((p1 ∧ p1) ∧ p2) ∨ (False ∨ (False → p1)))) → False) → p2) ∨ False) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h2 : ((p1 → (p1 ∨ ((p2 ∧ p2) ∨ ((True ∧ True) ∧ (p4 ∨ p1))))) → (((p1 ∧ p1) ∧ p2) ∨ (False ∨ (False → p1)))) := by
    -- Implications on the right can always be decomposed.
    intro h3
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h4
    -- False on the left can always be used.
    apply False.elim h4
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h5 := h1 h2
  -- False on the left can always be used.
  apply False.elim h5



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_41262446699614048389291326851 : (((((p1 ∨ p1) ∨ (p2 ∨ (((p4 ∨ True) → (p1 → (p5 ∧ True))) ∧ (p2 ∧ (p5 → p2))))) ∨ ((False → p4) → (True ∨ p1))) ∨ p5) ∨ p5) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_256683511038733958567608924024 : ((p1 ∨ False) → (p2 ∨ ((p1 → p3) ∨ (((p4 → p4) → ((p1 ∨ p2) ∧ (p4 ∨ ((p4 ∨ p3) ∧ p3)))) ∨ ((p2 ∧ p1) → (False → p5)))))) := by
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
    -- Implications on the right can always be decomposed.
    intro h4
    -- False on the left can always be used.
    apply False.elim h4
  case inr h5 =>
    -- False on the left can always be used.
    apply False.elim h5



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_311042187605829833938210892655 : (p2 ∨ ((p4 ∧ True) ∨ (((False ∧ ((p3 ∧ (p3 ∧ False)) → p1)) ∧ True) ∨ ((False → (p5 → p2)) ∧ ((True → ((p1 ∨ p1) → p5)) ∨ True))))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- False on the left can always be used.
  apply False.elim h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_146912324188580380694912171857 : (((((p3 ∧ (False ∨ (False → (((p1 → p5) ∧ (False ∧ p4)) → (True ∧ p3))))) → (p2 ∨ p2)) ∧ True) ∧ True) ∨ (p1 → ((True ∨ False) ∨ p3))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_677290813572422612590265733446 : ((((((p4 ∨ p5) ∨ (((p4 → p2) ∨ ((p2 ∨ (p5 ∧ True)) ∧ p3)) → ((p3 ∧ p3) ∨ p3))) ∧ False) ∨ ((p4 → (p3 ∨ p5)) ∨ True)) ∨ p1) ∧ True) := by
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
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_149452319398174081172842461202 : ((False ∧ (((p1 ∨ p1) ∧ (((False ∨ ((p4 ∨ p2) ∧ p4)) ∧ ((True → p3) ∨ False)) ∧ p5)) ∧ (False → p2))) ∨ (((p4 → True) ∧ p4) → True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_207722372622646831109727640125 : (((p2 ∧ (p2 ∨ (p2 ∧ p3))) → p4) → ((((False → (p1 ∧ p2)) → p5) ∧ (p3 → p3)) ∨ (False → (False ∧ ((p4 ∨ p1) ∨ (p5 → p2)))))) := by
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
  -- False on the left can always be used.
  apply False.elim h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_195434343910336094208610808983 : ((((True ∨ True) ∧ True) ∨ (False ∨ (p4 ∧ False))) ∧ (((p4 ∧ ((p4 → (False ∧ ((p2 → ((p2 → False) ∨ p5)) ∧ True))) → p2)) ∨ True) ∨ True)) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_215827648704079704987553276532 : ((p2 ∨ ((False ∨ p5) ∨ p2)) ∨ ((p5 → (((p3 ∧ True) ∧ ((p4 ∧ (p2 ∨ p1)) ∧ p3)) ∨ ((p3 → p3) → ((p4 ∧ p5) → p5)))) ∨ p1)) := by
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
  -- Implications on the right can always be decomposed.
  intro h3
  -- Conjunctions on the left can always be decomposed.
  let h4 := h3.left
  let h5 := h3.right
  -- One of the premise coincides with the conclusion.
  exact h5



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_147067228159720944237169798610 : (((((p1 → (p5 ∧ (True ∨ p5))) ∧ (p3 → p4)) → (False ∧ ((p1 ∨ True) → (p1 → (p1 ∧ False))))) ∧ True) ∨ ((False ∧ p1) → (True ∧ False))) := by
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
  -- False on the left can always be used.
  apply False.elim h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_43122957572021896508718737805 : (((((((p4 ∧ p2) ∧ ((p1 ∨ (p1 ∨ ((p4 → p5) ∧ True))) → p5)) ∧ True) → (((True ∨ (p3 ∨ True)) ∧ False) → p1)) ∧ p5) → p2) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_255209936137609409806864385152 : ((p4 ∧ p4) → ((True → ((p5 ∨ False) ∧ p4)) → (((((((p5 ∨ False) ∧ p2) ∧ p4) → p4) → ((p1 ∨ p3) ∨ False)) ∨ (True ∧ False)) ∨ p4))) := by
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
theorem thm_5_vars_630734290469344806282688383814 : (((((p3 → ((p2 ∧ ((p4 ∨ ((((False → (p3 ∧ True)) ∨ p1) ∧ True) ∧ ((p3 ∨ p2) → p4))) ∧ p4)) ∨ (p5 ∧ p4))) ∨ p2) → False) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_304074220112757522705094397842 : (p1 ∨ ((p3 ∨ ((((p3 ∨ p1) ∨ (p4 ∨ (True ∨ (p4 → ((((p2 → (p3 ∨ p2)) → p1) ∨ (p4 ∨ p4)) ∨ False))))) → p5) → p5)) ∨ p2)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h2 : ((p3 ∨ p1) ∨ (p4 ∨ (True ∨ (p4 → ((((p2 → (p3 ∨ p2)) → p1) ∨ (p4 ∨ p4)) ∨ False))))) := by
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h3 := h1 h2
  -- One of the premise coincides with the conclusion.
  exact h3



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_311261429009384113158173022747 : (p2 ∨ (True ∧ ((((True → False) ∨ ((((p5 ∨ (p4 ∧ (p2 ∧ p3))) ∨ p1) → p2) ∧ ((False ∨ True) → (p4 ∧ (p5 ∧ p5))))) ∧ p4) → p5))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- Disjunctions on the left can always be decomposed.
  cases h2
  case inl h4 =>
    -- We want to use the implication h4 based on <expert-advice>. So we show its premise.
    have h5 : True := by
      -- True on the right can always be proven directly.
      apply True.intro
    -- We have shown the premise of h4, we can now drive its conclusion.
    let h6 := h4 h5
    -- False on the left can always be used.
    apply False.elim h6
  case inr h7 =>
    -- Conjunctions on the left can always be decomposed.
    let h8 := h7.left
    let h9 := h7.right
    -- We want to use the implication h9 based on <expert-advice>. So we show its premise.
    have h10 : (False ∨ True) := by
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- True on the right can always be proven directly.
      apply True.intro
    -- We have shown the premise of h9, we can now drive its conclusion.
    let h11 := h9 h10
    -- We need to get the right conjuct of h11 based on <expert-advice>.
    let h12 := h11.right
    -- We need to get the left conjuct of h12 based on <expert-advice>.
    let h13 := h12.left
    -- One of the premise coincides with the conclusion.
    exact h13



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_138423465727887618391838199034 : ((p5 → ((p2 ∧ (((p3 ∨ False) ∨ (p1 ∧ ((p2 ∧ p5) ∨ p3))) ∨ ((p4 ∧ (p5 ∨ p1)) → False))) ∧ (p2 → p3))) ∨ ((p3 → p5) → True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_587786500537811029835673726328 : (((((((p1 ∨ p5) ∧ (((((True → (p2 → p4)) ∨ (p3 ∨ (p4 ∧ p2))) → (p3 → p3)) ∧ p5) → p4)) ∧ (True ∨ p5)) ∨ True) ∧ True) ∨ p4) ∧ True) := by
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
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_225951927604279044741860673264 : (((p2 ∧ p5) ∨ p2) ∨ ((((p5 ∧ True) ∧ (p3 ∨ p5)) ∨ p2) ∨ ((((p3 → (False ∧ False)) ∧ (True → p5)) ∨ p2) → (False → (p5 ∨ p3))))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- False on the left can always be used.
  apply False.elim h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_181083605238774252126579027358 : (((p5 ∨ p3) → (((p5 ∨ (False ∨ p3)) → (p5 ∨ (p5 ∨ p2))) → True)) → (((p1 → p3) ∧ ((p4 ∨ False) ∧ p5)) ∨ (p1 → (False → True)))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h2
  -- Implications on the right can always be decomposed.
  intro h3
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_172793768938870996567185618576 : (((p2 → p2) → ((((p2 ∧ (p5 → (p1 → (p1 ∨ p2)))) → p5) ∨ p3) ∧ p4)) ∨ ((((True ∧ p2) ∧ True) ∧ (p4 → (p2 ∨ p3))) → p2)) := by
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
  -- One of the premise coincides with the conclusion.
  exact h7



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_727840045549411209740193288063 : ((((p1 ∨ (p3 ∨ False)) ∨ (((True ∨ p3) → p1) → (((True → p1) ∧ (p2 ∧ (((True ∧ ((p1 → p4) ∧ p3)) ∨ p4) ∧ p2))) → p1))) ∨ p5) ∧ True) := by
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
  -- Conjunctions on the left can always be decomposed.
  let h3 := h2.left
  let h4 := h2.right
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
    let h10 := h9.left
    let h11 := h9.right
    -- Conjunctions on the left can always be decomposed.
    let h12 := h11.left
    let h13 := h11.right
    -- We want to use the implication h3 based on <expert-advice>. So we show its premise.
    have h14 : True := by
      -- True on the right can always be proven directly.
      apply True.intro
    -- We have shown the premise of h3, we can now drive its conclusion.
    let h15 := h3 h14
    -- One of the premise coincides with the conclusion.
    exact h15
  case inr h16 =>
    -- We want to use the implication h3 based on <expert-advice>. So we show its premise.
    have h17 : True := by
      -- True on the right can always be proven directly.
      apply True.intro
    -- We have shown the premise of h3, we can now drive its conclusion.
    let h18 := h3 h17
    -- One of the premise coincides with the conclusion.
    exact h18
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_224271865841924354351338978894 : ((False → (False ∧ p4)) ∧ (((((p3 → True) → ((((True ∧ (((False ∨ p5) ∨ (p1 ∧ True)) ∧ False)) ∧ True) ∧ p1) ∧ p1)) ∨ p1) ∨ p5) ∨ True)) := by
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
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_790638770138232231094548936182 : (((p5 ∨ (p4 ∨ ((((p5 → (p5 → (p2 → (False → (p1 ∧ (p2 ∧ False)))))) ∨ False) → ((p1 ∧ False) → (True ∧ (p5 ∧ False)))) → p5))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_190233662906974767655811509511 : ((((((p5 → (False → True)) ∨ p1) ∧ p3) ∧ p4) ∨ p2) ∨ ((p5 → ((p3 → ((p2 ∧ p2) → True)) ∧ ((p4 ∧ False) ∧ (p2 ∨ p2)))) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_66114873702936421344584969393 : ((p5 ∨ ((p1 ∧ ((p3 ∨ True) → ((((p1 → p3) ∨ p2) ∧ (p1 → ((((p2 ∧ p4) → (p5 → p5)) ∧ True) ∧ False))) ∨ False))) → p2)) ∨ p5) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- We want to use the implication h3 based on <expert-advice>. So we show its premise.
  have h4 : (p3 ∨ True) := by
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h3, we can now drive its conclusion.
  let h5 := h3 h4
  -- Disjunctions on the left can always be decomposed.
  cases h5
  case inl h6 =>
    -- Conjunctions on the left can always be decomposed.
    let h7 := h6.left
    let h8 := h6.right
    -- Disjunctions on the left can always be decomposed.
    cases h7
    case inl h9 =>
      -- We want to use the implication h8 based on <expert-advice>. So we show its premise.
      have h10 : p1 := by
        -- One of the premise coincides with the conclusion.
        exact h2
      -- We have shown the premise of h8, we can now drive its conclusion.
      let h11 := h8 h10
      -- We need to get the right conjuct of h11 based on <expert-advice>.
      let h12 := h11.right
      -- False on the left can always be used.
      apply False.elim h12
    case inr h13 =>
      -- One of the premise coincides with the conclusion.
      exact h13
  case inr h14 =>
    -- False on the left can always be used.
    apply False.elim h14



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_260743111282317762051092973901 : ((p3 → p4) → ((p3 ∨ p3) → ((((((True ∨ p4) ∧ (((True → p2) ∧ (p3 ∧ False)) ∧ p5)) ∨ True) → False) → p4) ∨ (p2 ∧ (p3 ∨ p3))))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Disjunctions on the left can always be decomposed.
  cases h2
  case inl h3 =>
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Implications on the right can always be decomposed.
    intro h4
    -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
    have h5 : p3 := by
      -- One of the premise coincides with the conclusion.
      exact h3
    -- We have shown the premise of h1, we can now drive its conclusion.
    let h6 := h1 h5
    -- One of the premise coincides with the conclusion.
    exact h6
  case inr h7 =>
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Implications on the right can always be decomposed.
    intro h8
    -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
    have h9 : p3 := by
      -- One of the premise coincides with the conclusion.
      exact h7
    -- We have shown the premise of h1, we can now drive its conclusion.
    let h10 := h1 h9
    -- One of the premise coincides with the conclusion.
    exact h10



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_47004723200381308980530055909 : (((((False → p1) ∧ (True → ((p1 → ((((False ∨ (True ∧ p4)) ∨ p4) ∧ (True ∧ (True ∧ p1))) ∨ p1)) ∧ p5))) → False) ∨ (p2 → True)) ∨ p2) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_233439633926416623823009762072 : ((False ∨ (False → True)) → ((p2 ∧ p2) → (p4 → ((False ∧ (((p3 ∧ p3) ∧ p1) → ((p4 ∨ p4) → (p2 ∧ p5)))) ∨ ((p2 ∧ p2) → True))))) := by
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
  cases h1
  case inl h6 =>
    -- False on the left can always be used.
    apply False.elim h6
  case inr h7 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h8
    -- True on the right can always be proven directly.
    apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_784847853357832014544202680474 : (((p3 ∨ (p1 → (((((p3 → (((p4 → p2) ∧ p5) → (False ∧ p3))) ∨ p2) → (((True → p3) → False) ∨ p2)) ∨ p2) ∨ (True → p1)))) ∨ p4) ∧ True) := by
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
  -- Implications on the right can always be decomposed.
  intro h2
  -- One of the premise coincides with the conclusion.
  exact h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_960446713125976069034143973675 : ((((True ∨ True) ∧ ((p5 ∧ (True ∨ False)) ∧ (p4 ∧ ((p4 ∧ p4) → ((((True ∨ (p3 ∧ p5)) ∧ (p1 ∨ True)) ∧ p3) ∧ (p2 ∧ p2)))))) → p3) ∧ True) := by
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
    let h7 := h5.left
    let h8 := h5.right
    -- Disjunctions on the left can always be decomposed.
    cases h8
    case inl h9 =>
      -- Conjunctions on the left can always be decomposed.
      let h10 := h6.left
      let h11 := h6.right
      -- We want to use the implication h11 based on <expert-advice>. So we show its premise.
      have h12 : (p4 ∧ p4) := by
        -- Conjunctions on the right can always be decomposed.
        apply And.intro
        -- One of the premise coincides with the conclusion.
        exact h10
        -- One of the premise coincides with the conclusion.
        exact h10
      -- We have shown the premise of h11, we can now drive its conclusion.
      let h13 := h11 h12
      -- We need to get the left conjuct of h13 based on <expert-advice>.
      let h14 := h13.left
      -- We need to get the right conjuct of h14 based on <expert-advice>.
      let h15 := h14.right
      -- One of the premise coincides with the conclusion.
      exact h15
    case inr h16 =>
      -- False on the left can always be used.
      apply False.elim h16
  case inr h17 =>
    -- Conjunctions on the left can always be decomposed.
    let h18 := h3.left
    let h19 := h3.right
    -- Conjunctions on the left can always be decomposed.
    let h20 := h18.left
    let h21 := h18.right
    -- Disjunctions on the left can always be decomposed.
    cases h21
    case inl h22 =>
      -- Conjunctions on the left can always be decomposed.
      let h23 := h19.left
      let h24 := h19.right
      -- We want to use the implication h24 based on <expert-advice>. So we show its premise.
      have h25 : (p4 ∧ p4) := by
        -- Conjunctions on the right can always be decomposed.
        apply And.intro
        -- One of the premise coincides with the conclusion.
        exact h23
        -- One of the premise coincides with the conclusion.
        exact h23
      -- We have shown the premise of h24, we can now drive its conclusion.
      let h26 := h24 h25
      -- We need to get the left conjuct of h26 based on <expert-advice>.
      let h27 := h26.left
      -- We need to get the right conjuct of h27 based on <expert-advice>.
      let h28 := h27.right
      -- One of the premise coincides with the conclusion.
      exact h28
    case inr h29 =>
      -- False on the left can always be used.
      apply False.elim h29
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_684178182108934839141209524557 : (((((p5 ∧ (p4 ∨ (False ∧ ((False ∨ True) ∨ (((p1 → p4) → False) → True))))) ∨ (False ∧ p1)) ∨ (((False ∨ (True ∧ True)) ∧ p5) → True)) ∨ p1) ∧ True) := by
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
theorem thm_5_vars_54008990308897356244848390376 : (((((p4 ∨ (p2 ∧ False)) ∧ ((p5 ∧ p4) ∧ p5)) → False) → (p1 → (((p5 → p5) ∧ ((p3 → p2) ∨ ((p3 ∨ p2) ∧ p1))) ∧ p4))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_168766192736065330702324021794 : ((p1 ∨ ((p4 ∧ (p2 → ((p4 → (((p4 ∧ p4) ∨ p3) ∨ False)) ∨ (p3 → p5)))) ∨ p4)) → ((((False ∧ (p5 → p1)) → True) → False) → p2)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h3 =>
    -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
    have h4 : ((False ∧ (p5 → p1)) → True) := by
      -- Implications on the right can always be decomposed.
      intro h5
      -- True on the right can always be proven directly.
      apply True.intro
    -- We have shown the premise of h2, we can now drive its conclusion.
    let h6 := h2 h4
    -- False on the left can always be used.
    apply False.elim h6
  case inr h7 =>
    -- Disjunctions on the left can always be decomposed.
    cases h7
    case inl h8 =>
      -- Conjunctions on the left can always be decomposed.
      let h9 := h8.left
      let h10 := h8.right
      -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
      have h11 : ((False ∧ (p5 → p1)) → True) := by
        -- Implications on the right can always be decomposed.
        intro h12
        -- True on the right can always be proven directly.
        apply True.intro
      -- We have shown the premise of h2, we can now drive its conclusion.
      let h13 := h2 h11
      -- False on the left can always be used.
      apply False.elim h13
    case inr h14 =>
      -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
      have h15 : ((False ∧ (p5 → p1)) → True) := by
        -- Implications on the right can always be decomposed.
        intro h16
        -- True on the right can always be proven directly.
        apply True.intro
      -- We have shown the premise of h2, we can now drive its conclusion.
      let h17 := h2 h15
      -- False on the left can always be used.
      apply False.elim h17



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_302714783280924017561669324615 : (False ∨ (p3 ∨ ((p1 ∨ p5) → (((p1 ∧ ((((((p5 ∨ p1) → (p1 ∨ (True ∧ p1))) ∨ True) ∧ p4) ∨ p3) ∧ p1)) → (p5 ∨ True)) ∨ p2)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
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
    -- Conjunctions on the left can always be decomposed.
    let h4 := h3.left
    let h5 := h3.right
    -- Conjunctions on the left can always be decomposed.
    let h6 := h5.left
    let h7 := h5.right
    -- Disjunctions on the left can always be decomposed.
    cases h6
    case inl h8 =>
      -- Conjunctions on the left can always be decomposed.
      let h9 := h8.left
      let h10 := h8.right
      -- Disjunctions on the left can always be decomposed.
      cases h9
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
    case inr h13 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- True on the right can always be proven directly.
      apply True.intro
  case inr h14 =>
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Implications on the right can always be decomposed.
    intro h15
    -- Conjunctions on the left can always be decomposed.
    let h16 := h15.left
    let h17 := h15.right
    -- Conjunctions on the left can always be decomposed.
    let h18 := h17.left
    let h19 := h17.right
    -- Disjunctions on the left can always be decomposed.
    cases h18
    case inl h20 =>
      -- Conjunctions on the left can always be decomposed.
      let h21 := h20.left
      let h22 := h20.right
      -- Disjunctions on the left can always be decomposed.
      cases h21
      case inl h23 =>
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- One of the premise coincides with the conclusion.
        exact h14
      case inr h24 =>
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- One of the premise coincides with the conclusion.
        exact h14
    case inr h25 =>
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- One of the premise coincides with the conclusion.
      exact h14



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_158799447537382561102334106949 : ((p5 ∧ ((p3 → (p5 ∨ (p4 ∧ p5))) → (((((p3 ∧ False) ∧ False) → p1) ∨ (p3 ∨ p3)) → False))) ∨ ((p3 ∧ (False ∧ p4)) → (p3 ∨ p3))) := by
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
  apply False.elim h4



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_47534696336256585016186108299 : (((p4 ∨ ((p5 ∨ p3) ∨ ((p4 ∨ ((((p5 → (True ∧ p5)) → (p2 ∧ p4)) ∨ p2) ∧ p4)) ∧ (True ∧ (p1 ∨ p1))))) ∨ (p3 → True)) ∨ p4) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_52415602405102664812275095821 : ((((p5 ∧ (p5 → p3)) → (((False → p4) ∨ (p4 → (False → True))) ∨ False)) ∧ ((True → True) → (p4 ∨ ((p5 ∧ p2) ∧ (False ∨ False))))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_148037866095970006519957932387 : ((((p2 ∨ p3) ∨ (((((False → ((p1 → True) → p2)) ∨ (p5 ∨ True)) ∧ True) ∨ p3) → p2)) ∨ (True → p2)) ∨ ((p1 ∨ True) ∨ (p2 → True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



