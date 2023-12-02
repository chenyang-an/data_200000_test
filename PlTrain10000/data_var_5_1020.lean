variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_262324532079366864407519139886 : (True ∧ (((p3 → ((p5 → p3) ∧ (p3 → (p2 ∧ p5)))) ∨ (((((p2 ∨ (p4 → False)) ∨ ((p4 → True) → True)) → p4) ∨ False) ∧ p1)) ∨ True)) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_303816311760861684534296184659 : (p1 ∨ (((p1 ∨ ((True ∧ False) → (((((False ∨ (p4 ∨ False)) ∨ p4) ∨ p1) ∧ ((True ∧ (p2 ∧ p5)) ∧ p1)) ∧ (p1 → p4)))) → p3) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_206342994626047782300840383875 : ((p2 ∨ (((p3 → p2) ∨ p1) ∨ p1)) ∨ ((((p4 → p1) ∧ (((p3 → False) ∨ p3) → ((p1 → False) ∨ False))) ∧ (p4 ∧ p4)) → (p2 ∨ p1))) := by
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
  let h6 := h3.left
  let h7 := h3.right
  -- We want to use the implication h4 based on <expert-advice>. So we show its premise.
  have h8 : p4 := by
    -- One of the premise coincides with the conclusion.
    exact h7
  -- We have shown the premise of h4, we can now drive its conclusion.
  let h9 := h4 h8
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h9



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_134839557724896361635020432211 : (((p3 ∨ ((True → ((p5 ∧ p4) ∧ ((p3 → p3) → p4))) → ((p2 ∨ ((p3 ∨ (p1 ∧ p1)) ∨ p2)) ∧ p1))) → False) ∨ (p4 → (p4 ∨ p4))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_59544044831675738642227547066 : (((p3 → False) ∨ ((((True ∧ (p3 ∧ False)) → p4) ∧ p3) → (((False → ((True ∨ p2) ∧ (p1 ∨ (True → p5)))) ∨ p5) → (p5 → p5)))) ∨ p4) := by
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
  cases h2
  case inl h4 =>
    -- Conjunctions on the left can always be decomposed.
    let h5 := h1.left
    let h6 := h1.right
    -- One of the premise coincides with the conclusion.
    exact h3
  case inr h7 =>
    -- Conjunctions on the left can always be decomposed.
    let h8 := h1.left
    let h9 := h1.right
    -- One of the premise coincides with the conclusion.
    exact h7



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_164750064170595553602713109111 : ((((((p2 ∨ ((p3 ∧ (p3 ∧ p2)) → p5)) ∨ False) ∧ (True → p4)) → (p3 ∨ p5)) ∨ p4) ∨ (True ∨ (False ∨ ((p2 ∨ p3) ∧ (True → True))))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_166262143229841643665897629930 : ((p3 ∧ ((p4 ∧ (p2 ∧ False)) ∧ (False ∨ (p1 → (((p2 ∨ p3) ∧ p3) ∨ (p1 → p2)))))) ∨ (((True ∧ (p5 ∧ (p2 → p1))) ∨ True) ∨ p5)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_165820981439652086128668083723 : (((False ∨ (False ∨ p5)) ∧ ((p4 → p3) ∧ ((p5 ∨ (p3 ∧ True)) ∧ ((p3 ∨ p1) ∧ p1)))) ∨ ((p4 → True) → ((p5 ∨ p4) → (True ∨ p5)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Disjunctions on the left can always be decomposed.
  cases h2
  case inl h3 =>
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- True on the right can always be proven directly.
    apply True.intro
  case inr h4 =>
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- True on the right can always be proven directly.
    apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_255807922700485434747079157228 : ((True ∨ False) → ((p2 ∧ ((True ∧ ((p4 ∨ p3) ∧ (p3 ∨ True))) ∧ ((p2 → False) ∧ (p4 ∨ p5)))) ∨ (True ∨ ((p4 ∨ (p5 ∨ p1)) ∧ p3)))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h2 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- True on the right can always be proven directly.
    apply True.intro
  case inr h3 =>
    -- False on the left can always be used.
    apply False.elim h3



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_230532258891917972376804210164 : (((False → p1) ∧ True) → (((p1 → ((p4 → p3) ∧ True)) ∧ (p2 ∨ (((p3 → p4) ∨ (p1 ∨ p3)) ∨ False))) ∨ ((p5 ∨ (p3 ∧ p5)) → True))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h4
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_711966350787359550064434193004 : (((((((p4 ∧ p1) ∨ p1) ∨ p2) ∨ False) ∨ ((p5 ∧ ((p2 → ((p4 → False) ∧ (True ∧ ((False → p3) → (p4 ∨ True))))) ∨ p1)) ∨ True)) ∨ p4) ∧ True) := by
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
theorem thm_5_vars_769513081475434390564625272992 : (((p5 ∧ (p3 ∧ (True ∧ ((p1 ∨ ((((p2 → (((p1 → True) ∧ p5) → p2)) ∧ p4) ∨ (p3 ∨ p3)) ∨ p4)) ∨ ((True ∨ True) ∨ False))))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_57454848624253020022496522193 : (((p5 ∨ (p2 ∨ p5)) ∨ ((False ∨ ((p4 ∨ (p4 → (False → (p4 ∨ p2)))) ∨ ((p2 ∨ p4) ∨ ((p1 ∨ p4) ∧ p1)))) ∧ (True ∨ True))) ∨ False) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
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
  -- False on the left can always be used.
  apply False.elim h2
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_49822633568727034434410328848 : (((p2 → (p1 → (p1 → ((((((False ∨ p2) ∧ True) ∨ p5) → p2) ∨ (p4 → False)) ∧ ((p5 ∨ p3) → p4))))) → ((p5 → False) → False)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_50846024004276964937153968190 : ((((False → ((p2 ∧ (p1 ∧ ((((p4 → (p3 ∨ p4)) ∨ True) → p1) → p1))) → p4)) ∧ p3) ∧ (p3 ∧ (p4 → (p5 ∨ (p1 ∨ False))))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_65089158468408871173663739894 : ((p2 ∨ (p1 ∨ ((p4 ∨ (((((((p2 ∧ p5) ∧ ((True ∨ p4) ∨ (p2 ∧ False))) ∨ (p2 → p1)) → p2) → p3) → True) ∧ False)) ∧ p2))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_257246571572080787641930921999 : ((p2 ∨ p3) → (((((p3 ∨ p2) ∨ True) ∧ ((p5 ∨ (((p5 → p4) ∧ p3) ∧ p2)) ∨ p4)) → ((True ∧ (p3 → (p3 ∧ False))) → p3)) ∨ True)) := by
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
theorem thm_5_vars_731601446405789788987524610237 : ((((p1 → (p5 ∧ True)) → (((False → False) → False) ∧ ((p1 ∧ (((p4 → ((p4 → (p1 ∧ p5)) → p4)) ∨ (p1 ∧ True)) ∨ p3)) ∨ True))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_165803695454536451418084534738 : ((((p4 ∨ p5) ∨ p3) ∧ (False → (((p2 → False) ∧ p5) ∨ (p1 ∧ (False ∨ (True ∧ p5)))))) ∨ ((p1 ∧ (((p4 ∨ p1) ∨ p4) ∧ False)) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_67895762319092794257177789480 : ((p2 → (((p3 ∨ (p2 → False)) ∨ ((False ∨ False) ∨ (((False ∧ p1) → p4) ∧ (p1 ∧ p3)))) ∨ ((p3 → True) ∧ ((True ∧ p2) ∨ p2)))) ∨ p4) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
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
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_165072150090706996968391958497 : (((p4 ∧ ((p2 ∧ (((p4 ∧ (p1 ∨ (False ∧ True))) ∨ p1) → (False ∨ p2))) → p3)) → False) ∨ (p4 ∨ (((p5 ∧ (False → p3)) ∨ True) ∨ p1))) := by
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
theorem thm_5_vars_147880935242981476292529080999 : (((p5 → (p2 ∧ ((p3 ∨ p3) → (((((p4 ∧ p3) → p2) ∧ p1) ∧ ((True ∨ True) ∧ False)) → p4)))) → p1) ∨ ((p5 → p5) ∨ (p5 → p4))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_112954848885662536520879521379 : (((True ∧ (p3 → (((((p4 ∧ False) ∨ p1) ∧ p1) ∧ p2) ∨ (p5 ∧ ((p5 ∨ p2) → (True → (p1 ∧ (p4 ∧ p2)))))))) → p1) ∨ (False → p3)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_319627466472554268000314103195 : (p4 ∨ ((((p4 ∧ (p4 ∨ True)) ∧ (p3 ∧ p3)) ∧ False) ∨ ((p3 ∧ (p5 → (((p1 ∨ (True → (p4 ∨ (False ∧ p3)))) ∧ True) ∧ p2))) ∨ True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_119110469614740481225065284420 : ((p1 → ((True → False) ∧ (((p5 ∨ False) ∧ (p2 → p5)) ∧ (((False ∧ ((p4 → (p5 → False)) → p1)) ∧ True) ∧ (False → p3))))) ∨ (p1 → True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_612826333386297637601809743075 : ((((((p2 → p1) → ((((False → p4) ∨ p1) ∨ (p2 → (True ∨ (p3 ∨ (True ∨ (p5 ∨ p3)))))) ∧ (False ∧ p5))) ∨ (p5 ∨ False)) ∨ p2) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_181703044429588565855249750282 : ((p5 → (((p5 ∧ False) ∧ ((p2 ∧ p3) ∧ p3)) ∧ ((False ∨ p3) ∨ False))) → ((p1 ∧ (p1 → (p5 ∧ p5))) → ((p2 ∧ True) ∧ (p1 → p5)))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Conjunctions on the left can always be decomposed.
  let h3 := h2.left
  let h4 := h2.right
  -- We want to use the implication h4 based on <expert-advice>. So we show its premise.
  have h5 : p1 := by
    -- One of the premise coincides with the conclusion.
    exact h3
  -- We have shown the premise of h4, we can now drive its conclusion.
  let h6 := h4 h5
  -- We need to get the left conjuct of h6 based on <expert-advice>.
  let h7 := h6.left
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h8 : p5 := by
    -- One of the premise coincides with the conclusion.
    exact h7
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h9 := h1 h8
  -- We need to get the left conjuct of h9 based on <expert-advice>.
  let h10 := h9.left
  -- We need to get the left conjuct of h10 based on <expert-advice>.
  let h11 := h10.left
  -- We need to get the right conjuct of h11 based on <expert-advice>.
  let h12 := h11.right
  -- False on the left can always be used.
  apply False.elim h12
  -- True on the right can always be proven directly.
  apply True.intro
  -- Implications on the right can always be decomposed.
  intro h13
  -- Conjunctions on the left can always be decomposed.
  let h14 := h2.left
  let h15 := h2.right
  -- We want to use the implication h15 based on <expert-advice>. So we show its premise.
  have h16 : p1 := by
    -- One of the premise coincides with the conclusion.
    exact h14
  -- We have shown the premise of h15, we can now drive its conclusion.
  let h17 := h15 h16
  -- We need to get the left conjuct of h17 based on <expert-advice>.
  let h18 := h17.left
  -- One of the premise coincides with the conclusion.
  exact h18



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_329657012591744005014376717731 : (True → ((p4 ∧ p5) → ((p4 → (False ∨ ((p2 ∧ (p4 ∨ ((p1 ∧ ((p2 ∨ False) ∧ (True → (False ∧ False)))) ∨ p3))) ∧ (p3 ∧ p1)))) ∨ p4))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Conjunctions on the left can always be decomposed.
  let h3 := h2.left
  let h4 := h2.right
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h3



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_117134176098234457003309844160 : (((p5 → False) → (((True ∨ (((p4 ∨ (p4 ∨ (p4 ∨ p4))) ∧ (False ∨ (((p2 → p4) ∧ p2) → p3))) ∧ p1)) ∧ True) → False)) ∨ (True ∨ False)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_674895268101075904228188322690 : ((((((True → (((p5 → ((((p2 → p1) ∧ p1) → True) → p3)) ∧ p4) → (p5 ∧ True))) ∨ p3) ∧ p5) ∧ (True → ((p2 → False) → p5))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_748033530969068145790644195022 : ((((p1 → p1) → ((((p4 ∧ (p4 ∨ (p1 ∧ (False ∧ True)))) ∨ ((True ∧ p3) → p4)) → (p1 ∧ ((p4 ∨ (False → True)) ∨ p2))) → p2)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_807871960486917050829706071085 : (((p4 → ((p2 ∧ p5) ∨ (((((False ∧ (p3 → (False ∨ (p5 ∨ (p5 → False))))) ∨ (p3 → True)) ∨ p4) ∨ p3) ∧ ((p4 → True) ∨ p2)))) ∨ p4) ∧ True) := by
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
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h1
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h2
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_153520568384834160319703667857 : ((True → ((p1 ∧ ((p5 ∧ p2) → ((p4 ∨ ((True ∨ ((p5 ∧ (p5 ∨ False)) ∧ p5)) → p2)) → p2))) ∧ False)) → (((p1 → p1) ∨ p3) ∧ p5)) := by
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
  -- We need to get the right conjuct of h3 based on <expert-advice>.
  let h4 := h3.right
  -- False on the left can always be used.
  apply False.elim h4
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h5 : True := by
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h6 := h1 h5
  -- We need to get the right conjuct of h6 based on <expert-advice>.
  let h7 := h6.right
  -- False on the left can always be used.
  apply False.elim h7



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_303238139314800503603331993051 : (False ∨ (p5 → ((p3 ∨ (((p1 → p1) ∨ (False → ((p2 ∨ (True ∧ (p4 → p4))) ∨ (True ∧ False)))) → ((p1 → p4) ∧ p1))) ∨ (p3 ∨ p5)))) := by
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
theorem thm_5_vars_206030416629824514138332777870 : ((p2 ∧ ((p4 ∧ p3) ∨ (p4 → True))) ∨ ((((p1 → p4) ∧ False) ∨ (True → p5)) ∨ ((p4 ∨ ((True ∧ p3) → (False ∨ (p5 ∨ p5)))) ∨ True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_60543537117647561476618073663 : ((True ∧ ((((p2 ∨ False) ∨ p5) ∨ (((((False ∨ False) ∧ p5) → p3) ∨ True) ∧ ((p1 ∨ (False ∧ True)) ∨ (True → (p2 → True))))) ∨ p2)) ∨ p1) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
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
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_697273085333151970000254108324 : (((((p1 ∨ p3) ∧ (p5 ∨ (((p5 ∨ (p1 ∨ True)) ∧ True) → p2))) ∧ ((False ∨ ((((p1 ∧ True) ∨ p4) ∨ p1) → (True → False))) ∧ p1)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_696963316686774046990341727018 : ((((((p5 → False) ∨ (((True → True) → True) → p5)) → (p1 → p5)) ∧ ((False ∨ ((p3 → (True → (p3 → (False ∧ True)))) ∧ p5)) → p4)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_677323701812441023457214035176 : (((((False ∨ ((p1 → (True ∧ ((((p2 → True) → p4) ∧ (p5 ∧ (p1 → p4))) ∨ True))) ∧ p2)) ∧ p2) ∨ (False → (p1 ∨ (p3 → True)))) ∨ p5) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- False on the left can always be used.
  apply False.elim h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_728906373576009249653779986421 : (((((True ∨ True) ∧ p2) → ((p1 ∨ (p4 ∧ (((p1 ∨ (p2 → (p2 ∨ ((False ∨ p5) ∨ p5)))) → p4) ∨ p5))) → (p4 ∧ (p5 ∧ p5)))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_54960865842004578842722646877 : ((((p3 ∨ (True ∧ p4)) ∨ (p5 ∧ True)) ∧ (p2 → ((p4 ∨ (False ∧ ((p5 ∨ p3) ∨ ((p3 → True) ∨ (p5 → p1))))) → (p3 ∨ p5)))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_317109955715278473872903115505 : (p3 ∨ (p5 → ((((p3 ∨ (p2 ∨ (((p4 ∧ (False → False)) ∧ (((False ∧ p3) ∧ p4) ∧ p1)) ∧ p3))) ∧ False) ∧ p2) ∨ ((False → True) → True)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h2
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_227970293473041050669742481561 : ((p3 ∧ (False ∨ p2)) ∨ ((((p1 ∨ ((False ∨ (True → False)) → True)) → ((p1 ∨ (p1 → (p4 → True))) ∨ p3)) → (p2 ∨ (p4 ∨ True))) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_37688216631511543038009411924 : (((((p1 → (((((p5 ∨ (p4 → True)) → ((p3 ∧ p3) → False)) ∧ p5) → p1) ∨ ((p5 ∨ False) → p4))) ∨ (p5 → p3)) → p4) ∧ p5) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_158302562827469579443269091084 : ((((p1 → False) → p2) → ((p1 ∨ (p3 ∨ (p1 ∨ ((True ∨ (p2 ∨ (p5 → p4))) ∨ p1)))) → p4)) ∨ ((((False ∧ p1) ∧ True) → p3) ∨ p1)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
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
  -- False on the left can always be used.
  apply False.elim h4



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_160838720631671799728821918878 : (((p3 → (False ∨ ((True ∧ p4) ∧ p1))) → (p1 ∨ ((((p2 ∨ (p3 → p5)) ∨ p2) → p4) ∧ p5))) → ((p1 ∧ ((p1 → p3) → p5)) ∨ True)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_149783396119327139319435779289 : ((False ∨ (((p1 → ((((p4 → ((p5 ∨ p2) → True)) → p5) ∧ False) ∧ p5)) → p5) ∨ (p4 → (False ∧ p2)))) ∨ (p4 → (p4 → (p1 ∨ p4)))) := by
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
theorem thm_5_vars_145928353094225094106134799812 : ((True ∧ ((p1 → ((p3 → (p2 ∨ p4)) ∨ ((((True ∧ p1) ∨ True) → p2) → ((p3 ∨ False) ∨ p2)))) ∨ True)) ∧ ((p3 ∨ (p1 ∧ p2)) → True)) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_350094855846011737799895961768 : (p4 → (((((((p4 ∨ p3) → p2) → ((p3 → True) ∨ p5)) → p3) ∧ (((p2 ∨ (p3 ∨ p1)) → p1) → p1)) ∨ ((p4 ∧ p1) ∨ p4)) ∨ True)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_199308065020390141736077596759 : (((((p3 ∨ True) ∨ (p3 ∨ p5)) ∨ False) ∨ p2) → (((p4 ∧ p3) ∨ ((((p4 ∨ (p5 ∨ p1)) ∨ True) ∨ p2) ∧ (True ∧ (True ∨ p4)))) ∨ p4)) := by
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
          -- Show the left disjunct based on <expert-advice>.
          apply Or.inl
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- Conjunctions on the right can always be decomposed.
          apply And.intro
          -- Show the left disjunct based on <expert-advice>.
          apply Or.inl
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- True on the right can always be proven directly.
          apply True.intro
          -- Conjunctions on the right can always be decomposed.
          apply And.intro
          -- True on the right can always be proven directly.
          apply True.intro
          -- Show the left disjunct based on <expert-advice>.
          apply Or.inl
          -- True on the right can always be proven directly.
          apply True.intro
        case inr h6 =>
          -- Show the left disjunct based on <expert-advice>.
          apply Or.inl
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- Conjunctions on the right can always be decomposed.
          apply And.intro
          -- Show the left disjunct based on <expert-advice>.
          apply Or.inl
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- True on the right can always be proven directly.
          apply True.intro
          -- Conjunctions on the right can always be decomposed.
          apply And.intro
          -- True on the right can always be proven directly.
          apply True.intro
          -- Show the left disjunct based on <expert-advice>.
          apply Or.inl
          -- True on the right can always be proven directly.
          apply True.intro
      case inr h7 =>
        -- Disjunctions on the left can always be decomposed.
        cases h7
        case inl h8 =>
          -- Show the left disjunct based on <expert-advice>.
          apply Or.inl
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- Conjunctions on the right can always be decomposed.
          apply And.intro
          -- Show the left disjunct based on <expert-advice>.
          apply Or.inl
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- True on the right can always be proven directly.
          apply True.intro
          -- Conjunctions on the right can always be decomposed.
          apply And.intro
          -- True on the right can always be proven directly.
          apply True.intro
          -- Show the left disjunct based on <expert-advice>.
          apply Or.inl
          -- True on the right can always be proven directly.
          apply True.intro
        case inr h9 =>
          -- Show the left disjunct based on <expert-advice>.
          apply Or.inl
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- Conjunctions on the right can always be decomposed.
          apply And.intro
          -- Show the left disjunct based on <expert-advice>.
          apply Or.inl
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- True on the right can always be proven directly.
          apply True.intro
          -- Conjunctions on the right can always be decomposed.
          apply And.intro
          -- True on the right can always be proven directly.
          apply True.intro
          -- Show the left disjunct based on <expert-advice>.
          apply Or.inl
          -- True on the right can always be proven directly.
          apply True.intro
    case inr h10 =>
      -- False on the left can always be used.
      apply False.elim h10
  case inr h11 =>
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Conjunctions on the right can always be decomposed.
    apply And.intro
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h11
    -- Conjunctions on the right can always be decomposed.
    apply And.intro
    -- True on the right can always be proven directly.
    apply True.intro
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- True on the right can always be proven directly.
    apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_315230521013563916185623273789 : (p3 ∨ (((p3 ∧ (p2 ∧ False)) ∧ p1) ∨ (((((p2 ∨ p2) ∨ p3) → ((p4 → (False → False)) → (((False ∧ p3) → p3) ∧ p1))) ∧ p2) → True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_300564442652146796200027953254 : (False ∨ ((True ∧ (((p2 ∧ True) → False) ∨ (((p1 ∨ False) ∧ ((p4 → (True → p5)) → (p2 ∨ p3))) → False))) ∨ ((False ∨ (False → p3)) ∨ True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_111037703992163281196637345909 : ((((p1 ∨ (p4 → ((p3 → ((((p4 ∧ p1) ∧ p2) ∨ False) ∨ (p1 → p3))) ∨ True))) ∧ (((p5 ∧ p4) ∧ True) → True)) ∧ p1) ∨ (True ∨ False)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_807460441222208896529828593963 : (((p4 → (((False → (p5 → ((p2 ∧ p3) ∨ p5))) ∧ True) → ((p3 ∧ ((True ∧ p1) ∧ ((p5 ∨ (p2 ∨ p5)) ∨ p4))) ∨ (p3 ∧ p4)))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_175036193011973978128490913517 : ((p1 ∧ (p4 → ((p2 ∨ True) → ((p5 → p4) → (False ∧ (p2 ∨ (p1 ∧ p4))))))) → (((p3 ∨ ((p3 ∨ True) → p3)) ∧ p3) ∨ (p1 ∨ True))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- One of the premise coincides with the conclusion.
  exact h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_246408036093378865237417271742 : ((p5 ∧ True) ∨ ((False → p1) ∧ (((True ∨ p3) → (((((p4 ∧ p5) ∧ p5) ∧ p2) ∨ False) ∨ True)) ∨ (((True → False) ∧ True) ∧ (p5 → p5))))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h1
  -- False on the left can always be used.
  apply False.elim h1
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
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
theorem thm_5_vars_124893863759425678644163737804 : (((((True → p3) ∨ p2) ∧ p1) → ((False → p3) ∧ ((p5 → ((p5 → ((p4 → (p5 ∨ p1)) ∨ p5)) ∧ (False → p3))) ∧ p4))) → (p3 ∨ True)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_245830728694184929529780268677 : ((p3 ∧ p4) ∨ (((p2 ∧ p1) → (p5 → ((((p2 → ((p3 ∨ True) ∧ ((p1 ∧ (False ∨ False)) ∨ p2))) ∧ (False ∧ p4)) ∨ p5) ∨ p3))) ∨ p2)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Conjunctions on the left can always be decomposed.
  let h3 := h1.left
  let h4 := h1.right
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_157117431003653977361826695821 : ((((((p3 ∨ ((p1 ∧ p2) ∨ ((p5 ∧ (p2 ∧ (p3 ∧ p5))) → False))) ∧ p4) ∨ False) ∧ p4) → p1) ∨ ((p5 ∧ (True ∨ (True ∧ True))) → p5)) := by
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
    -- One of the premise coincides with the conclusion.
    exact h2
  case inr h5 =>
    -- Conjunctions on the left can always be decomposed.
    let h6 := h5.left
    let h7 := h5.right
    -- One of the premise coincides with the conclusion.
    exact h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_703233071265677190165721620974 : ((((p1 ∧ (p2 ∧ (p1 ∨ ((True → False) ∧ (False → False))))) ∨ (((False → True) → p2) ∧ (p4 ∨ ((((p4 ∧ False) ∧ p2) ∨ p2) ∨ False)))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_65282240754051260745267681863 : ((p3 ∨ ((True ∧ (((False ∨ (p2 ∧ p4)) ∨ ((False → True) → p5)) ∨ (p4 ∧ (((p1 → p3) ∨ False) → (p4 → False))))) ∧ (False ∧ p2))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_701165434465744145476989491949 : (((((p5 → ((((p3 ∨ p5) ∨ p5) → p5) ∨ False)) → p4) ∧ (((p5 ∧ True) → ((((p4 ∨ p3) → (False ∨ False)) ∧ False) ∨ p5)) → False)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_715173708614649826139314659187 : ((((True → ((p3 ∨ p1) ∨ (p5 ∧ p5))) → ((p2 ∧ (((p2 ∧ False) ∧ True) → (p3 ∧ ((p2 ∧ ((True ∧ p3) ∧ True)) → p1)))) ∨ p5)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_115448573855653190473451645018 : (((((p2 ∨ p5) → p5) ∨ (p1 ∧ (False → p5))) ∨ (True → ((p4 ∧ (p2 ∨ (p1 ∨ ((False → (True → p5)) → p4)))) ∨ p3))) ∨ (p1 → True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_677425772882016737230913536513 : (((((((((True ∨ (True → p5)) → ((p3 ∨ p5) ∧ (p2 → p3))) → True) ∧ p4) ∧ (p2 ∨ p2)) ∨ False) ∨ (p3 ∨ (False ∧ (False ∧ p1)))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_670165542306345708015951556355 : (((((p2 ∧ (p2 ∨ ((p4 ∧ p2) → p3))) → ((False ∨ (True → (p1 ∧ (False ∨ p3)))) ∧ (p1 ∨ (p3 ∨ p4)))) ∨ (p3 → (p3 → p3))) ∨ p5) ∧ True) := by
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
  -- One of the premise coincides with the conclusion.
  exact h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_42517245444930464542013011069 : (((False ∨ (p5 ∧ ((((p1 ∧ False) ∨ True) ∧ ((p4 ∨ ((((p3 ∧ p2) → p5) ∨ (True → (p4 → p3))) → p1)) ∧ p2)) ∧ p4))) ∨ True) ∨ p2) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_629272551309911849140648889447 : (((((((((p5 → p4) → ((p4 → (((p3 ∨ p5) → p3) ∧ p1)) ∨ (p4 → ((True → p1) ∧ p2)))) → False) → p1) → p5) ∨ p2) → p2) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_149012592802346628646572203167 : ((((False ∧ p2) ∨ p4) ∨ (((p4 ∧ (((True ∧ (p2 → p1)) → p4) ∧ (p3 ∧ p2))) → (p1 ∨ p5)) → False)) ∨ ((p5 ∧ p3) ∨ (p1 ∨ True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_749560845757201273739673740108 : (((True ∧ ((p2 ∨ ((p5 ∧ (p5 → p5)) → (((True ∨ (((False → (p4 → (False ∧ p5))) → p1) → (True → False))) → p2) → p4))) ∧ p4)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_111200845207390827822657979562 : (((((False ∧ p4) ∧ p1) ∨ ((((p5 → p3) → (p3 → (True → (p2 → p3)))) → p4) ∨ ((p2 → (p4 ∧ False)) ∨ p3))) ∧ p1) ∨ (True ∨ p5)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_165656167300744237916431527102 : ((((p1 ∨ (p2 ∨ p1)) ∧ (p4 → p3)) ∨ ((((p5 → False) ∧ True) → (p5 ∨ p4)) ∨ True)) ∨ ((p2 ∨ (False ∧ p1)) → (False → (p3 → p4)))) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_18913159636309780789326704976 : (((False ∧ ((((p5 ∧ p3) → (p3 ∧ True)) → ((False ∨ (False ∧ (p2 → p2))) ∨ p4)) ∨ p1)) ∨ ((p1 ∨ False) → (p4 → (p5 → True)))) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Implications on the right can always be decomposed.
  intro h3
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_183607978139811277698215185994 : ((False → ((True → p3) → ((p1 ∧ p2) ∧ (False ∧ (p2 ∧ True))))) ∧ (((False ∨ ((p2 → (p4 ∨ p4)) ∨ (False ∨ p2))) ∧ (p3 ∧ p5)) ∨ True)) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- False on the left can always be used.
  apply False.elim h1
  -- False on the left can always be used.
  apply False.elim h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- False on the left can always be used.
  apply False.elim h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- False on the left can always be used.
  apply False.elim h1
  -- True on the right can always be proven directly.
  apply True.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_20865770816539807050902119761 : ((((False ∧ (False ∧ (p5 ∨ p3))) ∨ (((p2 ∨ p4) ∨ False) → p1)) ∨ (p1 ∨ (p5 → ((((p1 ∨ p1) ∨ False) → (p2 ∨ p3)) ∨ p5)))) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
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
theorem thm_5_vars_352181661910954078398964891113 : (p4 → (((p3 ∨ (False ∧ p1)) → True) ∧ ((p3 ∧ p3) ∨ (((((p3 ∨ (p5 ∧ False)) ∨ (p5 → p5)) → ((p4 → p5) ∧ False)) ∨ False) ∨ p4)))) := by
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
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_185832528280132824046129330122 : ((((p4 ∧ (p1 ∨ (p2 ∨ (p1 ∧ (True ∨ False))))) ∧ p5) ∧ p1) → (((((p5 ∧ (True ∨ p4)) → False) ∧ p2) ∨ (True ∨ (False ∨ p5))) ∧ True)) := by
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
  let h6 := h4.left
  let h7 := h4.right
  -- Disjunctions on the left can always be decomposed.
  cases h7
  case inl h8 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- True on the right can always be proven directly.
    apply True.intro
  case inr h9 =>
    -- Disjunctions on the left can always be decomposed.
    cases h9
    case inl h10 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- True on the right can always be proven directly.
      apply True.intro
    case inr h11 =>
      -- Conjunctions on the left can always be decomposed.
      let h12 := h11.left
      let h13 := h11.right
      -- Disjunctions on the left can always be decomposed.
      cases h13
      case inl h14 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- True on the right can always be proven directly.
        apply True.intro
      case inr h15 =>
        -- False on the left can always be used.
        apply False.elim h15
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_299291507816449962549792910371 : (False ∨ ((((p2 ∧ (((False ∧ ((p4 ∨ p1) → p1)) ∨ p4) ∨ False)) → p4) → ((p4 ∨ (((True ∨ (p3 → False)) ∧ p1) → p2)) → p4)) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_351398771898799818730839849270 : (p4 → (((p1 → (False ∨ (((p3 ∨ p2) ∧ (False ∨ (((False ∨ p3) ∧ True) → p3))) ∨ p5))) ∧ (p3 ∧ p2)) ∨ (p2 → (p2 ∨ (p2 → p2))))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h2
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- One of the premise coincides with the conclusion.
  exact h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_148327719158074124282529921493 : ((((p5 ∧ ((((((False ∧ p3) → p4) → p4) → p3) ∨ p3) ∧ p3)) ∧ True) ∧ (p5 → (p2 ∨ (True ∨ True)))) ∨ (True ∨ (p4 ∧ (p3 ∧ p4)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_351648031585273449228203475684 : (p4 → ((p5 ∧ ((((p3 → p4) → ((True ∨ (False → p2)) → False)) ∧ p3) ∨ (p3 ∧ p1))) ∨ (((True ∧ p4) ∧ (p5 → (True → p2))) ∨ True))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_46319294361355619183278185278 : (((((p5 ∧ (((p3 → (p4 → p1)) → (False ∧ (True ∨ p3))) ∨ p2)) ∧ (p4 → True)) ∨ (p4 → ((False ∨ True) ∨ p1))) ∧ (p1 → p1)) ∨ False) := by
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
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- Implications on the right can always be decomposed.
  intro h2
  -- One of the premise coincides with the conclusion.
  exact h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_45707930635205581090924135854 : (((True → ((p4 ∧ (p3 → (((p3 ∧ p4) ∨ p1) ∧ ((p4 → p3) ∨ ((((p4 ∨ p4) ∨ (p1 ∧ p4)) ∨ True) → p4))))) → True)) → p1) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_82608945729911942011399673481 : (((((p4 ∨ ((p5 ∧ (p2 ∨ p1)) ∧ p5)) → (p4 ∨ ((p1 ∧ p1) ∨ ((True ∨ p4) ∨ True)))) → p4) ∨ ((p3 ∨ (p2 ∧ p3)) ∧ p4)) → p4) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h2 =>
    -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
    have h3 : ((p4 ∨ ((p5 ∧ (p2 ∨ p1)) ∧ p5)) → (p4 ∨ ((p1 ∧ p1) ∨ ((True ∨ p4) ∨ True)))) := by
      -- Implications on the right can always be decomposed.
      intro h4
      -- Disjunctions on the left can always be decomposed.
      cases h4
      case inl h5 =>
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- One of the premise coincides with the conclusion.
        exact h5
      case inr h6 =>
        -- Conjunctions on the left can always be decomposed.
        let h7 := h6.left
        let h8 := h6.right
        -- Conjunctions on the left can always be decomposed.
        let h9 := h7.left
        let h10 := h7.right
        -- Disjunctions on the left can always be decomposed.
        cases h10
        case inl h11 =>
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- True on the right can always be proven directly.
          apply True.intro
        case inr h12 =>
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- True on the right can always be proven directly.
          apply True.intro
    -- We have shown the premise of h2, we can now drive its conclusion.
    let h13 := h2 h3
    -- One of the premise coincides with the conclusion.
    exact h13
  case inr h14 =>
    -- Conjunctions on the left can always be decomposed.
    let h15 := h14.left
    let h16 := h14.right
    -- Disjunctions on the left can always be decomposed.
    cases h15
    case inl h17 =>
      -- One of the premise coincides with the conclusion.
      exact h16
    case inr h18 =>
      -- Conjunctions on the left can always be decomposed.
      let h19 := h18.left
      let h20 := h18.right
      -- One of the premise coincides with the conclusion.
      exact h16



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_44093439373697852373513917506 : ((((p3 ∨ ((p1 → ((p2 → (p3 → False)) ∧ (p4 ∧ p1))) ∨ ((p4 ∧ (p2 → (p1 → p2))) ∧ p1))) ∧ (p2 → (False → p3))) → p4) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_213626044400682364818123466775 : ((((p3 ∧ p5) ∨ p5) ∨ p5) ∨ (((((((False ∧ (((False ∧ p2) → p5) ∧ p3)) ∧ False) ∨ p1) ∧ p3) → p5) ∨ False) ∨ (p1 → (p1 ∧ p1)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- One of the premise coincides with the conclusion.
  exact h1
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_707216593227355385452891006331 : (((((p1 → ((p1 ∨ (p1 ∨ p2)) ∨ p3)) → p2) ∨ (p1 → ((p2 ∧ (False ∧ ((False ∧ (True ∧ p4)) ∧ (p4 ∨ True)))) → (True ∧ False)))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_63287006886539636682577507363 : ((p5 ∧ (((False ∧ False) ∨ p5) ∧ (((p2 ∧ p5) → ((p4 → (p2 → p2)) ∨ p1)) → ((False → True) → (((False → True) ∨ False) → p1))))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_705835184042941654703225326501 : ((((((p5 ∨ p2) ∧ True) ∧ (True ∨ (p5 ∧ p2))) ∧ (((True → p2) ∨ (p3 ∧ ((p2 ∨ p4) ∧ (((True → True) ∧ True) → False)))) → p5)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_751933432020870494455436520956 : (((True ∧ (p3 ∨ ((p3 ∨ p5) → ((p1 ∨ (((p3 ∨ p5) ∨ (p2 → (p4 → True))) → ((True ∧ p2) → p5))) ∧ ((False → False) ∨ p5))))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_49470677049387853077924168028 : (((((((p5 ∨ ((True ∨ (p3 → (((p1 → p3) → p4) ∧ False))) → p2)) ∨ (False → p2)) ∨ True) ∨ p5) → p4) → ((p2 → p5) → False)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_137033890966608689245041558292 : (((p5 ∨ p2) → (((((True ∧ p3) ∨ ((p1 ∨ (False → p1)) → ((p1 ∧ p3) ∧ (p5 ∨ p3)))) ∧ p5) → True) → False)) ∨ ((p1 → p1) ∨ p2)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_627919648876787395133820374658 : ((((((((p1 ∨ (p5 ∧ (p4 ∨ p5))) ∨ (p2 ∧ p5)) ∨ p1) → (((p2 ∨ p1) → ((p4 ∨ (p4 ∧ True)) ∧ False)) ∨ p1)) ∧ p1) → p3) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_768322127486320110148845724674 : (((p5 ∧ ((p4 → ((((True → p5) → ((p4 ∧ p3) → (True ∧ ((p4 → (p1 ∧ p2)) → p2)))) ∨ p2) → p5)) ∨ (False ∧ (p2 ∧ p1)))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_42019744903021787568826246008 : ((((True ∧ p5) ∨ ((((False ∨ p2) ∨ ((((False ∧ p1) ∧ (((p1 ∨ p2) → p1) → p1)) ∧ (p1 ∨ True)) → p1)) → p1) ∨ p1)) ∨ True) ∨ p4) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_64860625362923405654983450355 : ((p2 ∨ (((((((False ∧ True) → True) ∧ p2) ∨ ((p4 ∧ (p1 ∨ p3)) → False)) ∨ ((False ∨ p1) ∨ (True → p4))) ∧ p5) ∨ (p4 ∨ True))) ∨ p3) := by
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
theorem thm_5_vars_112110834492696843081584244525 : ((((True → p2) → (((p4 ∨ True) → (((p5 ∧ p1) → (p5 ∧ p4)) ∧ ((p2 ∨ p2) ∨ True))) → ((False → p4) → p1))) ∨ p4) ∨ (p5 → p5)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_717274708303298354436257472505 : ((((p4 ∨ ((p4 ∧ True) ∧ p3)) ∧ ((p1 ∧ (p2 ∧ ((((p2 ∨ p1) ∨ ((p5 ∧ p1) ∧ p1)) → p1) ∨ True))) ∨ (p1 ∨ (p3 ∧ p1)))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_47111527679589172680703986698 : (((((((((p3 ∧ (((False ∨ False) ∨ (p5 ∧ p2)) → p1)) → p1) ∧ p1) → p3) ∧ p4) → p2) ∨ (p5 ∨ (False ∧ True))) ∨ (p3 → p3)) ∨ p2) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_258357550258003551048864686551 : ((p5 ∨ False) → ((True ∨ (p1 ∨ ((p3 ∧ ((p2 → p5) ∨ p4)) ∨ (((True → (p5 ∨ p3)) ∧ True) → p5)))) → ((p3 ∨ p3) ∨ (p4 ∨ True)))) := by
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
    -- Disjunctions on the left can always be decomposed.
    cases h6
    case inl h7 =>
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
        -- False on the left can always be used.
        apply False.elim h9
    case inr h10 =>
      -- Disjunctions on the left can always be decomposed.
      cases h10
      case inl h11 =>
        -- Conjunctions on the left can always be decomposed.
        let h12 := h11.left
        let h13 := h11.right
        -- Disjunctions on the left can always be decomposed.
        cases h13
        case inl h14 =>
          -- Disjunctions on the left can always be decomposed.
          cases h1
          case inl h15 =>
            -- Show the left disjunct based on <expert-advice>.
            apply Or.inl
            -- Show the left disjunct based on <expert-advice>.
            apply Or.inl
            -- One of the premise coincides with the conclusion.
            exact h12
          case inr h16 =>
            -- False on the left can always be used.
            apply False.elim h16
        case inr h17 =>
          -- Disjunctions on the left can always be decomposed.
          cases h1
          case inl h18 =>
            -- Show the left disjunct based on <expert-advice>.
            apply Or.inl
            -- Show the left disjunct based on <expert-advice>.
            apply Or.inl
            -- One of the premise coincides with the conclusion.
            exact h12
          case inr h19 =>
            -- False on the left can always be used.
            apply False.elim h19
      case inr h20 =>
        -- Disjunctions on the left can always be decomposed.
        cases h1
        case inl h21 =>
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- True on the right can always be proven directly.
          apply True.intro
        case inr h22 =>
          -- False on the left can always be used.
          apply False.elim h22



