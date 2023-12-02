variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_429398071957096825171083652591 : (((((((p5 ∨ ((p1 → p4) ∧ True)) ∧ (False ∧ (p1 → True))) ∨ ((False ∧ p5) ∧ p3)) ∧ (((p2 ∧ p3) ∨ p1) ∧ True)) ∨ (p1 → p1)) ∧ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- One of the premise coincides with the conclusion.
  exact h1
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_307364604329468388526863396210 : (p1 ∨ (p4 ∨ ((((p4 → p2) ∧ False) ∨ (p5 → ((p4 ∧ p5) → ((((p3 ∧ (True ∨ (p2 ∧ (p3 → p1)))) → False) ∨ p4) ∨ True)))) ∨ True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_311245892559797782410243831663 : (p2 ∨ ((p5 → p1) → (((((((((p4 ∧ False) ∨ (p2 ∨ p1)) ∧ (True ∨ p4)) ∨ p4) ∧ p3) ∧ (p4 ∧ p2)) ∧ (p1 ∨ p4)) ∨ True) ∨ True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_178433382722201383971224219319 : (((((p5 ∨ (p4 ∨ (p5 ∨ False))) ∨ p3) ∨ p2) ∧ ((p5 ∨ p1) ∧ p4)) ∨ (True ∨ (p1 ∧ (True → ((p5 ∧ (p4 ∨ p2)) ∨ (p1 → p3)))))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_205263192584140846660085753055 : ((((p4 ∧ p4) → p5) ∨ (p3 ∨ p4)) ∨ ((True ∨ True) → (False ∨ (p2 ∨ ((p1 → p3) ∨ (p1 → (((True → p1) ∨ (p3 → p5)) → p1))))))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
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
    -- Disjunctions on the left can always be decomposed.
    cases h4
    case inl h5 =>
      -- One of the premise coincides with the conclusion.
      exact h3
    case inr h6 =>
      -- One of the premise coincides with the conclusion.
      exact h3
  case inr h7 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h8
    -- Implications on the right can always be decomposed.
    intro h9
    -- Disjunctions on the left can always be decomposed.
    cases h9
    case inl h10 =>
      -- One of the premise coincides with the conclusion.
      exact h8
    case inr h11 =>
      -- One of the premise coincides with the conclusion.
      exact h8



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_113938495602469384304255716190 : ((((p3 ∨ (((p5 ∧ p3) → p5) ∧ p1)) ∧ (((True ∧ p1) → p5) ∨ (p3 → ((p3 → False) → False)))) ∧ ((p2 ∧ p4) ∨ p3)) ∨ (True ∨ p5)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_473337378171372990888999910888 : ((((((p5 ∧ True) → (p1 ∧ (False ∧ p2))) ∧ ((p5 → p5) → p2)) → (((((p2 → p5) ∧ (p2 ∨ p5)) ∨ p5) → p3) ∨ (True ∧ True))) ∧ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
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
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_257682120317843290455578953526 : ((p3 ∨ p3) → (((((p4 ∨ p4) ∨ (((p2 → p5) ∧ p2) ∨ (False → ((p5 ∧ p4) ∨ True)))) ∨ ((p1 → p3) ∧ p1)) ∨ p3) ∨ (False ∧ p2))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h2 =>
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h2
  case inr h3 =>
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h3



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_111392048638114736643674555480 : (((p1 ∨ ((p4 ∧ ((p2 ∧ (False ∨ True)) → (((False ∧ p3) ∧ p1) → ((True ∨ (p2 → p5)) → (p3 ∨ p1))))) ∨ p2)) ∧ p4) ∨ (p2 ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_305760232733387143986545460404 : (p1 ∨ (((p1 → ((p2 ∧ (p2 → False)) ∧ p5)) ∧ p4) ∨ (((p3 ∨ ((p3 ∨ (p3 → (False ∨ (False → p1)))) ∨ p3)) ∨ False) ∨ (p5 → p4)))) := by
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
  -- False on the left can always be used.
  apply False.elim h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_143929291090529013886376991648 : ((((((True → False) ∧ p1) ∧ (p4 ∧ p5)) ∨ ((True ∧ (p2 ∨ p3)) ∨ ((p2 → (p1 ∨ p2)) ∨ p3))) ∨ p5) ∧ ((p4 → p4) ∨ (p4 ∧ True))) := by
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
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h1
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h2
  -- One of the premise coincides with the conclusion.
  exact h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_259738813100023959301205572134 : ((p1 → p2) → ((p3 ∨ ((((False → p2) → p5) ∧ (p2 ∨ (p3 ∨ p5))) ∧ (False ∧ (((p4 → (p4 → (False ∨ p2))) → p1) ∧ p3)))) ∨ True)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_727377064599085080529635269970 : ((((p2 ∧ (p3 ∨ False)) ∨ ((p5 → (p3 → (False ∧ (((True ∨ False) ∧ p1) ∧ (p2 → p2))))) ∨ ((p5 → ((p4 ∨ False) ∨ True)) ∨ p3))) ∨ p2) ∧ True) := by
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
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_244736218316145469260866228817 : ((p1 ∧ False) ∨ (((p5 ∧ (p5 ∧ (p5 ∨ (((p4 ∨ p3) ∨ (p3 ∧ (True ∨ p3))) ∨ p3)))) ∨ ((p2 ∨ p1) ∨ (p5 ∨ (False → p2)))) ∨ p1)) := by
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
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_741107909600797625090586132765 : ((((p4 ∨ False) ∨ ((((False ∨ ((((p3 → p1) → p2) ∧ (((p5 ∨ p4) ∧ True) ∨ (p1 ∨ p5))) ∧ p2)) ∧ p3) ∨ p5) ∧ (p2 → p2))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_784975480405650258240983795090 : (((p3 ∨ (p4 → ((p3 ∨ ((p2 → (p2 ∧ p1)) ∧ True)) ∨ ((((p2 → p2) → True) ∧ ((((p2 → p2) → p4) ∨ p1) → p3)) → p2)))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_112156191250755611383772518527 : (((p2 ∧ (((True → ((p1 ∧ p3) ∨ (True ∨ True))) ∨ p3) ∧ ((p1 → (p5 ∨ p3)) ∧ (p4 ∨ (p4 ∨ (p2 ∨ p5)))))) ∨ p5) ∨ (p3 ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_42209449313176002866743955059 : (((True ∧ (p4 → ((((p5 → p1) → p2) ∨ p3) → (p3 ∨ (p3 ∨ (p4 → (((p1 ∧ (True → p2)) → (p1 ∧ False)) → p3))))))) ∨ p1) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_167824993770765300914367978693 : (((p5 ∨ (((p2 ∨ p1) ∧ (p1 ∧ p4)) → (p3 → p5))) ∧ ((p1 ∧ p4) ∧ (True → p4))) → (p3 → ((False ∨ p5) ∧ ((p1 ∨ p5) ∧ p4)))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Conjunctions on the left can always be decomposed.
  let h3 := h1.left
  let h4 := h1.right
  -- Disjunctions on the left can always be decomposed.
  cases h3
  case inl h5 =>
    -- Conjunctions on the left can always be decomposed.
    let h6 := h4.left
    let h7 := h4.right
    -- Conjunctions on the left can always be decomposed.
    let h8 := h6.left
    let h9 := h6.right
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h5
  case inr h10 =>
    -- Conjunctions on the left can always be decomposed.
    let h11 := h4.left
    let h12 := h4.right
    -- Conjunctions on the left can always be decomposed.
    let h13 := h11.left
    let h14 := h11.right
    -- We want to use the implication h10 based on <expert-advice>. So we show its premise.
    have h15 : ((p2 ∨ p1) ∧ (p1 ∧ p4)) := by
      -- Conjunctions on the right can always be decomposed.
      apply And.intro
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- One of the premise coincides with the conclusion.
      exact h13
      -- Conjunctions on the right can always be decomposed.
      apply And.intro
      -- One of the premise coincides with the conclusion.
      exact h13
      -- One of the premise coincides with the conclusion.
      exact h14
    -- We have shown the premise of h10, we can now drive its conclusion.
    let h16 := h10 h15
    -- We want to use the implication h16 based on <expert-advice>. So we show its premise.
    have h17 : p3 := by
      -- One of the premise coincides with the conclusion.
      exact h2
    -- We have shown the premise of h16, we can now drive its conclusion.
    let h18 := h16 h17
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h18
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Conjunctions on the left can always be decomposed.
  let h19 := h1.left
  let h20 := h1.right
  -- Disjunctions on the left can always be decomposed.
  cases h19
  case inl h21 =>
    -- Conjunctions on the left can always be decomposed.
    let h22 := h20.left
    let h23 := h20.right
    -- Conjunctions on the left can always be decomposed.
    let h24 := h22.left
    let h25 := h22.right
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- One of the premise coincides with the conclusion.
    exact h24
  case inr h26 =>
    -- Conjunctions on the left can always be decomposed.
    let h27 := h20.left
    let h28 := h20.right
    -- Conjunctions on the left can always be decomposed.
    let h29 := h27.left
    let h30 := h27.right
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- One of the premise coincides with the conclusion.
    exact h29
  -- Conjunctions on the left can always be decomposed.
  let h31 := h1.left
  let h32 := h1.right
  -- Disjunctions on the left can always be decomposed.
  cases h31
  case inl h33 =>
    -- Conjunctions on the left can always be decomposed.
    let h34 := h32.left
    let h35 := h32.right
    -- Conjunctions on the left can always be decomposed.
    let h36 := h34.left
    let h37 := h34.right
    -- One of the premise coincides with the conclusion.
    exact h37
  case inr h38 =>
    -- Conjunctions on the left can always be decomposed.
    let h39 := h32.left
    let h40 := h32.right
    -- Conjunctions on the left can always be decomposed.
    let h41 := h39.left
    let h42 := h39.right
    -- One of the premise coincides with the conclusion.
    exact h42



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_773394711077299347007682060273 : (((False ∨ ((p3 → ((((((p3 ∧ p4) → ((p1 ∧ p4) ∨ ((p1 ∨ p4) → (p1 ∧ (p3 → True))))) ∨ p4) ∧ p2) → p2) → p2)) ∧ p4)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_174106615492716582359295005609 : ((((p3 ∧ False) → (((True ∧ True) ∨ p1) → (p2 ∨ (p1 ∨ p4)))) ∧ (p5 ∧ p4)) → (((p1 ∨ p1) → (False ∧ ((p2 ∧ False) ∧ False))) ∨ p4)) := by
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
  -- One of the premise coincides with the conclusion.
  exact h5



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_157223541982992962938263954098 : (((((p3 ∧ (False ∧ ((False ∧ True) → p2))) ∧ (p2 ∨ (p4 ∧ False))) → (p5 ∨ (True ∧ p4))) → p4) ∨ (p2 ∨ (True ∨ ((p5 ∧ False) ∧ p2)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_748379792519843850336999176281 : ((((p2 → p3) → ((((p5 ∧ ((((p1 ∨ p4) ∨ p2) → p3) ∨ (True ∧ ((False → True) → p5)))) ∨ (p3 ∨ True)) ∧ (p5 → True)) ∧ True)) ∨ False) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
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
  -- Implications on the right can always be decomposed.
  intro h2
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_324477737773103203866473035242 : (p5 ∨ (((p3 ∨ (False → True)) ∧ p3) ∨ ((False ∨ (((((p1 → ((p4 → p2) ∧ True)) ∧ p4) ∨ (p1 ∨ (p1 → True))) ∨ False) → False)) → p4))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
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
    -- We want to use the implication h3 based on <expert-advice>. So we show its premise.
    have h4 : ((((p1 → ((p4 → p2) ∧ True)) ∧ p4) ∨ (p1 ∨ (p1 → True))) ∨ False) := by
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Implications on the right can always be decomposed.
      intro h5
      -- True on the right can always be proven directly.
      apply True.intro
    -- We have shown the premise of h3, we can now drive its conclusion.
    let h6 := h3 h4
    -- False on the left can always be used.
    apply False.elim h6



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_178476243493541203308126096876 : ((((p3 ∨ (p5 ∧ (False → (p4 ∧ p4)))) ∨ False) ∨ (p4 → (p3 ∧ True))) ∨ (True ∨ (p1 ∧ ((p5 → ((p5 ∧ p5) ∧ (p3 ∧ p3))) → p2)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_148949492505573258850611688382 : ((((False ∧ p2) ∧ p5) ∧ (p5 ∧ (p5 ∨ ((True ∨ p5) → ((p1 → False) ∨ (p3 ∨ (p1 ∨ (p1 → p5)))))))) ∨ ((p1 ∨ False) ∨ (True ∨ p2))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_119460224922488834842665061944 : ((p4 → ((p5 ∧ (p3 ∨ p4)) ∨ (((((p1 → p5) → ((p3 ∨ p1) ∨ p5)) ∨ ((p3 → p2) → (False → p3))) ∨ True) ∨ p5))) ∨ (False → p4)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_188291112661536338924333298386 : (((p5 ∨ ((False ∧ p4) → ((p1 ∧ p5) ∨ False))) ∨ p1) ∧ ((True ∧ (True ∧ (p1 ∧ (((p3 ∧ (p4 → False)) → p1) ∧ p5)))) ∨ (True ∨ True))) := by
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
  apply False.elim h2
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_233434002982426917252759772149 : ((False ∨ (True → True)) → ((p1 → p4) ∨ ((p1 ∧ p4) → ((p1 → True) → (((p2 → (p2 → p4)) → p5) ∨ ((p1 ∧ (p3 ∧ p1)) ∨ p1)))))) := by
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
    -- Implications on the right can always be decomposed.
    intro h4
    -- Implications on the right can always be decomposed.
    intro h5
    -- Conjunctions on the left can always be decomposed.
    let h6 := h4.left
    let h7 := h4.right
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h6



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_162907838982492321781749275925 : ((((((((False ∧ p3) ∧ False) → ((p5 → p4) ∧ p3)) ∧ p4) ∧ p1) ∨ p4) → (p2 ∨ p4)) ∧ ((p1 ∨ ((p4 ∨ (p1 ∧ p5)) ∨ True)) ∨ p5)) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h1
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h2 =>
    -- Conjunctions on the left can always be decomposed.
    let h3 := h2.left
    let h4 := h2.right
    -- Conjunctions on the left can always be decomposed.
    let h5 := h3.left
    let h6 := h3.right
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h6
  case inr h7 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h7
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_256529370147267729764559030825 : ((False ∨ p5) → ((p1 ∨ (((p2 → (p5 → (((p5 ∨ (p5 → p3)) ∨ p1) ∧ (p5 ∨ ((p2 ∧ True) → False))))) → p2) ∧ p3)) ∨ (p2 → p2))) := by
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
    -- Implications on the right can always be decomposed.
    intro h4
    -- One of the premise coincides with the conclusion.
    exact h4



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_159083822643404432213346587844 : ((True → ((p4 ∨ (p3 → ((p2 → p1) ∨ (p3 ∧ ((p1 ∧ p5) → ((True → p5) ∧ False)))))) ∨ p5)) ∨ ((False → (p5 ∧ True)) ∨ (p2 ∧ p1))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- False on the left can always be used.
  apply False.elim h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_50391531821449387197151892390 : ((((p1 → p5) ∨ ((p2 ∨ (p1 ∧ ((((True ∧ p1) → p5) ∧ (p2 → p4)) ∨ (p2 → True)))) ∨ False)) ∨ ((p1 → p5) → (p4 ∧ p1))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_458339735290789788917993705837 : ((((True ∧ ((((p5 → p1) ∨ p5) ∨ p1) ∧ ((((p2 ∨ p4) ∧ p2) ∨ p1) ∨ (False ∨ p3)))) ∨ ((((p3 ∧ p3) ∧ p5) ∧ p1) → True)) ∧ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
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
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_171340440349581403478961952445 : (((((p3 ∨ ((p3 ∧ (p1 ∧ (p3 ∧ p1))) ∧ (p2 ∧ False))) → True) → p3) ∧ p4) ∨ ((((p1 → (False ∨ False)) ∧ True) ∨ (False → p4)) ∨ p1)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_116280697172143673115183605715 : (((False ∨ (p5 → p2)) ∨ (((False ∨ (p4 ∧ ((((p4 → (True ∧ ((p5 ∨ p4) ∧ p5))) → p5) ∧ p5) ∧ p2))) → True) → p5)) ∨ (True ∨ p3)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_135130970726134317817259246163 : (((p3 ∧ ((((p3 ∨ True) → p2) → (p4 → p1)) → (((p4 ∧ (p4 → (True → p4))) → p4) → p3))) ∨ (p5 → p3)) ∨ (False ∨ (False ∨ True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_90923569001058701394324901346 : (((True → False) ∧ (p2 → (((p5 → p3) ∧ ((p3 ∧ p3) ∨ (p2 ∨ (p3 ∧ ((p1 → p2) → p4))))) → ((True → (True ∧ p5)) ∨ False)))) → p2) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
  have h4 : True := by
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h2, we can now drive its conclusion.
  let h5 := h2 h4
  -- False on the left can always be used.
  apply False.elim h5



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_192966088307235707818127756836 : (((p1 ∨ ((p5 → (p4 → p3)) → p3)) ∨ (p5 → p2)) → (p5 ∨ ((p5 → p5) → (((True ∧ (False ∨ p2)) ∧ p2) ∨ ((True ∧ p5) ∨ True))))) := by
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
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- True on the right can always be proven directly.
      apply True.intro
    case inr h5 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Implications on the right can always be decomposed.
      intro h6
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- True on the right can always be proven directly.
      apply True.intro
  case inr h7 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h8
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_179334653749752325803253879430 : ((p1 ∨ (((p3 ∨ ((p3 ∧ True) ∨ True)) → p3) → (p4 ∨ (p1 ∨ p3)))) ∨ ((p2 → ((p5 ∧ (p5 → ((p4 ∧ p1) ∨ p5))) → p4)) ∨ False)) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h2 : (p3 ∨ ((p3 ∧ True) ∨ True)) := by
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h3 := h1 h2
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h3



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_48444047848252106962484081124 : (((p5 → (((((((((True → p1) ∧ True) → p2) ∧ p4) ∨ (((True ∨ False) ∨ False) → p1)) → p3) ∨ True) ∧ p3) → p5)) → (True ∧ p4)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_111676310298680801964790394535 : ((((p5 → ((p4 → (p2 → (p1 → p5))) → (((p5 ∨ (p4 ∧ p4)) → (((p4 ∧ p2) → p1) → p1)) ∨ p1))) ∨ p1) ∨ True) ∨ (False ∧ p3)) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_245986462628070297440772302414 : ((p4 ∧ True) ∨ ((p5 → p2) → ((p1 ∧ ((((True → p1) ∧ (p5 ∨ ((p2 → p1) ∨ p1))) ∨ False) → p5)) → (p5 ∨ ((p3 ∧ p5) ∧ p2))))) := by
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
  have h5 : (((True → p1) ∧ (p5 ∨ ((p2 → p1) ∨ p1))) ∨ False) := by
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Conjunctions on the right can always be decomposed.
    apply And.intro
    -- Implications on the right can always be decomposed.
    intro h6
    -- One of the premise coincides with the conclusion.
    exact h3
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h3
  -- We have shown the premise of h4, we can now drive its conclusion.
  let h7 := h4 h5
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- One of the premise coincides with the conclusion.
  exact h7



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_656078067916075921210176408627 : (((((p5 ∧ (((((p2 ∨ p3) → (p3 → True)) ∨ p5) ∧ p1) → (p1 → (False ∧ p5)))) → (p2 ∧ (p3 ∨ (False → p5)))) ∨ (False → p5)) ∨ p4) ∧ True) := by
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
theorem thm_5_vars_787625172256545981617554969912 : (((p4 ∨ (p3 ∨ ((p4 ∨ ((((((((p2 ∧ (True ∨ (p1 ∨ True))) ∧ p5) → p4) → (p1 ∨ True)) ∨ p5) → True) ∨ False) ∧ p5)) → p4))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_679294162432792545253082813002 : ((((p1 → (((p2 ∨ (True ∨ p1)) → (p2 ∧ p2)) ∨ (True ∧ (True → (p2 ∨ ((False → p1) ∨ True)))))) ∨ ((p4 → p5) → (False → p5))) ∨ p5) ∧ True) := by
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
  -- False on the left can always be used.
  apply False.elim h2
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_774474175789327171387899761623 : (((False ∨ ((((p5 → (p3 ∧ p5)) ∨ ((True → False) → p4)) → ((p2 → p3) ∧ (False ∨ p3))) → ((((p1 → p2) ∨ p4) ∨ True) ∨ p5))) ∨ p5) ∧ True) := by
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
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_622031224615723820731219486793 : ((((p2 ∧ ((p2 ∧ ((((p4 ∧ (p3 ∧ p5)) ∧ (p3 ∨ p1)) ∨ ((False ∧ (p3 ∧ True)) → (p4 → p4))) ∨ (p3 ∨ p4))) ∨ p2)) ∨ p5) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_174069613548890372668321951654 : ((((p4 ∧ (p1 ∨ ((p4 → (p1 ∨ p3)) ∨ (p2 ∨ p4)))) ∧ p5) ∧ (True → True)) → ((p1 ∨ ((p2 ∧ p5) ∧ p2)) ∨ (p1 ∨ (p4 → p4)))) := by
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
  -- Disjunctions on the left can always be decomposed.
  cases h7
  case inl h8 =>
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- One of the premise coincides with the conclusion.
    exact h8
  case inr h9 =>
    -- Disjunctions on the left can always be decomposed.
    cases h9
    case inl h10 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Implications on the right can always be decomposed.
      intro h11
      -- One of the premise coincides with the conclusion.
      exact h11
    case inr h12 =>
      -- Disjunctions on the left can always be decomposed.
      cases h12
      case inl h13 =>
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- Conjunctions on the right can always be decomposed.
        apply And.intro
        -- Conjunctions on the right can always be decomposed.
        apply And.intro
        -- One of the premise coincides with the conclusion.
        exact h13
        -- One of the premise coincides with the conclusion.
        exact h5
        -- One of the premise coincides with the conclusion.
        exact h13
      case inr h14 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- Implications on the right can always be decomposed.
        intro h15
        -- One of the premise coincides with the conclusion.
        exact h15



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_191637558495706169610799482698 : ((p4 ∧ (((p2 ∨ (p4 ∧ p2)) → (p1 → p2)) → p5)) ∨ ((p1 ∨ p5) ∨ (p4 → ((((p2 ∨ (True ∨ p1)) ∧ False) → p1) ∨ (p5 ∨ p5))))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h2
  -- Conjunctions on the left can always be decomposed.
  let h3 := h2.left
  let h4 := h2.right
  -- Disjunctions on the left can always be decomposed.
  cases h3
  case inl h5 =>
    -- False on the left can always be used.
    apply False.elim h4
  case inr h6 =>
    -- Disjunctions on the left can always be decomposed.
    cases h6
    case inl h7 =>
      -- False on the left can always be used.
      apply False.elim h4
    case inr h8 =>
      -- False on the left can always be used.
      apply False.elim h4



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_696277149262557883747336476559 : ((((False → ((p1 ∧ (p3 → (((p5 ∧ p5) ∧ p3) ∧ (p5 ∧ p2)))) ∨ p3)) → ((False ∨ p4) ∧ (p3 ∨ (p3 ∧ ((p1 ∨ p5) ∧ p2))))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_53277831012602739229292816077 : (((p2 ∧ (p2 → (p4 → (((p4 ∧ p4) ∧ p5) ∧ (False ∧ p5))))) ∨ (p5 ∧ (p3 ∨ (((p1 → p2) → p4) ∨ ((p4 ∧ True) → p3))))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_639100516387444997032508886854 : ((((((True → (True → p2)) → p4) ∨ (((p1 ∨ (p2 ∨ (p5 ∧ ((False ∧ (False ∧ (p3 → p2))) ∨ True)))) ∧ (p5 → True)) ∨ p4)) → p2) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_119258516206682136948164876879 : ((p2 → (True → ((((((p4 → True) ∨ p5) ∧ (p4 ∨ ((True → p4) → p2))) ∧ p2) ∨ p2) → ((p3 ∧ p4) ∨ (True ∧ True))))) ∨ (True ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_655629715607482023436188024480 : (((((p1 → (((p4 ∧ False) ∨ (((p1 → False) → (((p3 ∨ p1) ∨ p4) ∧ p1)) → (p3 → p2))) ∧ False)) → (p1 ∨ p5)) ∨ (p4 → True)) ∨ False) ∧ True) := by
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
theorem thm_5_vars_302982300934656460737783485597 : (False ∨ (p1 → ((((((p1 → (p4 ∧ (p3 ∨ (p1 → False)))) → ((p1 ∨ False) ∨ p5)) → True) ∨ (((False ∧ False) ∧ True) ∧ p4)) → p3) ∨ p1))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_199332886016264714996130357093 : ((((((p1 ∨ p1) ∨ False) → True) → p1) ∨ False) → ((p1 ∨ (True ∧ ((p4 → p3) → (False ∧ (p1 → False))))) ∨ ((p2 ∧ (p5 ∨ p5)) → p3))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h2 =>
    -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
    have h3 : (((p1 ∨ p1) ∨ False) → True) := by
      -- Implications on the right can always be decomposed.
      intro h4
      -- True on the right can always be proven directly.
      apply True.intro
    -- We have shown the premise of h2, we can now drive its conclusion.
    let h5 := h2 h3
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- One of the premise coincides with the conclusion.
    exact h5
  case inr h6 =>
    -- False on the left can always be used.
    apply False.elim h6



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_137033097318447438270647962291 : (((p5 ∨ p1) → ((((True ∨ (p3 ∨ p1)) → (((True ∧ p3) ∨ (p3 → (p2 ∧ p3))) → p3)) ∨ True) ∨ (True → p2))) ∨ (p5 → (p2 ∧ p2))) := by
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
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_259210336474868875037016188099 : ((False → False) → (((((p1 → (p1 ∧ ((p3 → p3) ∨ (False ∨ False)))) ∧ p5) ∧ p1) ∧ p2) → (p3 ∨ (((p2 → p4) → (p2 ∧ False)) ∨ True)))) := by
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
  let h7 := h5.left
  let h8 := h5.right
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_247406375456448900263454307471 : ((False ∨ p2) ∨ (((((((p2 ∧ True) → p4) → ((p5 → p5) ∧ p5)) → ((((p5 ∧ True) ∨ False) ∧ (False → p3)) ∧ p3)) ∨ p5) ∨ True) ∨ p3)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_259617124113839414528003145655 : ((p1 → False) → ((False ∨ ((p2 ∧ (((False ∨ (p5 ∧ ((p1 ∧ p3) → (p4 ∧ p2)))) ∧ p5) → True)) → (p4 ∨ (p3 → (p3 ∧ p2))))) ∨ p4)) := by
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
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h5
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- One of the premise coincides with the conclusion.
  exact h5
  -- One of the premise coincides with the conclusion.
  exact h3



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_255211323378829940813406217339 : ((p4 ∧ p4) → (((p1 → p3) → False) ∨ ((((False ∨ p1) → ((((p5 ∧ p2) ∨ (p5 ∧ p4)) → (p1 → (p3 → p2))) ∧ False)) ∧ p5) ∨ p4))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h3



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_173326293666877477482253176985 : ((p2 → ((p4 → ((p1 ∨ p2) ∧ (p2 → (p4 ∧ (p1 ∨ False))))) → (True ∧ p1))) ∨ (((True → False) → p1) ∨ ((p2 → (p5 ∧ True)) ∨ p5))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
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
  -- False on the left can always be used.
  apply False.elim h3



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_47346750147313981055944458414 : ((((p1 → p3) ∧ (((p2 ∨ ((p3 ∧ p5) → (p1 → (p1 → (p1 → (True → (p4 ∧ p4))))))) → (p3 → p1)) ∨ True)) ∨ (p1 → p1)) ∨ p4) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_45229101035405023358533692886 : (((p1 ∧ ((((p3 ∨ ((p5 → (True ∨ p4)) ∨ (((True ∧ False) ∨ (p2 → (p1 → p1))) ∧ True))) ∨ (p1 → p1)) ∧ p1) ∨ p3)) → p5) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_259338717489441109116433225452 : ((False → p2) → (((p4 ∧ p4) → (p5 ∧ False)) ∨ ((p1 ∨ ((p3 ∧ False) ∧ p2)) ∨ (((((p1 ∧ True) → p5) ∧ p1) ∨ True) ∧ (p2 → True))))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
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
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_231764300678647186959301903873 : (((p3 ∧ p3) → False) → (((p2 ∨ ((False → p1) ∧ ((p1 ∧ p2) ∨ p4))) ∨ ((p4 → p2) ∨ (((False ∨ (p3 ∧ p5)) ∧ p5) ∨ p4))) ∨ True)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_114174024212753203787761431269 : ((((((False ∨ p2) ∨ ((p2 → p5) ∨ (False → (False → False)))) ∧ (False → (p4 ∧ p4))) ∨ (p2 → p1)) → ((p4 ∧ False) ∨ False)) ∨ (p4 → True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_221422586128071935087524986863 : (((True → p5) ∨ True) ∧ (((p2 ∨ ((p5 ∧ p3) → p2)) ∨ ((((False ∨ p4) ∨ (p5 ∨ p5)) → p3) → ((True → (False ∨ p5)) → p3))) ∨ p3)) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h3 : ((False ∨ p4) ∨ (p5 ∨ p5)) := by
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
    have h4 : True := by
      -- True on the right can always be proven directly.
      apply True.intro
    -- We have shown the premise of h2, we can now drive its conclusion.
    let h5 := h2 h4
    -- Disjunctions on the left can always be decomposed.
    cases h5
    case inl h6 =>
      -- False on the left can always be used.
      apply False.elim h6
    case inr h7 =>
      -- One of the premise coincides with the conclusion.
      exact h7
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h8 := h1 h3
  -- One of the premise coincides with the conclusion.
  exact h8



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_186907340378729198275571940507 : ((((p1 ∧ True) ∨ p4) ∧ (((p2 ∧ p5) ∧ (True → p5)) → True)) → ((((p3 → (((False ∨ p5) ∧ True) ∨ (p3 → False))) ∨ p2) → False) ∨ True)) := by
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
theorem thm_5_vars_134263581630058301241167063261 : (((((True → p2) → p2) → ((((p3 ∨ (p3 → (p2 → False))) ∧ (p2 ∨ p4)) ∨ p2) ∨ ((p4 ∧ p2) ∨ False))) ∨ p4) ∨ (p3 ∨ (True ∨ p5))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_126516614257694594257481058842 : ((p2 ∧ (p3 ∧ (((((p1 ∧ ((p1 ∨ p3) ∧ (False → (p3 ∨ p4)))) ∧ (True ∧ False)) ∨ p1) → (p3 ∧ p5)) ∧ (p3 ∨ True)))) → (p5 ∨ p2)) := by
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
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h2
  case inr h9 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_347830180976050900165577471163 : (p3 → (((p2 ∨ False) ∨ False) → ((p1 ∨ p4) ∨ ((False ∨ (((True ∨ p1) ∨ p2) → (p4 → (False ∨ p5)))) → (((False ∨ p1) ∧ False) ∨ True))))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
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
      -- Disjunctions on the left can always be decomposed.
      cases h5
      case inl h6 =>
        -- False on the left can always be used.
        apply False.elim h6
      case inr h7 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- True on the right can always be proven directly.
        apply True.intro
    case inr h8 =>
      -- False on the left can always be used.
      apply False.elim h8
  case inr h9 =>
    -- False on the left can always be used.
    apply False.elim h9



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_306361407482687177189419534236 : (p1 ∨ ((False → p4) ∧ ((False ∨ True) ∧ (((p5 → (p4 ∧ (p3 ∧ p4))) ∨ (p4 ∨ p4)) ∨ ((p5 → ((p1 ∨ (p2 → False)) ∨ p1)) ∨ True))))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h1
  -- False on the left can always be used.
  apply False.elim h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_613051266603598234957059918102 : ((((((((p4 ∨ (((p1 → (False ∧ p3)) ∨ p3) ∧ (p5 → (p2 ∨ False)))) ∨ p4) ∧ ((p1 → p4) ∧ True)) ∨ p2) → (p1 → False)) ∨ True) ∨ p2) ∧ True) := by
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
theorem thm_5_vars_190179753977870433498764671073 : (((p5 ∧ ((((p2 ∨ p3) ∨ p2) → p5) → p3)) ∧ p2) ∨ (True ∨ ((p3 ∧ (p1 ∨ (True ∧ ((p2 ∨ True) ∨ (p5 ∧ False))))) ∧ (p1 ∨ p3)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_139810598726772354533361128562 : (((p5 ∨ ((((p2 ∧ (p1 ∧ (((False ∧ False) ∧ False) ∨ p1))) → p5) ∨ (p4 → (p2 → p5))) → (p4 → False))) → False) → ((p4 → False) → p5)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h3 : (p5 ∨ ((((p2 ∧ (p1 ∧ (((False ∧ False) ∧ False) ∨ p1))) → p5) ∨ (p4 → (p2 → p5))) → (p4 → False))) := by
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h4
    -- Implications on the right can always be decomposed.
    intro h5
    -- Disjunctions on the left can always be decomposed.
    cases h4
    case inl h6 =>
      -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
      have h7 : p4 := by
        -- One of the premise coincides with the conclusion.
        exact h5
      -- We have shown the premise of h2, we can now drive its conclusion.
      let h8 := h2 h7
      -- False on the left can always be used.
      apply False.elim h8
    case inr h9 =>
      -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
      have h10 : p4 := by
        -- One of the premise coincides with the conclusion.
        exact h5
      -- We have shown the premise of h2, we can now drive its conclusion.
      let h11 := h2 h10
      -- False on the left can always be used.
      apply False.elim h11
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h12 := h1 h3
  -- False on the left can always be used.
  apply False.elim h12



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_116090056897370458014818530653 : ((((p3 ∨ p1) ∨ True) ∧ (p5 ∨ ((p1 ∨ (p3 → (p2 ∧ (((p4 ∨ False) → p1) ∧ True)))) ∨ (p3 → ((True → p1) → p1))))) ∨ (False ∨ p2)) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
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
  -- One of the premise coincides with the conclusion.
  exact h4



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_322285579046565925774522643377 : (p5 ∨ ((((p2 ∨ (((p2 ∧ p5) ∨ (p4 ∧ p5)) ∧ ((False ∧ p4) ∨ ((False → p2) ∨ ((p5 ∧ False) ∧ (False → p5)))))) → p2) → p5) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_810748211501851434976715367761 : (((p5 → ((p5 ∨ (p5 ∧ p1)) → (((p5 → p5) → ((p3 → (False → (p2 → (False ∨ False)))) → (p5 ∧ p3))) ∧ ((p1 ∧ p2) ∧ p4)))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_550527480789803931763452853827 : (((p1 ∨ (((p3 → (p2 → p1)) ∨ (((((p3 → p5) ∨ p1) ∨ (p3 ∧ (True ∨ False))) ∨ (p4 → (p4 ∧ p2))) ∨ p3)) ∨ (False → p4))) ∧ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
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
theorem thm_5_vars_264841797252230414369773847371 : (True ∧ ((p2 ∨ p1) ∨ (p3 → (((p1 → False) ∨ False) → (p4 ∨ ((p1 ∨ p2) ∨ (True ∨ (((p4 → p5) ∧ ((p5 ∨ p5) ∨ p3)) ∨ p3)))))))) := by
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
  -- Disjunctions on the left can always be decomposed.
  cases h2
  case inl h3 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- True on the right can always be proven directly.
    apply True.intro
  case inr h4 =>
    -- False on the left can always be used.
    apply False.elim h4



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_168104154485297327827293571237 : ((((p3 → True) → (p2 → p1)) ∨ (False ∨ (p2 → (p4 → ((True ∨ p2) → (p3 ∨ False)))))) → (((True → (False ∨ p5)) → p2) ∨ (False → p2))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h2 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h3
    -- False on the left can always be used.
    apply False.elim h3
  case inr h4 =>
    -- Disjunctions on the left can always be decomposed.
    cases h4
    case inl h5 =>
      -- False on the left can always be used.
      apply False.elim h5
    case inr h6 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Implications on the right can always be decomposed.
      intro h7
      -- False on the left can always be used.
      apply False.elim h7



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_299087916529555497798194312355 : (False ∨ ((((p1 ∨ (p3 → ((p3 ∨ True) ∧ (p4 ∨ ((((True → (p5 ∨ True)) ∧ ((False ∨ p3) ∨ p4)) → p5) ∧ False))))) ∨ p4) ∧ p2) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_54855132548217526397076976205 : ((((((p5 → p1) ∨ p4) → p1) ∧ p3) ∧ (((True ∧ (((True ∧ (p1 ∨ ((p2 ∧ p5) ∨ p2))) → p5) ∧ (p2 → p5))) → p2) ∨ p1)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_733238795714893468095696645926 : ((((p3 ∧ p3) ∧ (((((p1 ∧ ((p4 ∨ (True ∨ False)) ∧ (p5 → p2))) ∧ p3) → False) → (p3 ∧ (p2 → False))) ∧ ((p1 → p5) → p2))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_61917607257233019781697480902 : ((p2 ∧ ((p4 ∧ (((p5 ∧ (p4 ∨ p1)) → (p3 ∨ p5)) ∧ (p1 ∧ (p4 → (False ∨ ((p4 → p2) → p1)))))) ∨ (p2 ∨ (p2 ∨ p1)))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_59274253961412846292282894197 : (((p3 ∨ p1) ∨ ((((p4 ∨ p3) ∧ p3) ∨ p5) ∨ ((True ∧ (p2 ∧ (True → (p3 ∧ (((p1 ∧ False) ∧ False) ∨ (True → p5)))))) → p2))) ∨ p5) := by
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
  let h4 := h3.left
  let h5 := h3.right
  -- One of the premise coincides with the conclusion.
  exact h4



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_214160745807351755132545471513 : ((((p2 ∧ p2) → p4) → p3) ∨ ((((p3 ∧ True) → True) ∧ (p1 ∨ False)) ∨ (True ∨ ((p2 ∨ ((False ∨ p5) ∧ (p1 ∨ p3))) → (p2 ∧ p5))))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_60115078767682936014992820954 : (((p3 ∨ p4) → (((((p4 → ((p5 ∧ (p3 → (True ∧ True))) ∨ ((p2 → True) → p3))) → p3) ∧ ((p3 ∨ p3) ∧ p5)) ∨ True) ∨ p4)) ∨ p2) := by
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
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h3



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_707321549310314819521425089130 : ((((((p3 ∨ False) ∧ (p5 → p2)) ∨ (p3 ∨ False)) ∨ ((p1 ∨ (p1 → (True ∨ False))) ∧ ((p2 ∨ (((False ∧ p3) → p4) → p2)) → p2))) ∨ False) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro
  -- Implications on the right can always be decomposed.
  intro h2
  -- Disjunctions on the left can always be decomposed.
  cases h2
  case inl h3 =>
    -- One of the premise coincides with the conclusion.
    exact h3
  case inr h4 =>
    -- We want to use the implication h4 based on <expert-advice>. So we show its premise.
    have h5 : ((False ∧ p3) → p4) := by
      -- Implications on the right can always be decomposed.
      intro h6
      -- Conjunctions on the left can always be decomposed.
      let h7 := h6.left
      let h8 := h6.right
      -- False on the left can always be used.
      apply False.elim h7
    -- We have shown the premise of h4, we can now drive its conclusion.
    let h9 := h4 h5
    -- One of the premise coincides with the conclusion.
    exact h9
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_156696766468603603644146764726 : (((((p4 ∧ False) ∨ (((((False ∨ p5) → p5) → p5) → False) ∨ True)) ∨ (p1 ∧ (p3 → p2))) ∧ p5) ∨ ((True ∨ ((p2 ∧ p1) → p3)) → True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_606687373616169877536436895565 : (((((((p5 → (False ∧ True)) → (((((p2 → (p5 ∨ False)) ∨ p1) ∧ (p4 ∨ (p2 → p4))) ∨ False) ∨ p4)) ∧ (p5 → False)) ∧ p1) ∨ True) ∨ p5) ∧ True) := by
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
theorem thm_5_vars_660397309679508979552964916332 : (((((p1 → (p1 ∧ (((((((False → p4) ∨ False) → (False ∧ p3)) ∧ p5) ∧ ((p4 ∧ False) ∨ p5)) ∨ p3) ∨ p3))) ∨ p4) → (p1 → p2)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_180430707740528243171975348037 : ((((False ∧ (p4 ∨ ((p1 → p4) ∧ (p4 ∨ False)))) → p2) → (p5 ∧ False)) → (((((p5 ∧ True) ∨ p5) ∧ p1) → ((p3 ∧ p4) → False)) ∨ False)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h2 : ((False ∧ (p4 ∨ ((p1 → p4) ∧ (p4 ∨ False)))) → p2) := by
    -- Implications on the right can always be decomposed.
    intro h3
    -- Conjunctions on the left can always be decomposed.
    let h4 := h3.left
    let h5 := h3.right
    -- False on the left can always be used.
    apply False.elim h4
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h6 := h1 h2
  -- We need to get the right conjuct of h6 based on <expert-advice>.
  let h7 := h6.right
  -- False on the left can always be used.
  apply False.elim h7



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_658006779364867736198013020241 : ((((p2 ∧ (((p5 → True) → p5) ∨ (p3 ∧ ((p4 → False) ∧ (p4 ∨ ((p3 ∧ (((p1 → p3) ∧ p5) → False)) → p2)))))) ∨ (p4 → p4)) ∨ p4) ∧ True) := by
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
theorem thm_5_vars_606180639795174908898146322386 : ((((((((((((p2 → p1) → p3) ∧ p4) ∨ (p4 ∨ ((False ∨ p2) ∨ True))) ∧ p1) ∧ False) ∧ (p2 → (p1 ∧ p2))) ∧ False) ∧ p3) ∨ True) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_149020815843818401098794465775 : ((((p5 → p3) ∨ p4) ∨ ((p3 → p4) → ((((False ∧ p2) ∨ (p2 ∨ p2)) ∨ False) ∨ (p4 → (False ∧ p3))))) ∨ (False → ((p5 ∨ p1) ∨ p4))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_301416785836946220835901999798 : (False ∨ (((p5 → (True → p5)) ∨ p4) → (((((True ∨ ((p5 ∧ p5) → ((p5 ∧ True) → p1))) → p5) → p2) ∨ False) ∨ ((p3 ∨ True) ∨ p4)))) := by
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
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h3



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_231623166887402171583227394106 : (((False ∧ True) → True) → (((((p1 ∨ (p5 → p2)) ∧ (True → True)) ∨ p2) ∧ ((p4 → p5) → p3)) ∨ ((p3 → p3) → (True ∧ (True ∧ True))))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h2
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



