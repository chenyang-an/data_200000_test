variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_650399259938219968041871225255 : (((((False ∨ (((p5 → True) → (((p3 → False) → (p5 ∧ p3)) → p4)) → p4)) ∨ (((p3 ∧ False) → True) ∨ (p1 → False))) ∧ (p2 → False)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_135857390040496313308780735173 : ((((((p2 ∧ (p4 ∨ False)) ∨ p4) ∨ (p4 ∧ (False ∨ p2))) ∨ True) ∨ (p1 ∧ ((p2 → (p3 ∧ False)) → (False ∨ p4)))) ∨ (p1 ∧ (False ∧ False))) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_173390419570477907342456777096 : ((p4 → ((False ∨ (p5 → (p4 ∧ False))) ∨ (((p5 ∧ True) ∧ (True → p3)) ∧ p4))) ∨ ((((p5 ∧ p5) ∧ (p5 ∨ (p3 → p5))) ∨ False) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_42069327313697909460002537770 : ((((True → p1) ∨ (((p5 → False) ∧ False) ∧ (p4 ∨ (p3 ∧ (p4 → (((p1 → p3) → False) ∧ (p2 → (False ∧ (p5 → p5))))))))) ∨ p3) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_190021142102179794234522142134 : (((((False ∨ True) → ((p1 ∨ p5) → False)) ∧ p4) ∧ p4) ∨ (((p4 → (((p5 ∨ (True ∨ p3)) ∨ False) → True)) ∨ p4) ∧ (True ∧ (False ∨ True)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- True on the right can always be proven directly.
  apply True.intro
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_341760564236220817421860323795 : (p2 → ((p3 ∨ (p3 ∨ (p2 → (False ∧ (((p4 → p4) → (False ∨ p5)) ∧ (p3 ∧ ((p4 ∧ p4) ∧ (p1 → (False ∧ p1))))))))) ∨ (p3 ∨ p2))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_705592505689155377333227351675 : (((((p4 ∧ (((False ∧ False) → False) ∧ p4)) → False) ∧ (p1 ∧ (True → (p5 ∨ ((((p4 ∧ (p3 ∧ p4)) ∧ p4) ∧ p5) ∧ (True → p3)))))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_50382017306946411320914295958 : ((((False → p4) ∧ (((p1 ∧ (p5 → p3)) → ((p4 → (p1 ∧ p3)) ∧ ((p3 ∨ p5) → p5))) ∧ p2)) ∨ (p2 → ((p2 → p5) ∨ p2))) ∨ p5) := by
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
theorem thm_5_vars_249581060012433687623149325345 : ((p5 ∨ p2) ∨ (True → ((False ∧ (((p4 ∨ p5) → (((p2 → (p1 ∧ False)) ∨ (p4 → p1)) → (p5 ∨ True))) → (p2 ∧ p1))) ∨ (p5 ∨ True)))) := by
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
theorem thm_5_vars_217607414718099025282580898341 : ((((p2 → p4) ∨ True) → p3) → (((p4 → p5) ∧ (p2 ∨ ((True ∧ True) → (p4 ∨ (((False ∧ p4) → (False → (True ∨ p5))) → p1))))) → p3)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Conjunctions on the left can always be decomposed.
  let h3 := h2.left
  let h4 := h2.right
  -- Disjunctions on the left can always be decomposed.
  cases h4
  case inl h5 =>
    -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
    have h6 : ((p2 → p4) ∨ True) := by
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- True on the right can always be proven directly.
      apply True.intro
    -- We have shown the premise of h1, we can now drive its conclusion.
    let h7 := h1 h6
    -- One of the premise coincides with the conclusion.
    exact h7
  case inr h8 =>
    -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
    have h9 : ((p2 → p4) ∨ True) := by
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- True on the right can always be proven directly.
      apply True.intro
    -- We have shown the premise of h1, we can now drive its conclusion.
    let h10 := h1 h9
    -- One of the premise coincides with the conclusion.
    exact h10



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_183824566161746762963676595637 : (((((p3 → (p1 ∧ p4)) → (True ∧ (p2 ∧ p2))) → False) ∧ True) ∨ ((False ∨ ((p1 ∨ p1) → p1)) ∧ (p4 → (((p2 ∨ False) → p4) → True)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
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
    -- One of the premise coincides with the conclusion.
    exact h3
  -- Implications on the right can always be decomposed.
  intro h4
  -- Implications on the right can always be decomposed.
  intro h5
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_110726138157492962725818357643 : (((((p4 ∨ ((((p2 → ((p5 ∨ p1) ∨ p2)) → (p1 → p2)) ∨ True) → (p1 ∨ p4))) ∨ (True → (True ∧ p3))) ∧ p2) ∧ p2) ∨ (p4 ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_60924782980148671553539870944 : ((False ∧ ((((False ∨ (True → False)) ∧ ((p4 ∨ p4) ∧ (p3 ∨ p5))) ∨ (((p3 ∨ ((False ∨ False) ∧ True)) ∧ p1) ∧ (p3 ∨ p1))) ∧ p3)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_254143525556270548646526496488 : ((p2 ∧ p1) → ((((p5 ∨ p5) → (p4 ∨ (((((p4 ∨ p1) ∧ (True ∨ p3)) ∧ p2) → p4) → p3))) ∨ (p3 ∨ (p2 ∨ (p3 ∨ p2)))) ∧ True)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- One of the premise coincides with the conclusion.
  exact h2
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_232501369928300110516139619493 : ((True ∧ (p1 → False)) → ((p3 → False) ∨ ((((((p4 ∨ True) ∧ p5) ∧ (p3 ∧ (p4 ∨ ((p4 ∧ False) → True)))) ∨ p4) ∨ True) ∨ (p1 → p1)))) := by
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
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_172302006790216876396994260129 : ((((False → (p4 ∨ (p1 ∧ p4))) ∨ (p3 ∨ p5)) → (((False → p3) ∧ p5) ∧ True)) ∨ (True ∨ ((((p1 ∧ p4) → p5) ∨ False) ∧ (p4 ∧ p3)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_652428129397648675002473661252 : ((((p5 ∧ ((p3 ∧ ((((((p4 ∧ p3) ∧ p1) → p3) ∨ p2) → (((p5 ∨ False) ∧ True) ∨ False)) ∨ p5)) ∧ (p5 → p1))) ∧ (p1 → False)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_45686939758585815487321909105 : (((p5 ∨ (True ∧ ((p3 ∨ (p4 ∧ (True → True))) → (((p2 ∧ ((p1 → False) ∧ p2)) ∨ False) ∨ (p3 → (p1 ∧ (p1 ∨ p1))))))) → p3) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_263553291197160689827363951594 : (True ∧ (((((False ∧ p5) → (p5 → False)) → (((p5 ∨ p4) ∨ (p5 ∨ (p2 → (p3 ∨ p5)))) ∨ p2)) ∨ p4) ∨ ((p4 → (False → False)) ∨ p1))) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- True on the right can always be proven directly.
  apply True.intro
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
theorem thm_5_vars_204477047843254568571900386549 : (((((p5 ∨ p5) ∧ p4) ∨ p4) ∨ False) ∨ ((p5 ∧ True) ∨ (((False ∨ False) ∧ p5) → (((p4 ∧ (p5 ∧ p5)) → ((p2 → p1) ∨ p2)) ∧ p5)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
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
  -- Conjunctions on the left can always be decomposed.
  let h5 := h4.left
  let h6 := h4.right
  -- Conjunctions on the left can always be decomposed.
  let h7 := h1.left
  let h8 := h1.right
  -- Disjunctions on the left can always be decomposed.
  cases h7
  case inl h9 =>
    -- False on the left can always be used.
    apply False.elim h9
  case inr h10 =>
    -- False on the left can always be used.
    apply False.elim h10
  -- Conjunctions on the left can always be decomposed.
  let h11 := h1.left
  let h12 := h1.right
  -- Disjunctions on the left can always be decomposed.
  cases h11
  case inl h13 =>
    -- False on the left can always be used.
    apply False.elim h13
  case inr h14 =>
    -- False on the left can always be used.
    apply False.elim h14



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_343846982318569064857389563970 : (p2 → (p2 ∧ (p4 ∨ ((False ∨ (p1 ∨ ((((((p1 ∧ (p2 → p5)) ∨ True) ∧ ((p5 → True) → p2)) ∨ (p2 → p5)) → p1) ∨ True))) ∨ False)))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- One of the premise coincides with the conclusion.
  exact h1
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
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_194164137963559427088149314018 : ((p2 → ((((p5 → (p3 ∧ False)) → p5) ∧ True) ∨ False)) → (p1 → (p5 ∨ (True → ((((((p5 → p2) ∨ False) → p2) ∧ p5) → False) ∨ p1))))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h3
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_49569940400707275890249636998 : (((((((p3 ∧ p2) ∧ (p4 ∧ p5)) → (p3 → ((p2 ∧ p4) ∨ p5))) → False) ∧ (((p4 ∧ p3) → p4) → p3)) → ((p5 ∧ p4) ∧ p2)) ∨ p3) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
  have h4 : (((p3 ∧ p2) ∧ (p4 ∧ p5)) → (p3 → ((p2 ∧ p4) ∨ p5))) := by
    -- Implications on the right can always be decomposed.
    intro h5
    -- Implications on the right can always be decomposed.
    intro h6
    -- Conjunctions on the left can always be decomposed.
    let h7 := h5.left
    let h8 := h5.right
    -- Conjunctions on the left can always be decomposed.
    let h9 := h7.left
    let h10 := h7.right
    -- Conjunctions on the left can always be decomposed.
    let h11 := h8.left
    let h12 := h8.right
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h12
  -- We have shown the premise of h2, we can now drive its conclusion.
  let h13 := h2 h4
  -- False on the left can always be used.
  apply False.elim h13
  -- Conjunctions on the left can always be decomposed.
  let h14 := h1.left
  let h15 := h1.right
  -- We want to use the implication h14 based on <expert-advice>. So we show its premise.
  have h16 : (((p3 ∧ p2) ∧ (p4 ∧ p5)) → (p3 → ((p2 ∧ p4) ∨ p5))) := by
    -- Implications on the right can always be decomposed.
    intro h17
    -- Implications on the right can always be decomposed.
    intro h18
    -- Conjunctions on the left can always be decomposed.
    let h19 := h17.left
    let h20 := h17.right
    -- Conjunctions on the left can always be decomposed.
    let h21 := h19.left
    let h22 := h19.right
    -- Conjunctions on the left can always be decomposed.
    let h23 := h20.left
    let h24 := h20.right
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h24
  -- We have shown the premise of h14, we can now drive its conclusion.
  let h25 := h14 h16
  -- False on the left can always be used.
  apply False.elim h25
  -- Conjunctions on the left can always be decomposed.
  let h26 := h1.left
  let h27 := h1.right
  -- We want to use the implication h26 based on <expert-advice>. So we show its premise.
  have h28 : (((p3 ∧ p2) ∧ (p4 ∧ p5)) → (p3 → ((p2 ∧ p4) ∨ p5))) := by
    -- Implications on the right can always be decomposed.
    intro h29
    -- Implications on the right can always be decomposed.
    intro h30
    -- Conjunctions on the left can always be decomposed.
    let h31 := h29.left
    let h32 := h29.right
    -- Conjunctions on the left can always be decomposed.
    let h33 := h31.left
    let h34 := h31.right
    -- Conjunctions on the left can always be decomposed.
    let h35 := h32.left
    let h36 := h32.right
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h36
  -- We have shown the premise of h26, we can now drive its conclusion.
  let h37 := h26 h28
  -- False on the left can always be used.
  apply False.elim h37



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_318891362549122558847742603419 : (p4 ∨ ((True ∧ (((((p3 → ((p3 ∨ (p3 ∧ (p1 → p5))) → p5)) ∨ False) ∨ (p5 ∨ (True ∧ False))) → p2) ∧ p5)) ∨ (True → (p3 → p3)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- One of the premise coincides with the conclusion.
  exact h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_191457776733352277978919218219 : (((p3 → p3) → (((p5 ∧ p4) → True) → (p2 ∨ p4))) ∨ (((((p2 → (True ∨ p1)) → ((p2 ∧ p1) → (p2 ∨ True))) ∨ p1) ∧ False) → p5)) := by
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
    -- False on the left can always be used.
    apply False.elim h3
  case inr h5 =>
    -- False on the left can always be used.
    apply False.elim h3



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_723358278765648822674997241959 : (((((False ∧ p1) → p1) ∧ ((p3 ∧ ((p1 ∧ ((p5 ∧ ((p1 ∨ p5) ∧ (True → ((p3 ∨ p5) → False)))) → p2)) ∨ (p5 → p3))) ∧ p4)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_712340364712277971077389375702 : (((((True → (True ∧ (p5 → True))) → p1) ∨ ((((p5 ∨ (((p5 ∧ p4) ∨ p2) ∧ (p1 ∨ p3))) ∧ p5) → p3) ∨ (False ∨ (p1 → p1)))) ∨ p3) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
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
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_871994412595803445952884931428 : ((((p4 ∨ (((p3 ∧ p1) ∨ p5) ∨ ((p2 → p2) ∨ ((((p3 → True) → (((True → p3) → p4) ∧ (p1 ∨ p1))) ∧ p3) → p5)))) → p5) → p5) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h1
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h2 : (p4 ∨ (((p3 ∧ p1) ∨ p5) ∨ ((p2 → p2) ∨ ((((p3 → True) → (((True → p3) → p4) ∧ (p1 ∨ p1))) ∧ p3) → p5)))) := by
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Implications on the right can always be decomposed.
    intro h3
    -- One of the premise coincides with the conclusion.
    exact h3
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h4 := h1 h2
  -- One of the premise coincides with the conclusion.
  exact h4
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_229512234630795876133337359598 : ((p2 → (p1 ∨ p3)) ∨ (((p2 → p2) → p3) → ((p1 ∧ ((p4 ∧ (((p3 → p1) ∨ p5) → (p5 ∧ p3))) ∧ (p1 ∨ (p5 ∨ True)))) → p5))) := by
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
  let h7 := h5.left
  let h8 := h5.right
  -- Disjunctions on the left can always be decomposed.
  cases h6
  case inl h9 =>
    -- We want to use the implication h8 based on <expert-advice>. So we show its premise.
    have h10 : ((p3 → p1) ∨ p5) := by
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- Implications on the right can always be decomposed.
      intro h11
      -- One of the premise coincides with the conclusion.
      exact h9
    -- We have shown the premise of h8, we can now drive its conclusion.
    let h12 := h8 h10
    -- We need to get the left conjuct of h12 based on <expert-advice>.
    let h13 := h12.left
    -- One of the premise coincides with the conclusion.
    exact h13
  case inr h14 =>
    -- Disjunctions on the left can always be decomposed.
    cases h14
    case inl h15 =>
      -- One of the premise coincides with the conclusion.
      exact h15
    case inr h16 =>
      -- We want to use the implication h8 based on <expert-advice>. So we show its premise.
      have h17 : ((p3 → p1) ∨ p5) := by
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- Implications on the right can always be decomposed.
        intro h18
        -- One of the premise coincides with the conclusion.
        exact h3
      -- We have shown the premise of h8, we can now drive its conclusion.
      let h19 := h8 h17
      -- We need to get the left conjuct of h19 based on <expert-advice>.
      let h20 := h19.left
      -- One of the premise coincides with the conclusion.
      exact h20



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_670844907912214789126465142526 : ((((p2 ∧ ((((p5 ∧ p3) ∧ (True ∧ (p3 ∧ ((p1 → p1) ∧ ((True ∨ p2) ∨ p3))))) ∧ p4) → (p3 ∧ p2))) ∨ (True ∨ (p2 ∧ True))) ∨ p4) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_112059523576084950713422429428 : ((((True ∨ True) ∧ ((((False ∨ (p1 ∧ (p3 ∨ False))) ∨ (p1 ∧ True)) ∧ p5) ∨ ((p2 ∧ p2) ∨ ((p3 ∨ p4) → p5)))) ∨ p4) ∨ (p2 → True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_111640855768821181595030929359 : (((((p4 ∨ (((p1 ∧ p1) ∧ p1) ∨ p4)) ∧ ((p5 → ((p4 → p3) ∨ (((p5 ∨ False) → p5) ∧ p4))) ∧ True)) ∨ p5) ∨ p3) ∨ (True ∨ p3)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_49368092538732467101078836263 : (((p4 → ((((((p1 → (True ∧ p2)) ∨ (p5 ∧ ((p1 ∨ False) → p5))) → False) ∧ p1) ∧ p1) ∧ (False ∧ p5))) ∨ (p4 → (p3 ∨ True))) ∨ p1) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_166532091649517726505216542006 : ((p4 ∨ (p5 ∨ ((((p2 ∨ p4) ∨ (((p1 ∧ p2) → p3) ∨ p4)) → (p1 ∨ p4)) → p4))) ∨ ((((False → p5) → (p2 → p2)) ∨ p1) ∧ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
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
theorem thm_5_vars_192866969379843523294633585412 : ((((False → (True → p3)) → (False → p4)) ∧ (p3 ∨ p2)) → (((((p1 → p2) ∨ ((True ∨ (p1 ∧ p3)) ∧ p5)) → p3) ∧ (p1 ∧ p1)) ∨ True)) := by
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
    -- True on the right can always be proven directly.
    apply True.intro
  case inr h5 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_116705060459573242933103568741 : (((p1 ∧ False) ∨ ((p2 ∨ p2) ∧ ((p4 → p3) ∨ (p3 → (p5 ∨ (p1 ∨ (((((False ∨ True) → p1) ∧ True) → True) → p5))))))) ∨ (p3 ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_751684394292568210638437574203 : (((True ∧ (p4 ∧ (((True ∨ ((p3 ∨ (p2 ∨ p2)) ∨ (p5 ∨ True))) → ((True → p1) ∧ ((p5 → True) → p4))) ∨ ((False → p5) ∧ False)))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_353551061511055593833797307079 : (p4 → (p3 ∨ ((((p4 ∨ (False ∧ ((False ∧ ((p5 → p5) ∨ p3)) ∧ p4))) ∨ p2) ∨ (p1 → (p2 ∧ p2))) → ((p3 ∨ (p3 ∧ p4)) ∨ p4)))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h2
  -- Disjunctions on the left can always be decomposed.
  cases h2
  case inl h3 =>
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
        -- Conjunctions on the left can always be decomposed.
        let h7 := h6.left
        let h8 := h6.right
        -- False on the left can always be used.
        apply False.elim h7
    case inr h9 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- One of the premise coincides with the conclusion.
      exact h1
  case inr h10 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_702456891227224533618896121927 : (((((p2 ∨ (p2 → (p1 ∧ ((False → p2) ∨ p1)))) ∨ p3) ∨ (True → (True ∧ ((p2 ∧ p1) → (((p3 → False) ∧ (p4 → p3)) ∧ True))))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_68717359965774948234738015795 : ((p4 → (((p1 ∨ ((((False → p3) → p4) ∧ (False ∨ False)) ∨ False)) ∨ (((False ∧ p3) → (p2 ∨ False)) → p1)) ∨ (p2 ∨ (True ∨ p5)))) ∨ p3) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_316731353739292910786011278845 : (p3 ∨ (True → (((p2 ∧ ((p4 ∨ (((True → p1) ∧ (p1 → False)) ∧ p4)) ∨ p1)) ∧ (False ∨ (False ∧ (True ∧ ((p5 ∨ True) ∨ p5))))) ∨ True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_248988225466225645153389877552 : ((p4 ∨ False) ∨ (((True ∧ (p3 ∨ p5)) ∨ ((p1 ∨ p4) → ((p4 ∨ (False ∨ False)) → (p2 → ((False ∨ (p4 ∧ (p2 ∧ p2))) ∨ True))))) ∨ p2)) := by
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
  -- Implications on the right can always be decomposed.
  intro h3
  -- Disjunctions on the left can always be decomposed.
  cases h2
  case inl h4 =>
    -- Disjunctions on the left can always be decomposed.
    cases h1
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
    -- Disjunctions on the left can always be decomposed.
    cases h7
    case inl h8 =>
      -- False on the left can always be used.
      apply False.elim h8
    case inr h9 =>
      -- False on the left can always be used.
      apply False.elim h9



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_342569085826045742635050428743 : (p2 → (((False → ((p3 ∧ p4) → (p4 ∧ (True ∧ (False ∨ p1))))) → p1) ∨ (p3 → (p2 → ((((False ∧ p3) ∧ p2) → p4) ∧ (True ∨ p1)))))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h2
  -- Implications on the right can always be decomposed.
  intro h3
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h4
  -- Conjunctions on the left can always be decomposed.
  let h5 := h4.left
  let h6 := h4.right
  -- Conjunctions on the left can always be decomposed.
  let h7 := h5.left
  let h8 := h5.right
  -- False on the left can always be used.
  apply False.elim h7
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_315910939489164784732536715727 : (p3 ∨ (True ∧ ((p4 ∨ (p2 ∨ p5)) ∨ (((((((True ∧ (p5 ∨ p4)) → p4) ∨ p2) → True) ∧ ((True ∧ p1) → False)) ∧ p5) ∨ (p5 ∨ True))))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
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
theorem thm_5_vars_192055173551529810596463570623 : ((p3 → ((((p4 ∨ (p3 ∧ p5)) → True) → p2) ∨ p4)) ∨ (((True ∧ p5) ∧ p3) ∨ (p4 ∨ ((False ∧ (((p5 ∧ p3) ∨ p2) ∧ p4)) → False)))) := by
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
  -- False on the left can always be used.
  apply False.elim h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_613053831320586732883092144894 : ((((((((True ∧ ((p4 ∧ ((p2 ∧ False) → p3)) ∨ p2)) → (p1 → p1)) ∧ (((p5 ∧ False) ∨ p5) ∧ p3)) ∨ p2) → (True ∧ p1)) ∨ True) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_59046911126360835512176854995 : (((p4 ∧ p3) ∨ ((((p3 ∧ (p5 → p2)) ∨ False) ∧ ((p5 → p5) ∨ (p4 ∨ ((((p2 ∧ p2) → p3) ∨ (p4 ∧ p2)) → p3)))) ∨ p3)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_201756492541633059415431642404 : ((((p1 ∨ (p5 ∧ p1)) ∨ p4) ∨ True) ∧ ((p5 → (((p4 ∧ True) ∧ (p5 ∨ p1)) → (True ∧ p3))) → ((False ∨ ((True ∨ False) ∨ p3)) ∨ p3))) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- Implications on the right can always be decomposed.
  intro h1
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
theorem thm_5_vars_324938535201540774565036858342 : (p5 ∨ ((p1 ∨ p5) ∨ ((True → ((p1 ∧ (p1 ∨ p3)) ∨ (((True ∨ p3) ∨ (((p4 → p1) → False) → True)) → True))) ∨ ((p5 → p2) → False)))) := by
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
  -- Implications on the right can always be decomposed.
  intro h2
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_135857656007999631950004021414 : (((((p3 ∨ (p1 ∨ p1)) ∧ (((p3 → p5) ∨ p5) → p4)) ∨ True) ∨ (False ∧ ((p1 → ((p5 ∨ False) ∧ p5)) ∧ True))) ∨ ((p1 ∧ p5) ∧ p5)) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_793924739584610725612268043793 : (((True → (p5 → ((((((False ∧ p3) → ((p5 → ((p5 ∨ False) → p2)) ∧ (True → p2))) ∧ (p3 ∨ (p2 ∨ p2))) ∧ p3) → False) ∨ p5))) ∨ p5) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h2
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_177483646694312298272087684486 : ((p1 → ((p5 ∧ ((True ∧ ((True ∨ (True ∨ p4)) ∨ p4)) ∨ p2)) ∨ True)) ∧ ((p3 ∨ (p5 ∧ (False ∨ (False ∧ p3)))) ∨ (True → (True ∨ p5)))) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h2
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_780024453174784871766592888631 : (((p2 ∨ (((p2 ∧ ((p2 → p5) ∧ ((p5 ∧ p5) ∨ p3))) ∨ ((False ∨ (False ∨ ((p4 ∧ False) ∨ False))) ∨ (p5 ∧ p1))) ∨ (p5 ∨ True))) ∨ p2) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
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
theorem thm_5_vars_2280985719176312224523954716 : (((((p5 → p2) ∧ (p1 ∧ (p2 ∧ p3))) ∧ p2) ∧ (p3 ∨ (p5 ∨ p3))) ∨ ((p1 ∨ ((p5 → (p3 ∧ True)) ∨ (p4 → p4))) ∨ p5)) := by
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
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_190462181532985483612705814607 : (((((p4 ∧ ((p2 → False) ∨ True)) ∧ p2) ∧ p1) → p3) ∨ ((p5 ∨ ((p4 ∨ (p4 ∧ (p4 ∨ False))) ∧ (p3 → (p5 ∧ (p3 ∨ True))))) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_233760162183169614706173442046 : ((p3 ∨ (p1 ∨ True)) → ((p5 ∨ p5) → ((p3 ∧ p2) ∨ (p3 → (p2 → (True → ((True → p5) ∨ (False → ((p3 → False) ∨ (True ∧ False)))))))))) := by
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
      -- Implications on the right can always be decomposed.
      intro h5
      -- Implications on the right can always be decomposed.
      intro h6
      -- Implications on the right can always be decomposed.
      intro h7
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Implications on the right can always be decomposed.
      intro h8
      -- False on the left can always be used.
      apply False.elim h8
    case inr h9 =>
      -- Disjunctions on the left can always be decomposed.
      cases h9
      case inl h10 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- Implications on the right can always be decomposed.
        intro h11
        -- Implications on the right can always be decomposed.
        intro h12
        -- Implications on the right can always be decomposed.
        intro h13
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- Implications on the right can always be decomposed.
        intro h14
        -- False on the left can always be used.
        apply False.elim h14
      case inr h15 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- Implications on the right can always be decomposed.
        intro h16
        -- Implications on the right can always be decomposed.
        intro h17
        -- Implications on the right can always be decomposed.
        intro h18
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- Implications on the right can always be decomposed.
        intro h19
        -- False on the left can always be used.
        apply False.elim h19
  case inr h20 =>
    -- Disjunctions on the left can always be decomposed.
    cases h1
    case inl h21 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Implications on the right can always be decomposed.
      intro h22
      -- Implications on the right can always be decomposed.
      intro h23
      -- Implications on the right can always be decomposed.
      intro h24
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Implications on the right can always be decomposed.
      intro h25
      -- False on the left can always be used.
      apply False.elim h25
    case inr h26 =>
      -- Disjunctions on the left can always be decomposed.
      cases h26
      case inl h27 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- Implications on the right can always be decomposed.
        intro h28
        -- Implications on the right can always be decomposed.
        intro h29
        -- Implications on the right can always be decomposed.
        intro h30
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- Implications on the right can always be decomposed.
        intro h31
        -- False on the left can always be used.
        apply False.elim h31
      case inr h32 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- Implications on the right can always be decomposed.
        intro h33
        -- Implications on the right can always be decomposed.
        intro h34
        -- Implications on the right can always be decomposed.
        intro h35
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- Implications on the right can always be decomposed.
        intro h36
        -- False on the left can always be used.
        apply False.elim h36



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_179037798557129242684008739296 : (((True → False) → (p1 ∨ ((False ∨ ((False ∧ p1) ∨ p1)) ∨ (p1 ∧ False)))) ∨ ((False ∨ ((p2 ∧ (True ∨ True)) → p3)) ∧ ((True ∧ p3) ∧ p3))) := by
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
theorem thm_5_vars_45737927545223545014045720351 : (((False → ((((p4 ∧ p1) ∧ (((p1 → ((p5 ∨ ((p5 ∨ (p5 ∧ p2)) → p2)) → p1)) → p4) → (p1 ∨ False))) → True) ∧ p4)) → p4) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_350067591579759634113103427226 : (p4 → (((((((p3 ∨ (p2 ∧ False)) → True) ∨ (p1 ∧ False)) ∨ (p3 ∨ (p1 → ((p4 → p2) ∨ p4)))) → (p5 ∧ p3)) ∨ (p5 → p5)) ∨ p5)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h2
  -- One of the premise coincides with the conclusion.
  exact h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_259703563449036269616617451712 : ((p1 → p1) → ((((p4 → p4) ∧ p3) → p1) → ((p4 ∨ (p2 ∨ ((((((p1 → p2) ∧ True) → p3) ∧ p5) ∨ True) ∨ p3))) ∨ (False → p5)))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h3
  -- False on the left can always be used.
  apply False.elim h3



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_51468805030252144783814392587 : ((((((p3 ∨ p5) ∧ (False ∨ True)) ∧ (p5 → True)) ∧ ((((p1 → p3) ∧ p2) ∨ p2) ∧ p2)) → (((False ∨ (True ∧ p3)) → p1) ∨ True)) ∨ p4) := by
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
  -- Disjunctions on the left can always be decomposed.
  cases h6
  case inl h8 =>
    -- Disjunctions on the left can always be decomposed.
    cases h7
    case inl h9 =>
      -- False on the left can always be used.
      apply False.elim h9
    case inr h10 =>
      -- Conjunctions on the left can always be decomposed.
      let h11 := h3.left
      let h12 := h3.right
      -- Disjunctions on the left can always be decomposed.
      cases h11
      case inl h13 =>
        -- Conjunctions on the left can always be decomposed.
        let h14 := h13.left
        let h15 := h13.right
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- True on the right can always be proven directly.
        apply True.intro
      case inr h16 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- True on the right can always be proven directly.
        apply True.intro
  case inr h17 =>
    -- Disjunctions on the left can always be decomposed.
    cases h7
    case inl h18 =>
      -- False on the left can always be used.
      apply False.elim h18
    case inr h19 =>
      -- Conjunctions on the left can always be decomposed.
      let h20 := h3.left
      let h21 := h3.right
      -- Disjunctions on the left can always be decomposed.
      cases h20
      case inl h22 =>
        -- Conjunctions on the left can always be decomposed.
        let h23 := h22.left
        let h24 := h22.right
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- True on the right can always be proven directly.
        apply True.intro
      case inr h25 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- True on the right can always be proven directly.
        apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_265717533505769619098983879475 : (True ∧ (p3 ∨ (((p4 → ((False → False) ∧ False)) ∨ ((p4 ∧ p5) → (p3 → p2))) → (p1 → (((True → p2) ∨ ((p3 ∨ p2) ∨ p1)) ∨ p5))))) := by
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
  cases h1
  case inl h3 =>
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h2
  case inr h4 =>
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_190792223821052565471296253690 : ((((p3 ∧ (False ∧ p2)) ∧ (p1 ∨ p1)) ∨ (p5 ∨ True)) ∨ (((((p3 ∧ True) ∧ p5) ∧ p2) → p1) ∨ (((True ∨ p5) ∨ p2) ∧ (p3 ∧ False)))) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_56721105170222287446383307912 : ((((False ∨ p4) ∨ p4) ∧ (p4 ∧ ((((((((p2 ∨ p3) ∧ (p5 → p5)) ∧ True) ∨ (p4 ∨ p4)) ∧ p2) ∧ (p4 → p5)) ∨ False) ∨ p2))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_115692635522598821677489705528 : (((True → (p2 → ((p1 ∨ False) ∨ p3))) ∨ ((((p2 ∨ (p5 → p5)) ∨ ((p2 ∨ p3) ∧ ((p5 ∧ True) ∧ True))) ∨ True) ∧ False)) ∨ (p3 → True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_148375862961990674965968739663 : ((((p5 ∨ (((True ∧ p4) ∧ ((p3 ∧ True) ∨ (False ∧ p3))) ∧ p2)) → p3) ∨ (((p2 ∨ p3) ∨ p2) → p3)) ∨ ((False ∨ (p3 ∧ p1)) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_41968450744341402132006931786 : ((((True ∨ p5) ∧ ((((p1 ∨ ((((p1 ∨ (p5 ∧ (False ∧ True))) ∨ p4) ∨ p2) → p4)) ∨ True) → p5) ∨ (p4 → (p4 ∧ p4)))) ∨ p4) ∨ p2) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro
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
theorem thm_5_vars_617383048317818027609763031129 : ((((((p5 ∧ p4) → (p2 ∨ ((False ∨ False) → False))) → ((((p4 ∧ p3) ∧ (p3 ∧ (p1 ∨ ((p5 ∨ p5) ∧ p2)))) → p4) → p5)) ∨ True) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_299502158062474524757344546571 : (False ∨ ((p5 → ((p3 → (p5 ∧ (True ∧ ((((p2 → False) ∧ p2) → (p3 ∨ ((p4 → (p1 ∧ p2)) → p5))) → (p4 ∨ p3))))) → p4)) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_134005807619229011258666215937 : ((((p2 ∧ (((((((p2 ∧ p4) ∨ p2) ∨ ((p5 ∨ False) → False)) ∧ False) → p1) → (True ∧ p4)) ∧ p5)) ∧ p5) ∨ True) ∨ (p2 ∧ (p5 ∨ True))) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_195454244779727622853424694361 : ((((p4 → p2) ∨ p5) ∨ ((False ∧ False) → p5)) ∧ (((p4 ∨ (p1 → (p3 → False))) ∨ ((((False ∨ p3) ∨ (p2 ∨ p1)) ∧ p4) ∨ True)) ∨ p3)) := by
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
  apply False.elim h2
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_346785426066535734084218389338 : (p3 → (((((p2 → p2) ∧ p4) ∨ (p4 ∧ p2)) ∧ ((p4 ∨ p1) ∧ ((False → (p3 ∧ p4)) ∨ (p5 → p5)))) ∨ (p4 → (False → (p3 ∧ p3))))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h2
  -- Implications on the right can always be decomposed.
  intro h3
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- False on the left can always be used.
  apply False.elim h3
  -- False on the left can always be used.
  apply False.elim h3



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_604824773729430340296739576075 : ((((p1 → ((((False ∧ (((True ∧ ((p4 ∨ True) → p2)) ∨ p1) ∨ (p3 ∨ p4))) ∧ p3) ∨ ((False ∨ p3) ∧ p5)) ∨ (p4 ∨ p5))) ∧ p2) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_241688874989275394998839191085 : ((False → p5) ∧ (p2 → ((p2 ∨ p4) ∧ ((False ∨ ((False → p3) → p1)) ∨ ((((False ∧ p4) ∨ (p2 ∧ (False → p4))) ∧ p1) ∨ (p3 ∨ p2)))))) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h1
  -- False on the left can always be used.
  apply False.elim h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- One of the premise coincides with the conclusion.
  exact h2
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_172771150615548660625674200207 : (((p1 ∨ p5) → (((p1 → ((True ∨ p5) → (p1 ∧ True))) ∨ (p3 → True)) → False)) ∨ (((p3 ∧ p5) ∨ (p3 → (p2 ∧ (p2 ∨ True)))) → True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_135715973608010203964912204842 : (((p3 ∨ ((p4 → (((p3 ∨ p1) ∨ p1) ∧ ((True ∨ p1) ∧ p5))) ∨ p1)) ∧ (p1 ∨ ((p5 ∨ (True ∧ p5)) ∨ p2))) ∨ ((False ∨ p3) → True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_768742054768680324719961785792 : (((p5 ∧ (((p2 ∧ p3) ∨ (p2 ∨ (p4 → (p5 ∧ p3)))) ∧ (True ∨ ((((p1 ∧ False) ∨ (p4 → p4)) ∧ True) ∧ ((p5 → p5) ∧ p4))))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_640589845430258632488952100071 : (((((False ∨ p2) ∧ (p5 → (((p5 ∧ (((True ∨ p5) → (((((False ∧ p2) ∧ p2) → p1) → p5) ∧ p5)) → p5)) ∨ False) → p3))) → p3) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_54200788966731607107863493216 : ((((((p1 ∨ p3) ∨ p1) → (p3 ∧ p5)) ∨ p4) ∧ (((p1 → ((p4 ∨ p2) ∨ (p2 ∨ p5))) ∧ ((True ∨ p1) ∧ p4)) ∨ (True ∧ p1))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_669954304232428636980587775166 : ((((((p3 ∨ p2) ∧ ((((False ∧ p3) ∨ True) ∨ p4) → p2)) ∨ (((p2 ∧ p3) → (p4 ∧ p3)) ∨ (p5 ∧ p2))) ∨ (p1 → (False → True))) ∨ p5) ∧ True) := by
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
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_136122087030193253314044693841 : (((p3 ∨ ((p5 ∨ p3) ∧ (p5 ∨ (True → p5)))) ∨ (p2 ∨ (p2 ∨ (p2 ∨ (((p3 → p3) ∨ p1) ∨ (p1 ∧ p2)))))) ∨ ((p5 → False) → True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_327027701747431389734298561117 : (True → (((((p5 → p5) → p2) → ((p4 ∧ p2) → ((p4 ∨ p1) → False))) ∨ (p3 ∧ (p1 → ((False ∧ (p5 ∨ p1)) ∨ (p2 ∨ False))))) ∨ True)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_244405043128800342588496842355 : ((False ∧ p1) ∨ ((False ∨ p4) ∨ (True → (((False ∨ (p1 ∨ p5)) → (p5 ∨ True)) ∨ (((False ∨ ((p3 ∧ p3) ∨ True)) ∧ True) → (p5 ∧ True)))))) := by
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
  -- Disjunctions on the left can always be decomposed.
  cases h2
  case inl h3 =>
    -- False on the left can always be used.
    apply False.elim h3
  case inr h4 =>
    -- Disjunctions on the left can always be decomposed.
    cases h4
    case inl h5 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- True on the right can always be proven directly.
      apply True.intro
    case inr h6 =>
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- One of the premise coincides with the conclusion.
      exact h6



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_88019520226501826273350853426 : ((((p4 ∧ (p1 → p3)) ∧ p3) ∧ (((p2 ∧ p5) ∨ False) ∧ ((((((p2 ∧ p1) ∧ p5) → p1) → p1) ∨ p4) ∧ (p1 → (p3 ∨ False))))) → p3) := by
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
  let h8 := h3.left
  let h9 := h3.right
  -- Disjunctions on the left can always be decomposed.
  cases h8
  case inl h10 =>
    -- Conjunctions on the left can always be decomposed.
    let h11 := h10.left
    let h12 := h10.right
    -- Conjunctions on the left can always be decomposed.
    let h13 := h9.left
    let h14 := h9.right
    -- Disjunctions on the left can always be decomposed.
    cases h13
    case inl h15 =>
      -- One of the premise coincides with the conclusion.
      exact h5
    case inr h16 =>
      -- One of the premise coincides with the conclusion.
      exact h5
  case inr h17 =>
    -- False on the left can always be used.
    apply False.elim h17



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_174658016835258437399326468338 : ((((p3 ∨ p5) → p5) ∧ (((False ∨ (p5 → True)) ∧ (p3 ∨ p5)) → (p2 ∧ p4))) → (p5 → (p1 → (p2 ∧ ((p2 ∧ False) ∨ (p4 ∨ p4)))))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Implications on the right can always be decomposed.
  intro h3
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Conjunctions on the left can always be decomposed.
  let h4 := h1.left
  let h5 := h1.right
  -- We want to use the implication h5 based on <expert-advice>. So we show its premise.
  have h6 : ((False ∨ (p5 → True)) ∧ (p3 ∨ p5)) := by
    -- Conjunctions on the right can always be decomposed.
    apply And.intro
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h7
    -- True on the right can always be proven directly.
    apply True.intro
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h2
  -- We have shown the premise of h5, we can now drive its conclusion.
  let h8 := h5 h6
  -- We need to get the left conjuct of h8 based on <expert-advice>.
  let h9 := h8.left
  -- One of the premise coincides with the conclusion.
  exact h9
  -- Conjunctions on the left can always be decomposed.
  let h10 := h1.left
  let h11 := h1.right
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- We want to use the implication h11 based on <expert-advice>. So we show its premise.
  have h12 : ((False ∨ (p5 → True)) ∧ (p3 ∨ p5)) := by
    -- Conjunctions on the right can always be decomposed.
    apply And.intro
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h13
    -- True on the right can always be proven directly.
    apply True.intro
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h2
  -- We have shown the premise of h11, we can now drive its conclusion.
  let h14 := h11 h12
  -- We need to get the right conjuct of h14 based on <expert-advice>.
  let h15 := h14.right
  -- One of the premise coincides with the conclusion.
  exact h15



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_300552143221446081030050690846 : (False ∨ (((((p2 ∧ p2) → p2) ∨ ((p3 ∨ True) ∧ (p4 → False))) ∧ (True ∧ ((False ∧ p5) ∨ (p2 ∧ False)))) ∨ (p4 → ((True ∨ p1) ∨ False)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
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
theorem thm_5_vars_245758986706574176779996031187 : ((p3 ∧ p2) ∨ (p4 → ((p5 ∨ ((p2 ∧ (((((p4 → p3) ∨ (p5 ∧ (p2 ∨ p4))) ∨ (p3 ∧ (p1 ∨ p1))) ∨ True) ∧ p1)) ∧ False)) ∨ p4))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_56313796636795328652774736949 : ((((True ∨ (p4 ∧ p1)) ∧ p1) → (((((p2 ∨ ((True → p3) ∧ p5)) ∨ True) ∧ (((p4 ∨ True) ∧ (p2 ∧ p5)) ∨ p2)) ∧ p2) → False)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_148697694154595345995086867001 : (((p4 → ((False ∧ p4) ∨ ((p1 ∧ p3) ∨ p3))) ∨ ((p3 ∨ ((p4 ∨ p1) ∨ (p4 ∨ (p1 ∧ p1)))) ∨ p1)) ∨ ((True ∨ p1) ∧ (p3 → True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_60144631917177850027219725519 : (((p4 ∨ p2) → ((((((p5 ∨ p2) ∨ ((True ∧ (p5 ∨ (False ∨ True))) → p2)) ∧ p5) ∨ (p2 → p1)) ∨ p1) ∧ ((p2 → True) ∧ p2))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_57725369785409876707619832394 : ((((p1 ∨ False) → p1) → (((p3 ∨ p3) ∨ ((p2 ∨ False) ∧ ((p2 ∨ (p5 ∧ p1)) → False))) ∨ (p4 ∨ (((p3 → True) ∨ p5) → True)))) ∨ p2) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h2
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_115649355576041134680692111737 : ((((p5 ∧ (p4 → (True ∧ False))) → p4) ∨ (((((p5 ∧ p5) ∨ (p3 → p4)) ∧ p1) ∧ True) ∨ (((p5 ∧ True) ∨ False) ∨ p3))) ∨ (p1 → p1)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_50874044697260114696631043702 : ((((((((((p4 → (p5 ∧ p4)) ∧ True) ∨ False) ∧ p4) ∨ False) ∧ (p4 ∨ p2)) ∧ p5) → p2) ∧ ((p3 ∧ False) ∧ ((p1 ∧ p4) → p1))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_184422806778816606191956374369 : ((((p4 → (False ∨ (p2 → p4))) ∧ (True ∨ p1)) ∧ (p3 ∧ p2)) ∨ (((p5 → ((True ∧ p2) → p4)) ∧ p1) ∨ ((p3 ∨ False) → (p4 → p3)))) := by
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
    -- One of the premise coincides with the conclusion.
    exact h3
  case inr h4 =>
    -- False on the left can always be used.
    apply False.elim h4



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_186579784944845138705785553984 : ((((((p4 ∧ p3) ∨ (p3 ∧ p1)) ∧ p1) ∧ p5) → (p1 ∧ True)) → (((p1 ∨ ((True ∨ False) ∨ (p5 ∧ (p4 ∧ p1)))) → (p4 ∧ p4)) ∨ True)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_42003910725182964865488840176 : ((((p2 → p2) ∧ (p2 → (((p5 ∨ (p3 ∧ (p4 ∨ (((((p5 ∨ True) → p3) → (p4 ∧ p1)) ∨ p1) ∧ p4)))) ∨ p3) ∨ p4))) ∨ p4) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_52879528541366244299363719357 : (((True ∨ (True ∧ (p4 ∧ ((False ∧ (p3 ∨ ((False ∨ p5) → False))) ∨ True)))) → (((True ∨ p4) ∧ (p2 → p3)) ∨ ((p1 → False) → p3))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_68192672266237793382243251771 : ((p3 → (((p1 ∨ ((p5 → p2) ∧ (p2 ∨ False))) ∧ (((p5 ∨ ((p4 ∧ p1) ∧ (p5 → ((p5 ∧ p1) → p4)))) ∧ p1) → p5)) ∨ True)) ∨ p3) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_229508132598773910255916812962 : ((p2 → (False ∨ p5)) ∨ ((p1 ∨ (False ∨ (p3 ∨ ((p4 → p3) ∨ True)))) ∨ ((p1 ∨ (((p3 ∧ True) → p3) ∨ ((False ∨ p5) ∨ p1))) ∧ p5))) := by
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
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_150227662427430074225954008898 : ((p2 → (p5 ∨ ((((p3 → p3) ∧ False) → (False → p4)) → (p5 ∨ (((p1 ∧ p4) ∧ (p3 → True)) ∨ False))))) ∨ (p2 ∨ ((p2 ∧ False) → p5))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- False on the left can always be used.
  apply False.elim h3



